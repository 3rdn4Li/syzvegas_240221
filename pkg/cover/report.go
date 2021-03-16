// Copyright 2018 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package cover

import (
	"fmt"
	"sort"

	"github.com/google/syzkaller/pkg/cover/backend"
	"github.com/google/syzkaller/pkg/mgrconfig"
	"github.com/google/syzkaller/sys/targets"
)

type ReportGenerator struct {
	target    *targets.Target
	srcDir    string
	objDir    string
	buildDir  string
	subsystem []mgrconfig.Subsystem
	*backend.Impl
}

type Prog struct {
	Data string
	PCs  []uint64
}

var RestorePC = backend.RestorePC

func MakeReportGenerator(target *targets.Target, vm, objDir, srcDir, buildDir string, subsystem []mgrconfig.Subsystem,
	moduleObj []string, modules map[string]backend.KernelModule) (*ReportGenerator, error) {
	impl, err := backend.Make(target, vm, objDir, srcDir, buildDir, moduleObj, modules)
	if err != nil {
		return nil, err
	}
	subsystem = append(subsystem, mgrconfig.Subsystem{
		Name:  "all",
		Paths: []string{""},
	})
	rg := &ReportGenerator{
		target:    target,
		srcDir:    srcDir,
		objDir:    objDir,
		buildDir:  buildDir,
		subsystem: subsystem,
		Impl:      impl,
	}
	return rg, nil
}

type file struct {
	filename   string
	lines      map[int]line
	functions  []*function
	covered    []backend.Range
	uncovered  []backend.Range
	totalPCs   int
	coveredPCs int
}

type function struct {
	name    string
	pcs     int
	covered int
}

type line struct {
	progCount map[int]bool // program indices that cover this line
	progIndex int          // example program index that covers this line
}

func (rg *ReportGenerator) prepareFileMap(progs []Prog) (map[string]*file, error) {
	if err := rg.lazySymbolize(progs); err != nil {
		return nil, err
	}
	files := make(map[string]*file)
	for _, unit := range rg.Units {
		files[unit.Name] = &file{
			filename: unit.Path,
			lines:    make(map[int]line),
			totalPCs: len(unit.PCs),
		}
	}
	progPCs := make(map[uint64]map[int]bool)
	for i, prog := range progs {
		for _, pc := range prog.PCs {
			if progPCs[pc] == nil {
				progPCs[pc] = make(map[int]bool)
			}
			progPCs[pc][i] = true
		}
	}
	matchedPC := false
	for _, frame := range rg.Frames {
		f := getFile(files, frame.Name, frame.Path)
		ln := f.lines[frame.StartLine]
		var pc uint64
		if frame.Module == "" {
			pc = frame.PC
		} else {
			pc = frame.PC + rg.Modules[frame.Module].Addr
		}
		coveredBy := progPCs[pc]
		if len(coveredBy) == 0 {
			f.uncovered = append(f.uncovered, frame.Range)
			continue
		}
		// Covered frame.
		f.covered = append(f.covered, frame.Range)
		matchedPC = true
		if ln.progCount == nil {
			ln.progCount = make(map[int]bool)
			ln.progIndex = -1
		}
		for progIndex := range coveredBy {
			ln.progCount[progIndex] = true
			if ln.progIndex == -1 || len(progs[progIndex].Data) < len(progs[ln.progIndex].Data) {
				ln.progIndex = progIndex
			}
		}
		f.lines[frame.StartLine] = ln
	}
	if !matchedPC {
		return nil, fmt.Errorf("coverage doesn't match any coverage callbacks")
	}
	for _, unit := range rg.Units {
		f := files[unit.Name]
		for _, pc := range unit.PCs {
			if progPCs[pc] != nil {
				f.coveredPCs++
			}
		}
	}
	for _, s := range rg.Symbols {
		fun := &function{
			name: s.Name,
			pcs:  len(s.PCs),
		}
		for _, pc := range s.PCs {
			if progPCs[pc] != nil {
				fun.covered++
			}
		}
		f := files[s.Unit.Name]
		f.functions = append(f.functions, fun)
	}
	for _, f := range files {
		sort.Slice(f.functions, func(i, j int) bool {
			return f.functions[i].name < f.functions[j].name
		})
	}
	return files, nil
}

func (rg *ReportGenerator) lazySymbolize(progs []Prog) error {
	if len(rg.Symbols) == 0 {
		return nil
	}
	symbolize := make(map[*backend.Symbol]bool)
	uniquePCs := make(map[uint64]bool)
	var pcs []uint64
	for _, prog := range progs {
		for _, pc := range prog.PCs {
			if uniquePCs[pc] {
				continue
			}
			uniquePCs[pc] = true
			sym := rg.findSymbol(pc)
			if sym == nil {
				continue
			}
			if !sym.Symbolized && !symbolize[sym] {
				symbolize[sym] = true
				pcs = append(pcs, sym.PCs...)
			}
		}
	}
	if len(uniquePCs) == 0 {
		return fmt.Errorf("no coverage collected so far")
	}
	if len(pcs) == 0 {
		return nil
	}
	groupPCs := backend.GroupPCsByModule(pcs, rg.Modules)
	for name, pcs := range groupPCs {
		if len(pcs) == 0 {
			continue
		}
		frames, err := rg.Symbolize(pcs, rg.Modules[name].Path)
		if err != nil {
			return err
		}
		for i := range frames {
			frames[i].Module = name
		}
		rg.Frames = append(rg.Frames, frames...)
	}
	for sym := range symbolize {
		sym.Symbolized = true
	}
	return nil
}

func getFile(files map[string]*file, name, path string) *file {
	f := files[name]
	if f == nil {
		f = &file{
			filename: path,
			lines:    make(map[int]line),
			// Special mark for header files, if a file does not have coverage at all it is not shown.
			totalPCs:   1,
			coveredPCs: 1,
		}
		files[name] = f
	}
	return f
}

func (rg *ReportGenerator) findSymbol(pc uint64) *backend.Symbol {
	idx := sort.Search(len(rg.Symbols), func(i int) bool {
		return pc < rg.Symbols[i].End
	})
	if idx == len(rg.Symbols) {
		return nil
	}
	s := rg.Symbols[idx]
	if pc < s.Start || pc > s.End {
		return nil
	}
	return s
}
