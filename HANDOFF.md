# HANDOFF

## Branch: `refactor/compiler-stages`

A behavior-preserving reorganization of `src/` so that modules delimit the
standard compiler stages (see the "Compiler stages" section of README.md
for the stage → module table). Every exported function kept its name; only
module homes changed. Dead code (benchmarks, C FFI, HVM/LLVM/Chez
remnants, `Telomare.Decompiler`, orphan `.tel` files) was deleted first in
its own commit.

### Commit sequence

1. dead-code sweep (−3.7k lines, no moves)
2. `PrettyPrint` → `Telomare.PrettyPrint` + `Telomare.PrettyPrint.Indent`
3. `Telomare.hs` god-module → `Telomare.IR.{Loc,Base,Types,Surface,Core,Builder}` + `Telomare.Error` (facade for one commit, then deleted)
4. `Telomare.Parser` → `Telomare.Parse` + `Telomare.Parse.Sugar`
5. `Telomare.Resolver` → `Telomare.Desugar` + `Telomare.Resolve`
6. `Telomare.TypeChecker` → `Telomare.TypeCheck`
7. `Telomare.Possible`/`PossibleData` → `Telomare.Machine` + `Telomare.Size` + `Telomare.Size.IR` + `Telomare.Eval.Reference` (absorbs `Telomare.RunTime`); `SizingReport` moved from the driver to `Telomare.Size`
8. `Telomare.Eval` → `Telomare.Driver`; `Telomare.Meter` → `Telomare.Eval.Meter`
9. metadata: hie.yaml regenerated, README stage table, CHANGELOG

### Invariants verified

- All five test suites pass at every commit; sizing regression constants
  unchanged (`simpleplus` counts `11, 7, 10, 10`, budget 65536, tictactoe
  golden game, meter ≈46.5k steps).
- `--certificate`, `--meter`, `--fast`, `--compile`/`.telc` CLI paths all
  smoke-tested; REPL `--expr 'succ 7'` prints `8`.
- stylish-haskell no-diff, hlint "No hints", haddock builds.

### Deliberately NOT changed

- The dual resolve pipeline (`process` for the typechecker vs
  `processWlet` for sizing/execution) is preserved and documented in
  `Telomare.Resolve`'s module header. Unifying it is a semantic change
  and a separate project.
- `app/Main.hs`'s hand-rolled `.tel` import scanner and the LSP's own
  module resolver still duplicate `Telomare.Resolve.resolveImports`.
  Unifying the three import resolvers is a good follow-up.
