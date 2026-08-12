# Revision history for telomare

## Unreleased

* Reorganized the library into compiler-stage modules: `Telomare.Parse`,
  `Telomare.Expand`, `Telomare.Desugar`, `Telomare.Resolve`,
  `Telomare.TypeCheck`, `Telomare.Size` (+ `.IR`) with the shared
  `Telomare.Machine` step algebra, `Telomare.Eval.Reference` /
  `Telomare.Eval.Meter`, and `Telomare.Driver`. The IR vocabulary moved
  to `Telomare.IR.*` and the error types to `Telomare.Error`.
* Parser APIs now expose an explicit parse-then-expand pipeline. Each surface
  phase has its own term type: the parser produces `ParsedSurfaceTerm` (base
  functor `ParsedTermF` = `UnprocessedParsedTermF` plus the `SugarTermF`
  fragment), and `Telomare.Expand` removes the sugar fragment, returning
  `ExpandedSurfaceTerm` — so expanded trees structurally cannot contain raw
  sugar forms. `Telomare.Desugar` then returns `DesugaredSurfaceTerm`, whose
  case capability is uninhabited, and only that type enters name resolution.
  Module syntax uses `ModuleItem`/`ImportDecl`; expansion retains imports as
  typed `ExpandedModuleItem` values instead of encoding them as arbitrary
  terms. Complete expression runners reject trailing input. The old
  parse-time expansion APIs and `Telomare.Parse.Sugar` module were removed.
* Fixed parser and elaboration correctness issues around oversized naturals,
  keyword boundaries, empty list definitions, generated-pattern capture, UDT
  arity truncation, import failures/cycles, and shadowed builtin rewrites.
* Removed dead code: the unbuildable benchmarks, the C serializer FFI
  (`cbits/`, `ctest/`), the commented-out HVM/LLVM/Chez backends,
  `Telomare.Decompiler`, and orphaned fixture files.
* Removed the `telomare-evaluare` executable and its flake app; its
  interactive evaluation functionality lives in the LSP app now.

## 0.1.0.0 -- YYYY-mm-dd

* First version. Released on an unsuspecting world.
