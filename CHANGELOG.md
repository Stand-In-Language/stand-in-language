# Revision history for telomare

## Unreleased

* Reorganized the library into compiler-stage modules: `Telomare.Parse`,
  `Telomare.Sugar`, `Telomare.Desugar`, `Telomare.Resolve`,
  `Telomare.TypeCheck`, `Telomare.Size` (+ `.IR`) with the shared
  `Telomare.Machine` step algebra, `Telomare.Eval.Reference` /
  `Telomare.Eval.Meter`, and `Telomare.Driver`. The IR vocabulary moved
  to `Telomare.IR.*` and the error types to `Telomare.Error`.
* Parser APIs now expose an explicit parse-then-sugar pipeline. Complete
  runners return `Parsed` values, Sugar returns `Sugared` values, module
  syntax uses `ModuleItem`/`ImportDecl`, and complete expression runners reject
  trailing input. The old parse-time expansion APIs and `Telomare.Parse.Sugar`
  module were removed.
* Fixed parser and elaboration correctness issues around oversized naturals,
  keyword boundaries, empty list definitions, generated-pattern capture, UDT
  arity truncation, import failures/cycles, and shadowed builtin rewrites.
* Removed dead code: the unbuildable benchmarks, the C serializer FFI
  (`cbits/`, `ctest/`), the commented-out HVM/LLVM/Chez backends,
  `Telomare.Decompiler`, and orphaned fixture files.

## 0.1.0.0 -- YYYY-mm-dd

* First version. Released on an unsuspecting world.
