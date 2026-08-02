# Revision history for telomare

## Unreleased

* Reorganized the library into compiler-stage modules: `Telomare.Parse`
  (+ `.Sugar`), `Telomare.Desugar`, `Telomare.Resolve`,
  `Telomare.TypeCheck`, `Telomare.Size` (+ `.IR`) with the shared
  `Telomare.Machine` step algebra, `Telomare.Eval.Reference` /
  `Telomare.Eval.Meter`, and `Telomare.Driver`. The IR vocabulary moved
  to `Telomare.IR.*` and the error types to `Telomare.Error`. All
  function names are unchanged; only module homes moved.
* Removed dead code: the unbuildable benchmarks, the C serializer FFI
  (`cbits/`, `ctest/`), the commented-out HVM/LLVM/Chez backends,
  `Telomare.Decompiler`, and orphaned fixture files.

## 0.1.0.0 -- YYYY-mm-dd

* First version. Released on an unsuspecting world.
