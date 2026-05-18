# Brands ↔ User-Defined Types — State and Plan

> **Status (2026-05-18, after running the plan):** Phases A–H are complete.
> The `brands.tel` UDT example (`Nat`, `toNat`, `nPlus`, `nMinus`) runs
> end-to-end (`Success`). All test suites pass: 50 + 90 + 26 + 25.
> See **Execution log** at the end for what was done and what the plan
> looked different from once implementation started.

## Context

The `brands` branch introduces a destructuring syntax
`[name1, name2, …] = expr` that binds many top-level names from a single
expression. The motivation (and the pattern in `brands.tel` and
`Prelude.tel`'s `Rational`) is User-Defined Types (UDTs): a UDT is
built as
`let wrapper = \h -> (constructor, validator, …) in wrapper (# wrapper)`,
and what users want next is a clean way to bind each component of that
tuple to a real name. Brands and UDTs are the same feature seen from
two ends: brands are the front, UDTs are the body.

## Plan

### Phase A — Make `PatternAnnotated` enforce its type  ✅ DONE

**Files**: `src/Telomare/Parser.hs`, `src/Telomare/Resolver.hs`

The plan called for wrapping the annotation in `CheckUPF` and threading
it through `makeLambda`. **Final design diverges**: see the Execution
log below — `CheckUPF` was abandoned because it triggered a static
refinement analyser that can't symbolically evaluate hash-dependent
validators. The shipped solution uses the validator as the case
scrutinee directly.

### Phase B — Auto-generate the hash-tag wrapper  ✅ DONE

**File**: `src/Telomare/Parser.hs` (`expandBrand`)

When the brand body is a lambda `\h -> …`, `expandBrand` wraps it in
`wrapper (# wrapper)` automatically and binds the per-slot accessors
to an intermediate `__brand_<T>` name to avoid duplicating the wrapper
expression across each accessor.

### Phase C — First brand slot is the auto-generated validator  ✅ DONE

**File**: `src/Telomare/Parser.hs` (`expandBrand`, `autoValidator`)

The first slot of `[T, mk, op1, …] = \h -> [op0, op1, …]` is now the
auto-generated validator, exposed both as the top-level `T` and as a
*local* `let T = validator in …` inside the wrapper so the operations
can refer to `T` (via `: T` annotations) without forming a top-level
definition cycle.

### Phase D — Replace the sentinel-string hack  ✅ DONE

**File**: `src/Telomare/Parser.hs`

`parseOneAssignmentOrBrand` now returns
`Either AnnotatedUPT (String, AnnotatedUPT)`
(`Left` = brand, `Right` = assignment). `parseAssignmentsAndBrands`,
`parseImportOrAssignment`, and (Phase F) `parseLet` flatMap the
`Either` into the binding list. The `"8@$temp_label$@8"` sentinel is
gone.

### Phase E — Lift the 10-accessor limit  ✅ DONE

**File**: `src/Telomare/Parser.hs` (`expandBrand`)

`expandBrand` now generates `LeftUP (RightUP … e)` chains directly
instead of using `first..tenth` from Prelude. No cap on the number of
slots; no Prelude dependency for the destructure.

### Phase F — Allow brands inside `let`  ✅ DONE

**File**: `src/Telomare/Parser.hs` (`parseLet`)

`parseLet` now uses `parseOneAssignmentOrBrand` and the same
`Either`-flatMap expansion as `parseAssignmentsAndBrands`. Brands
work inside any `let … in …`.

### Phase G — Tests  ✅ DONE (partially — manual, not Spec)

**Files**: `brands.tel`, `examples.tel`

- `brands.tel` now has a working `main` that exercises
  `nPlus (toNat 3) (toNat 5)` ⇒ `"Success"`.
- `brands2.tel` deleted (was a duplicate).
- `examples.tel` cleaned up; brand example reference left as a
  comment pointing at `brands.tel`.
- **Not yet added**: dedicated cases in `test/Spec.hs` /
  `test/ResolverTests.hs` for brands. Validated manually via
  `cabal run telomare -- brands.tel` and a negative test
  (`nPlus (0, 3) (toNat 5)` ⇒ `Aborted, user abort: not Nat`).

### Phase H — Cleanup  ✅ DONE

**File**: `src/Telomare/Parser.hs`, `examples.tel`

- Removed commented `expandBrand` drafts.
- Removed `aux`/`aux1` test strings.
- Removed commented `parseDefinitions` block.
- Removed unused `Lexeme (String)` import.
- `examples.tel` brand comment trimmed to a one-line pointer.

## Critical files (final)

- `src/Telomare/Parser.hs` — `parseBrand`, `parsePatternAnnotated`,
  `parsePatternVar` (annotation now parens-only), `buildMultiLambda`
  (replaces per-arg `makeLambda` chains), `expandBrand`,
  `autoValidator`, `prependLocalValidator`, `parseLet` (now
  brand-aware), `parseImportOrAssignment` (flat-map `Either`).
- `src/Telomare/Resolver.hs` — `findInts`, `findStrings`,
  `findPatternVars`, `pairRoute2Dirs` each gained a
  `PatternAnnotatedF x _ -> x` case so they recurse through annotations.
- `brands.tel` — working UDT example using the new sugar.

## Execution log — how this differed from the written plan

1. **Phase A's `CheckUPF`-based annotation enforcement was abandoned.**
   The plan threaded the annotation through `makeLambda` as
   `CheckUPF typeExpr varName`. At runtime that wrapped the value in
   a `CheckingWrapper` fragment which the static refinement analyser
   (`findInputLimitStepM` in `src/Telomare/Possible.hs:880`) tried
   to symbolically evaluate. It can't evaluate hash-tag validators —
   `h` is structural-hash-derived, not constant in the analyser's
   view — and crashed with `findInputLimitStepM eval unexpected`.

   Final form: the validator is invoked as a *case scrutinee*
   (`case (typeExpr varName) of innerPat -> body`). The validator
   returns its argument on success or aborts on failure; using its
   result as the scrutinee forces evaluation and propagates the
   abort, with no `CheckUPF`/refinement-wrapper involved.

2. **Multi-argument annotated lambdas needed a structural rewrite.**
   The per-argument `makeLambda` foldr produced
   `\v1 -> case v1 of innerPat -> (\v2 -> case v2 of … body)`, where
   the outer case's body is a function. The case-rewrite
   (`removeCaseUPs` → `case2annidatedIfs`) always emits a Pair-typed
   abort as the chain's fallback, which can't unify with a
   function-typed branch.

   Final form: `parseLambda` now calls a new `buildMultiLambda` that
   emits *all the lambdas first*, then *nests all the destructuring
   inside the innermost body* —
   `\v1 -> \v2 -> case v1 of p1 -> case v2 of p2 -> body`. No case
   body is ever a function, so the type checker is happy.

3. **`parsePatternVar`'s bare-identifier annotation was removed.**
   Originally it accepted `v : T` (no parens) by stealing the `:`,
   which prevented `parsePatternAnnotated` from succeeding for
   `(v : T)` — the parser conflict caused a parse error. Annotations
   are now parens-only.

4. **Resolver's pattern walkers needed `PatternAnnotatedF` cases.**
   `findInts`, `findStrings`, `findPatternVars`, and `pairRoute2Dirs`
   used `cata` over `Pattern` with an `_ → []` / `_ → Map.empty`
   fallback. That dropped the inner pattern's bindings whenever an
   annotation wrapped it. Each function now passes the inner result
   through.

5. **Brand expansion shape was refined.** The plan suggested writing
   the validator into the body's tuple directly. The shipped version
   binds the validator as a *local* `let T = validator in …` inside
   the wrapper and prepends a reference `VarUPF T` to the list. This
   keeps top-level `T = left __brand_T` from forming a definition
   cycle with the operations that reference `T` via `: T`.

6. **`brands2.tel` was deleted** rather than kept as the
   "pre-annotation" form — both files were already in sync, and
   `brands.tel` covers the canonical idiom.

## Verification

- `nix develop --command cabal test` — `0 + 50 + 90 + 26 + 25` tests
  passing across the five suites.
- `nix develop --command cabal run telomare -- brands.tel` prints
  `Success` (positive path).
- Negative regression: replacing `toNat 3` with the raw pair
  `(0, 3)` in `brands.tel`'s `main` aborts with
  `Aborted, user abort: not Nat` — confirming the validator fires.
- Brands inside `let`: a `let [T, mk, …] = \h -> [...] in …` form
  parses and evaluates (smoke-tested manually).

## What's still open / nice-to-have

- **Dedicated Spec.hs / ResolverTests.hs brand cases.** Phase G's
  test additions are still manual-only. A short `Spec.hs` block that
  loads `brands.tel`, asserts `nPlus`'s result, and asserts the
  abort message for bad inputs would lock this in against regressions.
- **Better error location for annotation parse failures.**
  `parsePatternAnnotated` could report a more specific message when
  the inner pattern fails to validate.
- **Type-checker awareness of branded values.** Right now the
  validator runs purely at runtime. A future pass could lift the
  brand hash into the type system so `: Nat` is checked statically
  too.
- **`parseDefinitions` is gone but `parseTopLevelWithExtraModuleBindings`
  still uses `fromJust` to find `main`.** Not a brand-specific issue
  but worth a clean error message someday.
