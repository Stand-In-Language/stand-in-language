# Brands ↔ User-Defined Types — State and Plan

## Context

The `brands` branch introduces a destructuring syntax
`[name1, name2, …] = expr` that binds many top-level names from a single
expression. The motivation (and the pattern in `brands.tel`,
`brands2.tel`, and `Prelude.tel`'s `Rational`) is User-Defined Types
(UDTs): a UDT is built as
`let wrapper = \h -> (constructor, validator, …) in wrapper (# wrapper)`,
and what users want next is a clean way to bind each component of that
tuple to a real name. Brands and UDTs are the same feature seen from
two ends: brands are the front, UDTs are the body.

The 6 brand commits cover parsing, pattern-destructuring lambdas, brand
expansion via Prelude accessors, multi-module compilation tweaks, and a
prettier UPT printer. The REPL goal — `nPlus` over the `Nat` brand —
works (commit `d22e0d7`). The remaining work is to make brands carry
their UDT weight without forcing the user to spell out the hash-tag
wrapper and validator, and to make pattern annotations like `(x : Nat)`
actually fire.

## Review — what's done, what's still missing

### Works today
- `[Name1, Name2, …] = expr` parses (`parseBrand`,
  `src/Telomare/Parser.hs:199`) and expands to one binding per slot
  using `first/second/…/tenth` from Prelude
  (`expandBrand`, `src/Telomare/Parser.hs:430`).
- Pattern-destructuring lambdas (`makeLambda`,
  `src/Telomare/Parser.hs:291`): you can write `\(a, b) -> …`,
  internally rewritten to `\v -> case v of (a,b) -> body; _ -> abort`.
- Multi-module loader only compiles imported `.tel` files
  (`app/Main.hs`).
- Tests pass: 90 examples in the spec suite, plus ResolverTests and
  arithmetic tests.

### Gaps blocking the brand–UDT bridge

1. **`PatternAnnotated` drops its type expression.**
   - `makeLambda` (`src/Telomare/Parser.hs:295`) and `pattern2UPT`
     (`src/Telomare/Resolver.hs:167`) both pattern-match
     `PatternAnnotatedF x _` and throw the annotation away. So
     `\(p : N) -> …` parses, but `N` is never invoked. This is the
     single biggest gap: `\((_, aa) : N) ((_, bb) : N) -> …` in
     `brands.tel` silently skips Nat validation.
   - `parsePatternVar` wraps the annotation in `CheckUPF` while
     `parsePatternAnnotated` does not — the two forms produce
     different shapes of `PatternAnnotated`.

2. **User still writes the hash-tag wrapper by hand.** Every brand
   body in `brands.tel`, `brands2.tel`, and the `Rational` UDT in
   `Prelude.tel` repeats `let wrapper = \h -> [...] in wrapper (# wrapper)`
   and hand-rolls the validator. The brand syntax should absorb this.

3. **First brand slot is not auto-generated.** The user writes
   `N = \(hc, _) x -> assert (dEqual hc h) "not Natural"` manually
   inside the wrapper. With the bridge, the first slot of
   `[T, …] = …` should *become* the auto-generated validator for the
   brand's hash tag.

4. **Brand expansion is capped at 10 elements** because
   `expandBrand` (`src/Telomare/Parser.hs:432`) uses
   `first..tenth`. Anything beyond ten names silently produces wrong
   bindings (`zipWith` truncates).

5. **Brands don't work inside `let`.** `parseLet`
   (`src/Telomare/Parser.hs:340`) uses `parseAssignment` only — a
   brand inside `let … in …` is a parse error.

6. **Sentinel-string hack.** `parseOneAssignmentOrBrand`
   (`src/Telomare/Parser.hs:403`) tags brand entries with the literal
   name `"8@$temp_label$@8"`, then strips them in
   `parseAssignmentsAndBrands`. Works but is fragile — any leak into
   an error message is confusing.

7. **No automated test exercises brands end-to-end.** `brands.tel`'s
   `main` is commented out; `brands2.tel` is a copy; `examples.tel`
   still uses the older `MyInt` UDT. `test/ResolverTests.hs` has
   nothing for brands.

8. **Loose ends.** Commented-out attempts at `expandBrand`
   (`src/Telomare/Parser.hs:425-446`), unused `aux`/`aux1` test
   strings (`src/Telomare/Parser.hs:505-540`), commented-out
   `parseDefinitions` (`src/Telomare/Parser.hs:447-451`), and an
   unused `import Text.Read (Lexeme (String))`
   (`src/Telomare/Parser.hs:33`).

## Plan

### Phase A — Make `PatternAnnotated` enforce its type

**Files**: `src/Telomare/Parser.hs`, `src/Telomare/Resolver.hs`

1. Normalize the annotation shape. In `parsePatternAnnotated`
   (`src/Telomare/Parser.hs:257`) wrap the parsed `typeExpr` the same
   way `parsePatternVar` (`src/Telomare/Parser.hs:245`) does: hand the
   inner pattern's bound variable to the annotation so the stored
   value is `CheckUPF typeExpr (VarUPF varName)`. For destructuring
   patterns (`(a, b) : N`) bind a fresh name first, then check it.
   Both annotation forms then produce identical `PatternAnnotated`
   payloads.
2. In `makeLambda` (`src/Telomare/Parser.hs:291`) keep the existing
   destructure-case rewrite, but thread the annotation through. New
   shape for `PatternAnnotated p typeExpr`:
   ```
   \varName ->
     (\__check -> case varName of p -> body ; _ -> abort)
       typeExpr
   ```
   The throwaway lambda forces `typeExpr` (a `CheckUPF`) to evaluate,
   which fires the runtime assert if the check fails. `__check` is a
   fresh name that doesn't appear in `body`.
3. Leave `pattern2UPT` (`src/Telomare/Resolver.hs:158`) as-is: it
   discards the annotation, which is now correct because the
   assertion fires at lambda entry, not inside the case rewrite.
4. Sanity-check: `assert` (`Prelude.tel:114`) returns 0 on success and
   `(1, s)` on failure, and `CheckUPF` triggers abort when its check
   function returns nonzero. So `let _ = check var in body` is the
   right shape.

### Phase B — Auto-generate the hash-tag wrapper

**File**: `src/Telomare/Parser.hs` (`expandBrand`, lines 430–435)

Right now `expandBrand` just unpacks `exp` slot by slot. Change it so
the brand expression is implicitly wrapped:

```
[T, mk, op1, …] = body
```

becomes

```
__brand_<T> = let wrapper = \__brand_hash -> body_with_T_prepended
              in wrapper (# wrapper)
T   = first  __brand_<T>
mk  = second __brand_<T>
op1 = third  __brand_<T>
…
```

`body_with_T_prepended` is constructed in `expandBrand`: prepend the
auto-generated validator to the user's tuple (Phase C). The user's
body keeps direct access to `__brand_hash` (the freshly-tagged hash)
via a known magic identifier — name it `_h` or similar — so existing
code that wraps/unwraps the hash keeps working.

Rationale: the wrapper / `(# wrapper)` step is mechanical and the same
for every UDT. Hiding it removes the part of the UDT idiom that
beginners trip on (the recursive self-hash).

### Phase C — First brand slot is the auto-generated validator

**File**: `src/Telomare/Parser.hs` (`expandBrand`)

When `expandBrand` builds the wrapped body, prepend an auto-generated
validator for the first name:

```
firstSlot = \x -> let _ = assert (dEqual (left x) _h) "not <T>" in x
```

User now writes only the remaining slots. The brand becomes:

```
[Nat, toNat, nPlus, nMinus] = \_h ->
  [ \x -> (_h, x)                                       -- toNat
  , \((_, aa) : Nat) ((_, bb) : Nat) -> (_h, d2c aa succ bb)
  , \((_, aa) : Nat) ((_, bb) : Nat) ->
       let sLeft = \x -> case x of
                           (l, _) -> l
                           _      -> abort "underflow"
       in (_h, d2c bb sLeft aa)
  ]
```

Combined with Phase A, the `: Nat` annotations actually fire because
`Nat` (the validator) is in scope after expansion. This is the
bridge: the brand-bound first name is both a value (the validator) and
a usable type marker in patterns.

### Phase D — Replace the sentinel-string hack

**File**: `src/Telomare/Parser.hs`

Change `parseOneAssignmentOrBrand` to return
`Either BrandSpec (String, AnnotatedUPT)` (or similar), and have
`parseAssignmentsAndBrands` flatMap the `Either` into the final
binding list. Removes `"8@$temp_label$@8"` and makes the intent
explicit.

### Phase E — Lift the 10-accessor limit

**File**: `src/Telomare/Parser.hs` (`expandBrand`)

Generate accessors as direct AST nodes rather than referencing Prelude
names:
- slot 0 → `LeftUP exp`
- slot 1 → `LeftUP (RightUP exp)`
- slot n → `LeftUP (iterate RightUP exp !! n)`

Removes both the 10-element cap and the implicit dependency on
Prelude. `first..tenth` can stay in Prelude for user code, but brands
no longer require them.

### Phase F — Allow brands inside `let`

**File**: `src/Telomare/Parser.hs` (`parseLet`, lines 340–347)

Swap `parseSameLvl lvl parseAssignment` for a sibling parser that
also accepts `parseBrand`, with the same temp-binding expansion. Easy
once Phase D is in (use the `Either` machinery).

### Phase G — Tests

**Files**: `test/ResolverTests.hs`, `test/Spec.hs`, `brands.tel`,
`brands2.tel`, `examples.tel`

1. Uncomment the `main` in `brands.tel` (`aux (toNat 8)` → `"Success"`)
   and add a Spec test that runs it as a main, asserting the right
   output.
2. Add a ResolverTests case: `nPlus (toNat 2) (toNat 3)` evaluates to
   `(h, 5)` for the right `h`.
3. Add a negative test: applying `nPlus` to a non-Nat aborts with
   `"not Natural"` (proves Phase A wired the annotation in).
4. Delete `brands2.tel` once `brands.tel` has the working main, or
   keep one and remove the other — they're identical except for the
   `: N` annotation.

### Phase H — Cleanup

**File**: `src/Telomare/Parser.hs`

- Remove the commented `expandBrand` drafts (lines 425–446).
- Remove the `aux`/`aux1` test strings (lines 505–540).
- Remove the commented `parseDefinitions` block (lines 447–451).
- Remove `import Text.Read (Lexeme (String))` — unused.
- In `examples.tel`, drop the commented-out brand block; replace it
  with the working brand example.

## Critical files

- `src/Telomare/Parser.hs` — most of the work: `parsePatternAnnotated`,
  `makeLambda`, `expandBrand`, `parseOneAssignmentOrBrand`,
  `parseAssignmentsAndBrands`, `parseLet`.
- `src/Telomare/Resolver.hs` — verify `pattern2UPT` and
  `validateVariables` still cope with the new `PatternAnnotated`
  shape (they should; the annotation becomes inert by Phase A's
  rewrite).
- `src/Telomare.hs` — no data changes expected; `BrandUP` /
  `PatternAnnotated` stay as-is.
- `Prelude.tel` — leave `first..tenth` (lines 200–209) for user code,
  but brands no longer depend on them.
- `brands.tel`, `brands2.tel`, `examples.tel` — uncomment and trim.
- `test/Spec.hs`, `test/ResolverTests.hs` — add coverage.

## Verification

1. `nix develop --command cabal test` — full suite still green.
2. `nix develop --command cabal run telomare -- brands.tel` — prints
   `Success` (Nat 8 round-trips).
3. New positive test: `nPlus (toNat 2) (toNat 3)` evaluates to
   `(<hash>, 5)` (representation may differ — assert via the
   `fromNat`/`toNat` path).
4. New negative test: `nPlus 0 (toNat 3)` aborts with the message
   `"not Natural"`.
5. Manual REPL regression: paste `brands.tel`'s contents and call
   `nPlus (toNat 2) (toNat 3)` — must match what worked before commit
   `d22e0d7`.
6. Brands inside `let`: `let [A, B] = …Pair… in (A, B)` parses and
   evaluates.
