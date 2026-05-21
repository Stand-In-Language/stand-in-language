# Source Locations Branch Progress

## Goal

Improve Telomare source provenance so parser, resolver, CLI-facing errors, tests, and the Haskell LSP can report useful source locations instead of opaque or dummy locations.

## Branch

- Branch: `source-locations`
- Base branch: `master`
- First completed commit: `79044b9 Introduce source provenance locations`

## Progress Log

### 2026-05-21: Source Provenance Groundwork

Added the initial location/provenance model in `src/Telomare.hs`.

- Added `SourcePosition` and `SourceSpan`.
- Extended `LocTag` with source, generated, builtin, runtime, decompiled, and unknown provenance constructors.
- Added `locStartLineColumn` as the compatibility bridge for consumers that still only need point-style line and column data.
- Replaced several obvious `DummyLoc` uses with more meaningful provenance in builtin insertion, generated wrappers, and typechecker-created fragments.
- Updated source display code in `src/Telomare/Eval.hs` to use `locStartLineColumn`.
- Kept old `Loc` and `DummyLoc` temporarily to avoid an unsafe large migration.

Plan note: This route changed after review. `Loc` and `DummyLoc` were redundant once the richer provenance constructors existed, so the next slice removes them instead of keeping them temporarily. Parser locations are moving to `SourceLoc SourceSpan`, and generated/runtime/test/decompiled values use semantic provenance constructors.

### 2026-05-21: Remove Legacy Location Sentinels

Started the large migration away from the legacy location constructors.

- Removed the legacy `Loc Int Int` source-point constructor from `LocTag`.
- Removed the catch-all `DummyLoc` constructor from `LocTag`.
- Replaced runtime conversions with `RuntimeLoc`.
- Replaced decompiler-created terms with `DecompiledLoc`.
- Replaced intentionally location-less test/generated trees with `UnknownLoc` or a more specific `GeneratedLoc` where useful.
- Replaced equality checks against a sentinel location with semantic checks based on `locStartLineColumn`.

Route change: old sentinel constructors are no longer allowed. New code must choose a provenance constructor that describes where the term came from: source, generated, builtin, runtime, decompiled, or unknown.

### 2026-05-21: Parser Source Span Capture Route

Moved parser source capture toward the idiomatic Megaparsec shape.

- Split raw token parsers from whitespace-consuming lexeme wrappers where source spans matter.
- Added a `withSourceSpan` parser helper that captures `start` and `end` around the raw syntactic token, then consumes trailing whitespace after the end position has been recorded.
- Converted parser-created locations from the removed `Loc Int Int` to `SourceLoc SourceSpan`.
- Added a parser test proving a variable span excludes trailing whitespace in input like `foo   0`.

Plan note: This fixes token-level location capture first, which is the important path for missing-definition diagnostics. Composite expression spans are still conservative where the parser currently records the expression start before delegating to existing whitespace-consuming combinators. The follow-up route is to continue applying the same Megaparsec pattern to delimiters and composite forms so LSP can safely highlight full expression ranges.

### 2026-05-21: Legacy Location Removal Verification

Verified the `Loc`/`DummyLoc` removal slice.

- `nix develop -c stylish-haskell -i app/Repl.hs src/Telomare.hs src/Telomare/Parser.hs src/Telomare/Eval.hs src/Telomare/Decompiler.hs src/Telomare/Possible.hs src/Telomare/PossibleData.hs test/ParserTests.hs test/ResolverTests.hs test/UDTTests.hs test/NatUDTTests.hs test/CaseTests.hs test/Common.hs` completed.
- `nix develop -c cabal build all` passed.
- `nix develop -c cabal test telomare-parser-test telomare-resolver-test` passed after rerunning sequentially; the first attempt overlapped another Cabal build and hit a `dist-newstyle` temporary-file race.
- `nix develop -c cabal test all` passed.
- `nix build .#checks.x86_64-linux.default` passed.
- `git diff --check` passed.
- `nix run .#format-lint` still reports only the known 9 pre-existing HLint hints.

Plan note: The migration is ready for final diff inspection and commit. The remaining parser-location work is now specifically about broadening full-span capture to composite forms, not about removing legacy constructors.

### 2026-05-21: Resolver Diagnostics Slice

Started exposing resolver errors with source locations.

- Added `MissingDefinitionAt LocTag String` to `ResolverError`.
- Added `renderLocTag`, `renderLocTagVerbose`, and `renderResolverError`.
- Added a custom `Show ResolverError` that preserves useful rendered text and still works in nested contexts.
- Changed missing variable resolution to return `MissingDefinitionAt anno name` instead of only `MissingDefinitions [name]`.
- Added a resolver test proving `main = foo 0` reports `missing definition "foo" at line 1, column 8`.

Plan note: I focused on missing-definition diagnostics first because they can use the parser annotations already attached to variable nodes. Typechecker diagnostics remain deferred because selecting the right primary location for type mismatch errors needs a separate design pass.

### 2026-05-21: Parser Diagnostics API

Added a structured parser entry point for diagnostic consumers.

- Added `parseModuleDetailed :: String -> Either (ParseErrorBundle String Void) [Either AnnotatedUPT (String, AnnotatedUPT)]`.
- Kept `parseModule` compatible by rendering `ParseErrorBundle` with `errorBundlePretty`.
- Added a parser test proving parse error offsets are available for diagnostics.

Plan note: Existing parser callers should keep using `parseModule`. Diagnostic consumers, especially LSP, should use `parseModuleDetailed` so they can map Megaparsec offsets to editor ranges.

### 2026-05-21: LSP Diagnostics Integration

Integrated parser and resolver diagnostics into `app/LSP.hs`.

- Extended `DocState` with `docDiagnostics`.
- Changed open/change handlers to receive `GlobalState`, not only `DocStore`, so diagnostics can resolve against known module bindings.
- On document open/change, the LSP now parses with `parseModuleDetailed`, stores parse state, computes diagnostics, and publishes them to the client.
- Parse diagnostics are mapped from Megaparsec error offsets to one-character LSP ranges.
- Resolver diagnostics run through `main2Term3 (("Current", parsed) : modules) "Current"`.
- Suppressed `NoMainFunction` diagnostics during normal editing so library/import files are not noisy.
- Missing-definition resolver errors are reported at the source location from `LocTag`; other resolver errors fall back to the beginning of the file.
- On document close, diagnostics are cleared.
- Added `megaparsec` to the `telomare-lsp` executable dependencies and removed no-longer-used `mtl` and `filepath` executable dependencies.

Plan note: LSP diagnostics are intentionally narrow for now: parser errors and resolver missing definitions. The route is to land this useful diagnostic path first, then improve source spans and add richer LSP features once the underlying locations are reliable.

### 2026-05-21: Verification and Route Change

Ran verification for the diagnostics slice.

- `nix develop -c cabal test all` passed.
- `git diff --check` passed.
- `nix run .#format-lint` still reports known pre-existing HLint hints in `Possible.hs`, `Resolver.hs`, and `TypeChecker.hs`.
- `nix run .#format-lint` also found one new local hint in `app/LSP.hs`; that was fixed.
- `nix develop -c cabal build telomare-lsp` exposed a local `guard` name conflict after an import cleanup.

Route change: Instead of importing `Control.Monad.guard`, keep the existing local `guard :: Bool -> Maybe ()` helper in `app/LSP.hs` and avoid the import. After that, rerun LSP build, full tests if needed, default flake check, whitespace check, and lint status.

### 2026-05-21: Verification After LSP Cleanup

Finished the local LSP cleanup and reran checks.

- `nix develop -c stylish-haskell -i app/LSP.hs src/Telomare.hs src/Telomare/Parser.hs src/Telomare/Resolver.hs test/ParserTests.hs test/ResolverTests.hs` completed.
- `nix develop -c cabal build telomare-lsp` passed.
- `nix build .#checks.x86_64-linux.default` passed.
- `git diff --check` passed.
- `nix run .#format-lint` now reports only 9 known pre-existing HLint hints outside the new LSP diagnostic change.

Plan note: The introduced LSP lint issue and signature warnings are resolved. The route is now final diff inspection, then commit the diagnostics/LSP slice if the diff contains only intended changes.

## Current Plan

1. Inspect the final diff.
2. Commit the legacy-location removal slice with a detailed multi-line commit message if the diff contains only intended changes.
3. Continue composite parser span work in a follow-up slice.

## Deferred Work

- Continue applying raw-parser plus lexeme-wrapper source capture to composite parser forms so all `SourceLoc SourceSpan` ranges exclude trailing whitespace.
- Add binder spans and a source-facing LSP index for hover, definition, and completion.
- Add typechecker diagnostics only after deciding how to choose primary and related source locations for type errors.

## Verification Notes

- `nix run .#format-lint` currently reports known HLint hints unrelated to this branch in existing files.
- Do not run `stylish-haskell` on `telomare.cabal`; it is not a Haskell source file and previously produced a parse error.
