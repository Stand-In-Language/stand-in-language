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

Plan note: I intentionally did not rewrite parser annotations to full spans yet. The current parser lexeme structure consumes trailing whitespace in places, so a naive span migration would produce bad diagnostic ranges. The route is to first improve provenance and diagnostics using existing start-point annotations, then do parser span work deliberately.

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
2. Commit the diagnostics/LSP slice with a detailed multi-line commit message, if all required checks are acceptable.
3. Continue with deferred parser-span work in a follow-up slice.

## Deferred Work

- Replace legacy parser point annotations with proper `SourceLoc SourceSpan` values after adjusting parsers so spans do not include trailing whitespace.
- Add binder spans and a source-facing LSP index for hover, definition, and completion.
- Add typechecker diagnostics only after deciding how to choose primary and related source locations for type errors.
- Continue replacing `DummyLoc` incrementally where generated, builtin, runtime, or unknown provenance is known.

## Verification Notes

- `nix run .#format-lint` currently reports known HLint hints unrelated to this branch in existing files.
- Do not run `stylish-haskell` on `telomare.cabal`; it is not a Haskell source file and previously produced a parse error.
