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
* Fixed every GHC `-Wall` warning across the library, executables, and test
  suites (unused imports, name shadowing, incomplete patterns, missing
  signatures, orphan instances, type defaults), and enabled `-Wall`
  permanently for every component in `telomare.cabal`. Orphan instances moved to
  their proper homes: `MonadFail (Either ResolverError)` to `Telomare.Error`,
  `TelomareLike CompiledExpr` to `Telomare.IR.Core`, and the
  `PrettyPrintable` `Char`/`FunctionIndex` instances to
  `Telomare.PrettyPrint`.
* Removed a further ~1,100 lines of dead code across the library, the
  executables and the test suites, including the unused `super*`/`indexed*`
  step family in `Telomare.Machine` and test scaffolding reachable from nothing
  live. Every component now also carries `-Wunused-packages`, and the
  build is warning-free under it.
* Consolidated duplicated logic behind shared abstractions: `Telomare.Util`
  (one `debugTrace`, `padRight` and `plural` where there were six, four and
  two), `Telomare.Lexical` (reserved words, identifier character classes and
  comment delimiters, now read by both the parser and the language server),
  `traverseScoped` in `Telomare.IR.Surface` (one binding-aware traversal of the
  surface functor replacing five hand-written scope walks), and `purely` in
  `Telomare.Machine` (the pure step functions are derived from the monadic ones
  rather than written out a second time).
* Fixed three drifts between the language server's lexer and the parser, all of
  which came from the lexer restating parser facts: `where` was highlighted as
  a keyword though the language does not reserve it, identifiers could only
  start with an ASCII letter, and `{- -}` block comments were never lexed.
* Added `test/ConformanceTests.hs`, a corpus-driven check that the sized
  evaluator, the step meter and the fast runtime agree on the programs they can
  all run.
* Fixed `topologicalSort` in `Telomare.Resolve`, which existed twice with the
  two copies returning opposite orders.
* Fixed the nix build, which had stopped compiling the test suites: it builds
  from `cabal sdist` output, and the Telomare programs the tests read at run
  time were no longer declared in `telomare.cabal`.
* Fixed `nix run .#push-cachix`, which aborted before pushing anything: it named
  the shell apps' closures by evaluating `apps.<system>.<name>.program`, which
  computes a store path without building it, and `nix path-info` rejects a path
  that does not exist. The apps are now build inputs of the script.
* Moved to GHC 9.10.3 and `cabal-version` 3.12, and updated every flake input.
* Moved the Nix build from nixpkgs + flake-parts + haskell-flake to the
  ekala package ecosystem (ekapkgs): `corepkgs` for the base system and the
  GHC 9.10.3 bindist (added upstream for this, corepkgs#178 and #180), plus
  the `haskell-pkgs` snapshot (Stackage LTS 24), consumed with
  `corepkgs.lib.mkFlake`. The Nix code lives in `nix/`; the package
  expression is a checked-in cabal2nix file (`nix/telomare-cabal2nix.nix`,
  regenerate when `build-depends` change); `default.nix` and `shell.nix`
  read the pins from `flake.lock` instead of going through flake-compat,
  and are no longer built or cached by `push-cachix`.
  `apps.telomare-lsp` now carries the version stamp like `apps.lsp`. The
  default dev shell is the minimum that builds the project (GHC and
  cabal-install); `nix develop .#full` adds haskell-language-server, hlint,
  stylish-haskell and ghcid; both export `name`, which corepkgs' structured
  attributes leave unexported, so direnv hands it to prompts that show the
  environment's name (haskell-language-server needs its closure in
  one Cabal-syntax 3.14 scope; `nix/haskell.nix` carries that override until
  ekala-project/haskell-pkgs#4 or its corepkgs equivalent lands), and hoogle
  is no longer built for either. `nix run .#push-cachix` publishes every
  declared development shell with its environment closure, every check and
  every app, and uses the cachix and nix on PATH (the snapshot's cachix does
  not build, its amazonka 2.0 predates GHC 9.8, and corepkgs' Nix is a
  from-source build); it keeps what it builds rooted until the push is over,
  since Determinate Nix collects garbage on its own when the disk runs low;
  `nix flake check` builds and shellchecks it. No check
  depends on the LSP version stamp any more, so CI, which builds a pull
  request's merge commit rather than the pushed one, finds every check in
  the cache instead of rebuilding the LSP wrapper, the helper and
  ShellCheck. `systems` is `x86_64-linux` until corepkgs marks
  aarch64-linux supported.
* CI installs Determinate Nix 3.22.5, the Nix `push-cachix` is run with,
  instead of Nix 2.31.5: `nix develop` builds its environment from the
  running Nix's own get-env.sh, so only the same version finds it in the
  cache. Bump the pin with the maintainer's Nix. magic-nix-cache is gone:
  every upload was failing, and Cachix holds everything CI needs.

## 0.1.0.0 -- YYYY-mm-dd

* First version. Released on an unsuspecting world.
