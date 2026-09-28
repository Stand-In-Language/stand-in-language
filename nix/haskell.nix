# The GHC package set the build and every tool come from — the one place the
# compiler is named. corepkgs ships GHC as bindists; 9.10.3 is the one this
# project's `cabal-version: 3.12` needs (its Cabal is 3.12.1.0), and the
# haskell-pkgs snapshot (Stackage LTS 24) is built for it.
{ pkgs }:
let
  compose = pkgs.haskell.lib.compose;

  # haskell-language-server's formatters (ormolu 0.8, fourmolu 0.19) need
  # Cabal-syntax 3.14 where GHC 9.10 bundles 3.12; with the bundled one, the
  # closure ends up with two Cabal-syntax instances and Cabal refuses to
  # configure. Build the whole closure in one 3.14 scope, the way nixpkgs'
  # configuration-common.nix does. This is ekala-project/haskell-pkgs#4 carried
  # locally; delete it when that (or a corepkgs equivalent) lands upstream.
  hlsOverlay =
    final: prev:
    let
      hlsScope = lself: lsuper: {
        Cabal-syntax = lself.Cabal-syntax_3_14_2_0;
        Cabal = lself.Cabal_3_14_2_0;
        # Bounded to Cabal-syntax < 3.13; picks 3.14 once the bound is lifted.
        cabal-install-parsers = compose.doJailbreak lsuper.cabal-install-parsers;
        # The default 0.1.0.2 wants Cabal 3.12; 0.1.1.0 is the Cabal-syntax 3.14 release.
        extensions = compose.doJailbreak lself.extensions_0_1_1_0;
        # Depends on Cabal for its Setup.hs only; keep the bundled one so there
        # is a single ghc-paths in the set.
        ghc-paths = lsuper.ghc-paths.override { Cabal = null; };
      };
      inHlsScope = names: pkgs.lib.genAttrs names (name: prev.${name}.overrideScope hlsScope);
      hlsClosure = inHlsScope [
        "haskell-language-server"
        "hls-plugin-api"
        "ghcide"
        "hlint"
        "ormolu"
        "fourmolu"
        "lsp-types"
      ];
    in
    {
      # A versioned Cabal must be built against its own Cabal-syntax, not the
      # compiler's bundled one.
      Cabal_3_14_2_0 = prev.Cabal_3_14_2_0.override { Cabal-syntax = final.Cabal-syntax_3_14_2_0; };
      Cabal_3_16_1_0 = prev.Cabal_3_16_1_0.override { Cabal-syntax = final.Cabal-syntax_3_16_1_0; };
      # deepseq upper bound excludes the 1.5.1.0 that GHC 9.10 ships.
      hw-fingertree = compose.doJailbreak prev.hw-fingertree;
    }
    // hlsClosure
    // {
      # haskell-language-server links its executables dynamically by default;
      # unless the builder is told so, the fixup check finds an RPATH into
      # /build. Same override as nixpkgs' configuration-nix.nix.
      haskell-language-server = compose.overrideCabal (_: {
        enableSharedExecutables = true;
      }) hlsClosure.haskell-language-server;
    };

  hsPkgs = pkgs.haskell.packages.ghc9103Binary.extend hlsOverlay;
in
{
  inherit hsPkgs;
  tools = {
    inherit (hsPkgs)
      hlint
      stylish-haskell
      ghcid
      haskell-language-server
      ;
    # cabal-install 3.16 builds against Cabal 3.16, not the 3.12 that GHC
    # 9.10 bundles, so its scope gets the snapshot's newer Cabal (as nixpkgs
    # does). The snapshot also marks it broken although none of its
    # dependencies is; it builds.
    cabal-install = compose.markUnbroken (
      hsPkgs.cabal-install.overrideScope (
        final: _: {
          Cabal = final.Cabal_3_16_1_0;
          Cabal-syntax = final.Cabal-syntax_3_16_1_0;
        }
      )
    );
  };
  # shellcheck, which every shell app's check phase runs, from the same set:
  # haskell-pkgs exposes it at the top level too, but built with the default
  # (9.8.4) compiler, which would mean a second GHC and its closure for one
  # executable. (cachix is not built here at all: on this snapshot its
  # amazonka 2.0 dependencies do not compile with GHC 9.8 or 9.10 — the
  # Hackage release predates both — so `nix run .#push-cachix` takes cachix,
  # like nix, from the caller's PATH; see nix/tools.nix.)
  executables = {
    shellcheck = compose.justStaticExecutables hsPkgs.ShellCheck;
  };
}
