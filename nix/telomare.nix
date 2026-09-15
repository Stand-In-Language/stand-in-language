# The package. The expression cabal2nix generated from telomare.cabal sits in
# telomare-cabal2nix.nix; this is the policy on top of it, chosen to match
# what haskell-flake did for this project: build from `cabal sdist` so that
# anything the test suites open at run time has to be declared in
# `extra-source-files`, run the suites (ekapkgs defaults to skipping them),
# and skip haddock and library profiling, which nothing consumes.
{ pkgs, hsPkgs, src }:
let
  compose = pkgs.haskell.lib.compose;
in
pkgs.lib.pipe (hsPkgs.callPackage ./telomare-cabal2nix.nix { }) [
  (compose.overrideCabal (_: {
    inherit src;
    doCheck = true;
    doHaddock = false;
    enableLibraryProfiling = false;
  }))
  compose.buildFromSdist
]
