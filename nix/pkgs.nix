# The package set: corepkgs with the haskell-pkgs snapshot folded in, as the
# flake builds it, for callers without a flake.
{
  system ? builtins.currentSystem,
}:
let
  pins = import ./pins.nix;
in
import pins.corepkgs {
  inherit system;
  modules = [ (import "${pins.haskell-pkgs}/pkgs-module.nix") ];
}
