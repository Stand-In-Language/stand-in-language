# What default.nix and shell.nix build: the project over the pinned package
# set, from a cleaned copy of the working tree. (The flake builds from its
# own source, which is the tracked files.)
{
  system ? builtins.currentSystem,
}:
let
  pkgs = import ./pkgs.nix { inherit system; };
  inherit (pkgs) lib;
  src = lib.cleanSourceWith {
    src = ./..;
    filter =
      path: type:
      lib.cleanSourceFilter path type
      && !(builtins.elem (baseNameOf path) [
        "dist-newstyle"
        ".direnv"
        "result"
      ])
      && !(lib.hasSuffix ".telc" path);
  };
in
import ./. { inherit pkgs src; }
