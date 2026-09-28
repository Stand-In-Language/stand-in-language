# Everything the flake exposes, as plain Nix over a package set: the package,
# the development shell, the apps and the checks. flake.nix calls this with
# the flake's own source and `self`-derived version stamp; default.nix and
# shell.nix call it through nix/legacy.nix.
{
  pkgs,
  src,
  lspVersion ? "unknown",
}:
let
  hs = import ./haskell.nix { inherit pkgs; };
  telomare = import ./telomare.nix {
    inherit pkgs src;
    hsPkgs = hs.hsPkgs;
  };
  devShells = import ./devshell.nix {
    inherit telomare;
    hsPkgs = hs.hsPkgs;
    tools = hs.tools;
  };
  tools = import ./tools.nix {
    inherit
      pkgs
      src
      lspVersion
      telomare
      ;
    tools = hs.tools;
    executables = hs.executables;
    devShellNames = builtins.attrNames devShells;
    checkNames = builtins.attrNames checks;
    appNames = builtins.attrNames apps;
  };
  packages = {
    inherit telomare;
    default = telomare;
  };

  # One app per executable under its own name (`nix run .#telomare-repl`, as
  # CI does), plus the short names and the tooling.
  apps = {
    default = "${telomare}/bin/telomare";
    telomare = "${telomare}/bin/telomare";
    repl = "${telomare}/bin/telomare-repl";
    telomare-repl = "${telomare}/bin/telomare-repl";
    lsp = "${tools.telomareLsp}/bin/telomare-lsp";
    telomare-lsp = "${tools.telomareLsp}/bin/telomare-lsp";
    format = "${tools.telomareFormat}/bin/telomare-format";
    format-lint = "${tools.telomareFormatLint}/bin/telomare-format-lint-check";
    push-cachix = "${tools.pushCachix}/bin/telomare-push-cachix";
  };

  # `nix flake check` builds the package — with all its test suites — and
  # verifies formatting and linting. Nothing here may depend on the version
  # stamp: CI builds a pull request's merge commit, whose timestamp is never
  # the one `push-cachix` ran at, so a stamped check would always rebuild.
  checks = packages // {
    format-lint = tools.formatLintCheck;
    push-cachix = tools.pushCachix;
  };
in
{
  inherit
    packages
    devShells
    apps
    checks
    ;
}
