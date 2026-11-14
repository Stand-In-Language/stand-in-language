# `nix develop`, and so direnv's `use flake` and `nix-shell`: the project's
# dependencies, GHC and cabal-install, with the editor and linting tools —
# haskell-language-server, hlint, stylish-haskell, ghcid. It is the one shell,
# so that an editor that takes the project's environment finds the language
# server in it. Hoogle is not built (haskell-flake used to build a database
# over every dependency); `withHoogle = true` brings it back.
{ hsPkgs, tools, telomare }:
{
  default =
    (hsPkgs.shellFor {
      packages = _: [ telomare ];
      withHoogle = false;
      # shellFor gathers the dependencies through a package of its own, and
      # corepkgs' builder, unlike nixpkgs', defaults that to `doCheck = false`,
      # which leaves the test suites' dependencies out of the shell's GHC.
      genericBuilderArgsModifier = args: args // { doCheck = true; };
      nativeBuildInputs = [
        tools.cabal-install
        tools.haskell-language-server
        tools.hlint
        tools.stylish-haskell
        tools.ghcid
      ];
    }).overrideAttrs
      (old: {
        # corepkgs builds with structured attributes, which leave `name` an
        # unexported shell variable: direnv drops it, and prompts that show
        # the environment's name (any-nix-shell's reads `$name`) have none.
        shellHook = (old.shellHook or "") + ''
          export name
        '';
      });
}
