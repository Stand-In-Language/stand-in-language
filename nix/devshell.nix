# `nix develop`: the project's dependencies, GHC and cabal-install — the
# minimum that builds telomare. `nix develop .#full` adds the editor and
# linting tools: haskell-language-server, hlint, stylish-haskell, ghcid.
# Hoogle is not built for either shell (haskell-flake used to build a
# database over every dependency); `withHoogle = true` brings it back.
{ hsPkgs, tools, telomare }:
let
  shell =
    extra:
    (hsPkgs.shellFor {
      packages = _: [ telomare ];
      withHoogle = false;
      nativeBuildInputs = [ tools.cabal-install ] ++ extra;
    }).overrideAttrs
      (old: {
        # corepkgs builds with structured attributes, which leave `name` an
        # unexported shell variable: direnv drops it, and prompts that show
        # the environment's name (any-nix-shell's reads `$name`) have none.
        shellHook = (old.shellHook or "") + ''
          export name
        '';
      });
in
{
  default = shell [ ];
  full = shell [
    tools.haskell-language-server
    tools.hlint
    tools.stylish-haskell
    tools.ghcid
  ];
}
