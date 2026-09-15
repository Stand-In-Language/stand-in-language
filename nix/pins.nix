# The flake's inputs for the flake-less entry points (default.nix, shell.nix),
# read from flake.lock so that both roads lead to the same package set — the
# way ekapkgs' own pins.nix does it.
let
  lock = builtins.fromJSON (builtins.readFile ../flake.lock);
  fetch =
    name:
    let
      node = lock.nodes.${name}.locked;
    in
    if node.type == "path" then
      builtins.fetchTree { inherit (node) type path narHash; }
    else
      builtins.fetchTree {
        inherit (node)
          type
          owner
          repo
          rev
          narHash
          ;
      };
in
{
  corepkgs = fetch "corepkgs";
  haskell-pkgs = fetch "haskell-pkgs";
}
