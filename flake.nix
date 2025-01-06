{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
    hvm.url = "github:hhefesto/HVM";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = inputs@{ self, nixpkgs, flake-compat, hvm, flake-parts, haskell-flake, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" ];
      imports = [ inputs.haskell-flake.flakeModule ];
      perSystem = { self', system, pkgs, ... }: {
        haskellProjects.default = {
          basePackages = pkgs.haskell.packages.ghc92;
          settings = {
            cowsay.custom = _: pkgs.cowsay;
            telomare = {
              extraBuildDepends = [ pkgs.cowsay
                                  ];
            };
          };
          devShell = {
            enable = true;
          };
      };
      packages.default = self'.packages.telomare;
      apps.default = {
        type = "app";
        program = self.packages.${system}.telomare + "/bin/telomare";
      };

      apps.repl = {
        type = "app";
        program = self.packages.${system}.telomare + "/bin/telomare-repl";
      };
    };
  };
}
