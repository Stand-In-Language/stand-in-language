{
  description = "Telomare: a simple but robust virtual machine";

  inputs = {
    # The ekala package ecosystem. corepkgs supplies stdenv, the compilers
    # and the Haskell build machinery; haskell-pkgs supplies the Hackage
    # snapshot as a module for corepkgs' `config.overlays.haskell`. They are
    # consumed directly rather than through the ekapkgs aggregate, which
    # pins corepkgs from its own lock file.
    corepkgs.url = "github:ekala-project/corepkgs";
    # corepkgs' formatter pulls nixpkgs in through treefmt-nix; nothing this
    # flake evaluates uses it, so it follows an input that is already here
    # rather than adding a nixpkgs checkout to the lock and to the cache push.
    corepkgs.inputs.treefmt-nix.inputs.nixpkgs.follows = "corepkgs/nix-lib";
    haskell-pkgs = {
      url = "github:ekala-project/haskell-pkgs";
      flake = false;
    };
  };

  # An input's nixConfig is not applied transitively, so the caches this build
  # can draw on are named here: `telomare` holds everything this flake builds,
  # the compiler included; `ekala-corepkgs` holds the base system.
  nixConfig = {
    extra-substituters = [
      "https://telomare.cachix.org"
      "https://ekala-corepkgs.cachix.org"
    ];
    extra-trusted-public-keys = [
      "telomare.cachix.org-1:H0qRjVstxtb9oyEPvDDpmPSLyJ9oViAsTgwR02ra6Dk="
      "ekala-corepkgs.cachix.org-1:DcZV+vegWoEzacbSdXFXU4S7728C0eS9RfGpKeyHd6w="
    ];
  };

  outputs =
    {
      self,
      corepkgs,
      haskell-pkgs,
    }:
    let
      # mkFlake's per-system functions see only the package set, so what
      # depends on the flake itself is captured here: the source, and the
      # checkout timestamp the LSP reports as its version.
      lspVersion =
        if self ? lastModifiedDate then
          let
            timestamp = self.lastModifiedDate;
            year = builtins.substring 0 4 timestamp;
            month = builtins.substring 4 2 timestamp;
            day = builtins.substring 6 2 timestamp;
            hour = builtins.substring 8 2 timestamp;
            minute = builtins.substring 10 2 timestamp;
          in
          "${year}-${month}-${day}T${hour}:${minute}Z"
        else
          "unknown";
      project = pkgs: import ./nix {
        inherit pkgs lspVersion;
        src = self;
      };
    in
    corepkgs.lib.mkFlake {
      # corepkgs' stdenv is checked on x86_64-linux alone for now.
      systems = [ "x86_64-linux" ];
      modules = [ (import "${haskell-pkgs}/pkgs-module.nix") ];
      packages = pkgs: (project pkgs).packages;
      devShells = pkgs: (project pkgs).devShells;
      checks = pkgs: (project pkgs).checks;
      apps = pkgs: (project pkgs).apps;
    };
}
