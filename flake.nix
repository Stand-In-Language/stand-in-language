{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = inputs@{ self, nixpkgs, flake-compat, flake-parts, haskell-flake, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" ];
      imports = [ inputs.haskell-flake.flakeModule ];
      perSystem = { self', system, pkgs, ... }: {
        haskellProjects.default = {
          basePackages = pkgs.haskell.packages.ghc96;
          # To get access to non-Haskell dependencies one most add them to `extraBuildDepends`
          # and then use the haskell package `which` to locate the Filepath of the executable
          # that's being added. In this toy example we'll be using the non-Haskell dependency
          # `cowsay` findable in nixpkgs like so:
          #
          # telomare = {
          #   extraBuildDepends = [ pkgs.cowsay
          #                       ];
          # };
          #
          # An example of Haskell code using `cowsay` would be:
          # ```haskell
          # cowsayBin :: FilePath
          # cowsayBin = $(staticWhich "cowsay")

          # cowsay :: IO String
          # cowsay = do
          #   (_, mhout, _, _) <- createProcess (shell $ show cowsayBin <> " hola") { std_out = CreatePipe }
          #   case mhout of
          #     Just hout -> hGetContents hout
          #     Nothing -> pure "mhout failed"
          # ```
          # settings = {
          #   semaphore-compat = {
          #     check = false;
          #     jailbreak = true;
          #   };
          # };
	  settings = {
	    telomare = {
		extraBuildDepends = with pkgs; [
		  # Node.js and npm for Claude Code
		  #nodejs_20
		  nodejs_22
		  nodePackages.npm
		];
	    };
	  };
          devShell = {
            enable = true;
            tools = hp: {
              inherit (hp) cabal-install haskell-language-server;
            } // {
	      inherit (pkgs) nodejs_22;
	      inherit (pkgs.nodePackages) npm;
	    };
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
      apps.evaluare = {
        type = "app";
        program = self.packages.${system}.telomare + "/bin/telomare-evaluare";
      };
      apps.lsp = {
        type = "app";
        program = "${self.packages.${system}.telomare}/bin/telomare-lsp";
      };
      apps.format-lint = {
        type = "app";
        program = "${pkgs.writeShellApplication {
          name = "telomare-format-lint-check";
          runtimeInputs = [
            pkgs.diffutils
            pkgs.git
            pkgs.haskellPackages.hlint
            pkgs.haskellPackages.stylish-haskell
          ];
          text = ''
            mapfile -t hs_files < <(git ls-files '*.hs')
            tmp_dir="$(mktemp -d)"
            trap 'rm -rf "$tmp_dir"' EXIT

            format_status=0
            if [ "''${#hs_files[@]}" -gt 0 ]; then
              for hs_file in "''${hs_files[@]}"; do
                formatted_file="$tmp_dir/$(basename "$hs_file")"
                stylish-haskell "$hs_file" > "$formatted_file"

                if ! cmp -s "$hs_file" "$formatted_file"; then
                  printf '%s needs formatting. Suggested diff:\n' "$hs_file"
                  diff -u "$hs_file" "$formatted_file" || true
                  format_status=1
                fi
              done
            fi

            if [ "$format_status" -ne 0 ]; then
              exit "$format_status"
            fi

            hlint .

            printf 'Formatting and linting are OK\n'
          '';
        }}/bin/telomare-format-lint-check";
      };

      checks = self'.packages;
    };
  };
}
