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
      perSystem = { self', system, pkgs, ... }:
        let
          # The GHC package set used for the build and all tooling. This is
          # nixpkgs' default (curated) set, so package coverage and HLS
          # support are the best available.
          hsPkgs = pkgs.haskell.packages.ghc910;
          lspVersion =
            if self ? lastModifiedDate then
              let
                timestamp = self.lastModifiedDate;
                year = builtins.substring 0 4 timestamp;
                month = builtins.substring 4 2 timestamp;
                day = builtins.substring 6 2 timestamp;
                hour = builtins.substring 8 2 timestamp;
                minute = builtins.substring 10 2 timestamp;
              in "${year}-${month}-${day}T${hour}:${minute}Z"
            else
              "unknown";

          telomareLsp = pkgs.writeShellApplication {
            name = "telomare-lsp";
            text = ''
              export TELOMARE_LSP_VERSION="${lspVersion}"
              exec "${self.packages.${system}.telomare}/bin/telomare-lsp" "$@"
            '';
          };

          # Format and lint the tracked Haskell files. `--check` reports needed
          # changes without applying them; otherwise formatting is applied in
          # place. Scoping to `git ls-files` is what keeps this identical to CI:
          # recursing over `.` locally wanders into untracked trees like
          # .direnv/ and dist-newstyle/ and aborts on read-only store files.
          telomareFormat = pkgs.writeShellApplication {
            name = "telomare-format";
            runtimeInputs = [
              pkgs.diffutils
              pkgs.git
              hsPkgs.hlint
              hsPkgs.stylish-haskell
            ];
            text = ''
              mapfile -t hs_files < <(git ls-files '*.hs')
              if [ "''${#hs_files[@]}" -eq 0 ]; then
                echo "No tracked Haskell files found"
                exit 0
              fi

              format_status=0
              if [ "''${1:-}" = "--check" ]; then
                tmp_dir="$(mktemp -d)"
                trap 'rm -rf "$tmp_dir"' EXIT
                for hs_file in "''${hs_files[@]}"; do
                  formatted_file="$tmp_dir/$(basename "$hs_file")"
                  stylish-haskell "$hs_file" > "$formatted_file"
                  if ! cmp -s "$hs_file" "$formatted_file"; then
                    printf '%s needs formatting. Suggested diff:\n' "$hs_file"
                    diff -u "$hs_file" "$formatted_file" || true
                    format_status=1
                  fi
                done
              else
                echo "Formatting ''${#hs_files[@]} tracked Haskell files"
                stylish-haskell -i "''${hs_files[@]}"
              fi

              lint_status=0
              hlint "''${hs_files[@]}" || lint_status=$?

              if [ "$format_status" -ne 0 ]; then
                printf 'Formatting check failed\n'
              fi
              if [ "$lint_status" -ne 0 ]; then
                printf 'Linting check failed\n'
              fi
              if [ "$format_status" -ne 0 ] || [ "$lint_status" -ne 0 ]; then
                exit 1
              fi

              printf 'Formatting and linting are OK\n'
            '';
          };

          telomareFormatLint = pkgs.writeShellScriptBin "telomare-format-lint-check" ''
            exec ${telomareFormat}/bin/telomare-format --check
          '';
        in {
        haskellProjects.default = {
          basePackages = hsPkgs;
          devShell = {
            enable = true;
            tools = hp: {
              inherit (hp) cabal-install haskell-language-server;
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
      apps.lsp = {
        type = "app";
        program = "${telomareLsp}/bin/telomare-lsp";
      };
      apps.format = {
        type = "app";
        program = "${telomareFormat}/bin/telomare-format";
      };
      apps.format-lint = {
        type = "app";
        program = "${telomareFormatLint}/bin/telomare-format-lint-check";
      };
      apps.push-cachix = {
        type = "app";
        program = "${pkgs.writeShellApplication {
          name = "telomare-push-cachix";
          runtimeInputs = [
            pkgs.cachix
            pkgs.jq
            pkgs.nixVersions.nix_2_31
          ];
          text = ''
            cache_name=telomare
            tmp_dir="$(mktemp -d)"
            trap 'rm -rf "$tmp_dir"' EXIT

            direct_paths="$tmp_dir/direct-paths"
            closure_paths="$tmp_dir/closure-paths"
            key_paths="$tmp_dir/key-paths"
            : > "$direct_paths"
            : > "$key_paths"

            build_target() {
              local target="$1"
              local output_path
              printf 'Building %s\n' "$target"
              output_path="$(nix build --no-link --print-out-paths "$target")"
              printf '%s\n' "$output_path" >> "$direct_paths"
              printf '%s\n' "$output_path" >> "$key_paths"
            }

            build_target ".#packages.${system}.default"
            build_target ".#checks.${system}.default"
            build_target ".#devShells.${system}.default"

            printf 'Building nix develop environment closure\n'
            dev_env_profile="$tmp_dir/dev-env-profile"
            nix print-dev-env --profile "$dev_env_profile" ".#devShells.${system}.default" >/dev/null
            dev_env_path="$(nix path-info "$dev_env_profile")"
            printf '%s\n' "$dev_env_path" >> "$direct_paths"
            printf '%s\n' "$dev_env_path" >> "$key_paths"

            printf 'Building legacy default.nix with nix-build\n'
            legacy_build_path="$(nix-build --no-out-link)"
            printf '%s\n' "$legacy_build_path" >> "$direct_paths"
            printf '%s\n' "$legacy_build_path" >> "$key_paths"

            printf 'Building legacy shell.nix closure with nix-store\n'
            legacy_shell_drv="$(nix-instantiate shell.nix)"
            legacy_shell_path="$(nix-store --realise "$legacy_shell_drv")"
            printf '%s\n' "$legacy_shell_path" >> "$direct_paths"
            printf '%s\n' "$legacy_shell_path" >> "$key_paths"
            nix-store --query --requisites --include-outputs "$legacy_shell_drv" >> "$direct_paths"

            printf 'Archiving flake source and inputs\n'
            nix flake archive --json \
              | jq -r '.. | objects | .path? // empty' \
              >> "$direct_paths"

            # The shell apps. Naming them by interpolation rather than by
            # `nix eval` of `apps.<name>.program` makes them build inputs of
            # this script, so they are realised whenever it runs; an evaluated
            # path is merely a name, and `nix path-info` rejects it when the
            # derivation behind it has not been built. The `default` and `repl`
            # apps need no entry: they live in the package built above.
            printf 'Including the shell apps\n'
            printf '%s\n' \
              "${telomareLsp}" \
              "${telomareFormat}" \
              "${telomareFormatLint}" \
              >> "$direct_paths"

            sort -u "$direct_paths" \
              | xargs nix path-info --recursive \
              | sort -u \
              > "$closure_paths"

            path_count="$(wc -l < "$closure_paths")"
            printf 'Pushing %s store paths to Cachix cache %s\n' "$path_count" "$cache_name"
            cachix push "$cache_name" < "$closure_paths"

            printf 'Verifying key paths in Cachix cache %s\n' "$cache_name"
            while IFS= read -r key_path; do
              printf 'Verifying %s\n' "$key_path"
              nix path-info --store "https://$cache_name.cachix.org" "$key_path" >/dev/null
            done < "$key_paths"

            printf 'Cachix push completed for cache %s\n' "$cache_name"
          '';
        }}/bin/telomare-push-cachix";
      };

      # `nix flake check` builds the packages and verifies formatting and
      # linting. The flake source only contains tracked files, so this
      # covers the same file set as `nix run .#format` / `.#format-lint`
      # and the CI format/lint jobs.
      checks = self'.packages // {
        format-lint = pkgs.runCommand "telomare-format-lint-check"
          {
            nativeBuildInputs = [
              pkgs.diffutils
              pkgs.findutils
              hsPkgs.hlint
              hsPkgs.stylish-haskell
            ];
            LC_ALL = "C.UTF-8";
          } ''
            cp -r ${self} source
            chmod -R u+w source
            cd source
            find . -type f -name '*.hs' -print0 | xargs -0 stylish-haskell -i
            cd ..
            if ! diff -ru ${self} source; then
              echo "Formatting check failed: stylish-haskell has the suggestions diffed above."
              echo "Run 'nix run .#format' to apply them."
              exit 1
            fi
            cd source
            if ! find . -type f -name '*.hs' -print0 | xargs -0 hlint; then
              echo "Linting check failed: fix the hints above or add exceptions to .hlint.yaml."
              exit 1
            fi
            touch $out
          '';
      };
    };
  };
}
