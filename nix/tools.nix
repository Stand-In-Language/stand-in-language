# The shell apps and the format/lint check, as they were in the flake before
# the move to ekapkgs. Scripts are linted with shellcheck explicitly:
# corepkgs' `writeShellApplication` refers to a `shellcheck-minimal` that the
# package set does not define, so the default check phase cannot evaluate.
# `gitMinimal` rather than `git`: the scripts only list and read tracked files,
# and the full git brings its manual (asciidoc, perl) into the closure.
{
  pkgs,
  src,
  lspVersion,
  telomare,
  tools,
  executables,
  devShellNames,
  checkNames,
  appNames,
}:
let
  inherit (pkgs) lib;
  system = pkgs.stdenv.hostPlatform.system;

  mkScript =
    args:
    pkgs.writeShellApplication (
      args
      // {
        checkPhase = ''
          runHook preCheck
          ${pkgs.stdenv.shellDryRun} "$target"
          ${lib.getExe executables.shellcheck} "$target"
          runHook postCheck
        '';
      }
    );

  # `telomare-lsp` reports the checkout's timestamp as its version; the flake
  # knows it, so hand it over. The binary shells out to git for the same
  # purpose, hence git on its PATH.
  telomareLsp = mkScript {
    name = "telomare-lsp";
    runtimeInputs = [ pkgs.gitMinimal ];
    text = ''
      export TELOMARE_LSP_VERSION="${lspVersion}"
      exec "${telomare}/bin/telomare-lsp" "$@"
    '';
  };

  # Format and lint the tracked Haskell files. `--check` reports needed
  # changes without applying them; otherwise formatting is applied in
  # place. Scoping to `git ls-files` is what keeps this identical to CI:
  # recursing over `.` locally wanders into untracked trees like
  # .direnv/ and dist-newstyle/ and aborts on read-only store files.
  telomareFormat = mkScript {
    name = "telomare-format";
    runtimeInputs = [
      pkgs.diffutils
      pkgs.gitMinimal
      tools.hlint
      tools.stylish-haskell
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

  # `nix flake check` verifies formatting and linting over the flake source,
  # which is the tracked files — the same set `nix run .#format` and the CI
  # format/lint steps see.
  formatLintCheck =
    pkgs.runCommand "telomare-format-lint-check"
      {
        nativeBuildInputs = [
          pkgs.diffutils
          pkgs.findutils
          tools.hlint
          tools.stylish-haskell
        ];
        LC_ALL = "C.UTF-8";
      }
      ''
        cp -r ${src} source
        chmod -R u+w source
        cd source
        find . -type f -name '*.hs' -print0 | xargs -0 stylish-haskell -i
        cd ..
        if ! diff -ru ${src} source; then
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

  # Neither cachix nor nix is pinned here: the ekapkgs snapshot has no cachix
  # that builds (its amazonka 2.0 dependencies predate GHC 9.8), corepkgs'
  # Nix is a from-source build nothing else needs, and this is a maintainer's
  # tool, so it uses the cachix already installed for `cachix use telomare`
  # and the nix the flake is being used with.
  pushCachix = mkScript {
    name = "telomare-push-cachix";
    runtimeInputs = [ pkgs.jq ];
    text = ''
      for tool in cachix nix; do
        if ! command -v "$tool" >/dev/null; then
          echo "$tool not found on PATH: install it (https://docs.cachix.org) and log in first" >&2
          exit 1
        fi
      done
      cache_name=telomare
      tmp_dir="$(mktemp -d)"
      trap 'rm -rf "$tmp_dir"' EXIT

      direct_paths="$tmp_dir/direct-paths"
      closure_paths="$tmp_dir/closure-paths"
      key_paths="$tmp_dir/key-paths"
      : > "$direct_paths"
      : > "$key_paths"

      # Everything built here stays a garbage collector root until the push
      # is over: Nix may collect garbage while this runs (Determinate Nix
      # does on its own when the disk runs low), and an unrooted output is
      # garbage as soon as it is built.
      roots="$tmp_dir/roots"
      mkdir "$roots"

      build_target() {
        local target="$1"
        local output_path
        printf 'Building %s\n' "$target"
        output_path="$(nix build --out-link "$(mktemp -u "$roots/XXXXXXXX")" \
          --print-out-paths "$target")"
        printf '%s\n' "$output_path" >> "$direct_paths"
        printf '%s\n' "$output_path" >> "$key_paths"
      }

      build_target ".#packages.${system}.default"

      # Every check, so that `nix flake check` in CI substitutes all of them.
      for check_name in ${lib.escapeShellArgs checkNames}; do
        build_target ".#checks.${system}.$check_name"
      done

      # Include every declared shell and the environment used by nix develop.
      # In particular, the full shell carries HLS and the editor tools.
      for shell_name in ${lib.escapeShellArgs devShellNames}; do
        shell_target=".#devShells.${system}.$shell_name"
        build_target "$shell_target"
        printf 'Building nix develop environment closure for %s\n' "$shell_name"
        dev_env_profile="$tmp_dir/dev-env-profile-$shell_name"
        nix print-dev-env --profile "$dev_env_profile" "$shell_target" >/dev/null
        dev_env_path="$(nix path-info "$dev_env_profile")"
        printf '%s\n' "$dev_env_path" >> "$direct_paths"
        printf '%s\n' "$dev_env_path" >> "$key_paths"
      done

      printf 'Archiving flake source and inputs\n'
      source_count=0
      while IFS= read -r source_path; do
        source_count=$((source_count + 1))
        nix-store --realise --add-root "$roots/source-$source_count" \
          "$source_path" >/dev/null
        printf '%s\n' "$source_path" >> "$direct_paths"
      done < <(nix flake archive --json | jq -r '.. | objects | .path? // empty')

      # Every app, built from the derivation its program comes from: an
      # evaluated program path is merely a name, and `nix path-info`
      # rejects it until that derivation is built. They are not
      # interpolated into this script because the LSP wrapper carries the
      # checkout's timestamp: naming it here would make this script, and so
      # `checks.push-cachix`, differ on every commit, and CI, which builds a
      # pull request's merge commit, would never find either in the cache.
      for app_name in ${lib.escapeShellArgs appNames}; do
        app_drv="$(nix eval --raw ".#apps.${system}.$app_name.program" \
          --apply 'program: builtins.head (builtins.attrNames (builtins.getContext program))')"
        build_target "$app_drv^*"
      done

      # The shell apps are linted at build time by this ShellCheck, which is
      # in no closure above; without it, building a wrapper at a commit
      # nobody pushed from compiles ShellCheck and its libraries.
      printf '%s\n' "${executables.shellcheck}" >> "$direct_paths"

      sort -u "$direct_paths" \
        | xargs nix path-info --recursive \
        | sort -u \
        > "$closure_paths"

      path_count="$(wc -l < "$closure_paths")"
      printf 'Pushing %s store paths to Cachix cache %s\n' "$path_count" "$cache_name"
      cachix push "$cache_name" < "$closure_paths"

      # A lookup that missed before the push is remembered by Nix for an
      # hour (narinfo-cache-negative-ttl), so verify without that memory.
      printf 'Verifying key paths in Cachix cache %s\n' "$cache_name"
      while IFS= read -r key_path; do
        printf 'Verifying %s\n' "$key_path"
        nix path-info --store "https://$cache_name.cachix.org" \
          --narinfo-cache-negative-ttl 0 "$key_path" >/dev/null
      done < "$key_paths"

      printf 'Cachix push completed for cache %s\n' "$cache_name"
    '';
  };
in
{
  inherit
    telomareLsp
    telomareFormat
    telomareFormatLint
    formatLintCheck
    pushCachix
    ;
}
