# Telomare
> A simple but robust virtual machine

<p float="left">
  <img src="https://github.com/Stand-in-Language/stand-in-language/actions/workflows/telomare-ci.yml/badge.svg" />
  <a href="https://gitter.im/stand-in-language/Lobby?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge"
     title="Join the chat at https://gitter.im/stand-in-language/Lobby">
    <img src="https://badges.gitter.im/stand-in-language/Lobby.svg" /> 
  </a>
</p>


A virtual machine with a simple grammar evolved from simply typed lambda calculus, that eventually will have powerful static checking and an optimizing backend.

## Warning
This project is in active development. Do expect bugs and general trouble, and please let us know if you run into any by creating a new issue if one does not already exist.

## Quick Start

1. Clone this repository and change directory to it:
   ```sh
   $ git clone https://github.com/Stand-In-Language/stand-in-language.git
   $ cd stand-in-language
   ```
2. [Install Nix](https://nixos.org/nix/download.html):
   ```sh
   $ curl https://nixos.org/nix/install | sh
   ```
3. Optional (reduces build time by using telomare's cache):
   ```sh
   # Install cachix with nix-env or adding `cachix` to your `/etc/nixos/configuration.nix`'s' `environment.systemPackages` if in NixOS.
   $ cachix use telomare
   ```
4. Enter a Nix shell. This will setup an environment where all external dependencies will be available (such as `cabal` for building):
   ```sh
   $ nix develop # or nix develop -c zsh
   ```
5. Build the project:
   ```sh
   $ cabal build # or nix build
   ```
6. Run the tictactoe example and start playing with a friend (or run your own telomare file):
   ```sh
   $ cabal run telomare -- tictactoe.tel # or nix run . -- tictactoe.tel
   ```
7. Profit!

## Telomare REPL
1. Run:
   ```sh
   $ cd <your/local/proyect/location>/telomare
   $ nix develop -c zsh
   $ cabal run telomare-repl -- --haskell # or nix run .#repl
   ```
2. Profit!

## Editor Support (LSP)

Telomare ships a language server (`telomare-lsp`) and an Emacs major mode
under [`emacs-telomare-mode/`](emacs-telomare-mode/), with variants for
Spacemacs, Doom, and vanilla Emacs.

### LSP capabilities

The language server provides:

- **Diagnostics** — on every document open and edit it reports parse
  errors, missing imported modules, undefined variable references, and
  resolver errors. Diagnostics are cleared when the document is closed.
- **Go to definition** — jumps to local `let`, lambda, and case-pattern
  binders, to top-level definitions, and to definitions in qualified
  imported modules.
- **Find references** — lists every reference to a symbol, optionally
  including its declaration.
- **Semantic-token highlighting** — keywords, comments, strings,
  numbers, and operators, for the whole file or a requested range.
- **Code action** — *Partially evaluate*: select an expression and the
  server evaluates it, reporting the result in an editor popup.
- **Workspace commands**:
  - `telomare.version` — reports the server version as a UTC timestamp.
  - `telomare.partialEval` — evaluates a given expression; this backs
    the partial-evaluation code action.

Document sync is full-text (whole-document). Hover and rename are not
implemented yet.

### Installing the Emacs mode

The recommended Spacemacs setup is to load Telomare's Emacs mode from the
same Telomare flake input that provides the language server. Do not point
Spacemacs at a random checkout unless you are actively developing the mode;
make the editor use the same pinned source that NixOS or Home Manager builds.

For a NixOS/Home Manager Spacemacs config, add Telomare as a flake input and
load the mode file from that input:

```elisp
(load "${telomare}/emacs-telomare-mode/telomare-mode-spacemacs.el")
```

The mode auto-detects the surrounding flake source path and starts the LSP with
`nix run path:<telomare-source>#lsp --`. This matters for Nix store paths:
`nix run /nix/store/...-source#lsp --` is parsed incorrectly by Nix, while
`nix run path:/nix/store/...-source#lsp --` is the intended absolute-path flake
form.

For a manual checkout-based setup, load the mode from this repository and set
`TELOMARE_ROOT` only if auto-detection cannot find `flake.nix`:

```elisp
(load "/path/to/telomare/emacs-telomare-mode/telomare-mode-spacemacs.el")
```

For Doom and vanilla Emacs setup, see
[`emacs-telomare-mode/README.md`](emacs-telomare-mode/README.md).

### Keybindings

The mode binds only features the server implements. Some entries below
come from `lsp-mode` rather than Telomare's mode — these are marked
*(lsp-mode)*. Spacemacs exposes the major-mode leader as `SPC m` in Evil
state and as `M-m m` in holy-mode; the leader entries are otherwise the
same bindings.

**Spacemacs — Evil mode** (`SPC m` major-mode leader):

| Key | Action |
|-----|--------|
| `SPC m g` | Go to definition |
| `SPC m G` | Find references |
| `SPC m a` | Execute code action (partial evaluation) |
| `SPC m v` | Show Telomare LSP version |
| `C-c C-v` | Show Telomare LSP version |
| `g d` | Go to definition *(lsp-mode / Evil default)* |

**Spacemacs — holy mode** (`M-m m` major-mode leader):

| Key | Action |
|-----|--------|
| `M-m m g` | Go to definition |
| `M-m m G` | Find references |
| `M-m m a` | Execute code action (partial evaluation) |
| `M-m m v` | Show Telomare LSP version |
| `C-c C-v` | Show Telomare LSP version |
| `M-.` | Go to definition *(lsp-mode)* |
| `M-?` | Find references *(lsp-mode)* |
| `M-,` | Jump back *(xref)* |

Vanilla Emacs binds `M-.`, `M-?`, `C-c a`, and `C-c C-v`.

### Troubleshooting

If navigation does not work, check the active LSP session with
`M-x lsp-describe-session`, restart it with `M-x lsp-workspace-restart`, and
confirm the server command with:

```elisp
M-: (telomare--lsp-command)
```

The expected command shape is:

```elisp
("nix" "run" "path:/nix/store/...-source#lsp" "--")
```

### LSP version command

`C-c C-v` (or `SPC m v` / `M-m m v` in Spacemacs) reports the server
version as a UTC timestamp truncated to minutes, using the parent commit
timestamp when git history is available and the flake source timestamp
when launched from a Nix store source without `.git`. It can also be
invoked directly:

```elisp
(lsp-request "workspace/executeCommand"
             `(:command "telomare.version" :arguments []))
```

The command shows an editor message such as:

```text
Telomare LSP version: 2026-05-22T10:14Z
```

## Git Hooks

You can setup your git configuration to automatically format and look for lint suggestions. Just run:

``` sh
$ git config core.hooksPath hooks
```

## Contributing
If you'd like to contribute, please fork the repository and use a feature branch. Pull requests are warmly welcome.

## Links
1. [A Better Model of Computation](http://sfultong.blogspot.com/2016/12/a-better-model-of-computation.html?m=1) by Sfultong
2. [SIL: Explorations in non-Turing Completeness](http://sfultong.blogspot.com/2017/09/sil-explorations-in-non-turing.html?m=1) by Sfultong
3. [Deconstructing Lambdas, Closures and Application](http://sfultong.blogspot.com/2018/04/deconstructing-lambdas-closures-and.html?m=1) by Sfultong
4. [Join the community's chat](https://gitter.im/stand-in-language/Lobby)


## Licensing
The code in this project is licensed under the Apache License 2.0. For more information, please refer to the [LICENSE file](https://github.com/Stand-In-Language/stand-in-language/blob/master/LICENSE).
