# Telomare Mode for Emacs

LSP-enabled major mode for the Telomare programming language, with support for Doom Emacs, Spacemacs, and vanilla Emacs.

## Features

Based on the Telomare LSP server capabilities:
- **Syntax highlighting** via semantic tokens (keywords, comments, strings, numbers, operators)
- **Hover information** showing expression evaluation and parse errors
- **Go to definition** and **Find references** (via LSP)
- **Rename symbol** support
- **Parse error reporting** displayed on hover
- **Comment support** (`-- comments`)

## Installation

### Prerequisites

Ensure your Telomare LSP server is available at the configured path (default: `/home/hhefesto/src/telomare#lsp`).

### Modular Configuration (4 files)

Place all four files in a directory in your load-path. All variants require `telomare-mode-common.el`.

#### Doom Emacs

1. Place all files in `~/.doom.d/lisp/`
2. Add to your `config.el`:
```elisp
(load! "lisp/telomare-mode-doom")
```
3. Run `doom sync`

#### Spacemacs

1. Place all files in `~/.spacemacs.d/lisp/`
2. Add to `dotspacemacs/user-config`:
```elisp
(add-to-list 'load-path "~/.spacemacs.d/lisp/")
(require 'telomare-mode-spacemacs)
```
3. Ensure the `lsp` layer is enabled in `dotspacemacs-configuration-layers`

#### Vanilla Emacs

1. Place all files in `~/.emacs.d/lisp/`
2. Add to your `init.el`:
```elisp
(add-to-list 'load-path "~/.emacs.d/lisp/")
(require 'telomare-mode-vanilla)
```
3. Install lsp-mode if not present:
```elisp
(package-install 'lsp-mode)
```

## Configuration

### Customizing the LSP Command

```elisp
;; Use a different nix path
(setq telomare-lsp-command '("nix" "run" "/path/to/your/telomare#lsp" "--"))

;; Use a local binary
(setq telomare-lsp-command '("/usr/local/bin/telomare-lsp"))
```

## Key Bindings

### Doom Emacs
- `SPC m g` - Go to definition TODO: improve
- `SPC m G` - Find references  
- TODO: `SPC m h` - Describe at point (hover)
- TODO: `SPC m r` - Rename symbol

### Spacemacs
- `SPC m g` - Go to definition TODO: improve
- `SPC m G` - Find references
- TODO: `SPC m h` - Describe at point (hover)
- TODO: `SPC m r` - Rename symbol

### Vanilla Emacs
- `M-.` - Go to definition
- `M-?` - Find references
- TODO: `C-c h` - Describe at point (hover)
- TODO: `C-c r` - Rename symbol

## Troubleshooting

1. **LSP not starting**: Test your LSP command in terminal:
   ```bash
   nix run /home/hhefesto/src/telomare#lsp --
   ```

2. **Check LSP status**: With a `.tel` file open, run:
   - `M-x lsp-describe-session`

3. **View LSP logs**: Check the `*lsp-log*` buffer for errors

## File Structure

- `telomare-mode-common.el` - Core mode definition and LSP client registration
- `telomare-mode-doom.el` - Doom Emacs specific keybindings and setup
- `telomare-mode-spacemacs.el` - Spacemacs specific keybindings and setup  
- `telomare-mode-vanilla.el` - Vanilla Emacs minimal configuration
