;;; telomare-mode-doom.el --- Telomare mode configuration for Doom Emacs -*- lexical-binding: t; -*-

;; Author: Your Name
;; Version: 0.1.0
;; Package-Requires: ((emacs "26.1"))

;;; Commentary:

;; Doom Emacs specific configuration for Telomare mode.
;; Add (load! "path/to/telomare-mode-doom.el") to your Doom config.el

;;; Code:

;; Load common functionality
(require 'telomare-mode-common)

;; Doom-specific LSP setup
(defun telomare-doom-setup ()
  "Set up Telomare mode for Doom Emacs."
  ;; Register LSP client after lsp-mode is loaded
  (after! lsp-mode
    (telomare-register-lsp-client))

  ;; Use Doom's lsp! macro for better integration
  (add-hook 'telomare-mode-hook #'lsp! 'append))

;; Initialize on load
(telomare-doom-setup)

;; Optional: Doom keybindings for convenience
(after! telomare-mode
  (map! :map telomare-mode-map
        :localleader
        "g" #'lsp-find-definition
        "G" #'lsp-find-references
        "h" #'lsp-describe-thing-at-point
        "r" #'lsp-rename
        "a" #'lsp-execute-code-action))

(provide 'telomare-mode-doom)
;;; telomare-mode-doom.el ends here
