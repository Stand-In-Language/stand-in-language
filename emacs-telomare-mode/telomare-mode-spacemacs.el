;;; telomare-mode-spacemacs.el --- Telomare mode configuration for Spacemacs -*- lexical-binding: t; -*-

;; Author: Your Name
;; Version: 0.1.0
;; Package-Requires: ((emacs "26.1"))

;;; Commentary:

;; Spacemacs specific configuration for Telomare mode.
;; Add (load "path/to/telomare-mode-spacemacs.el") to dotspacemacs/user-config

;;; Code:

;; Load common functionality
(require 'telomare-mode-common)

;; Spacemacs-specific setup
(defun telomare-spacemacs-setup ()
  "Set up Telomare mode for Spacemacs."
  ;; Register LSP client when lsp-mode is available
  (with-eval-after-load 'lsp-mode
    (telomare-register-lsp-client))

  ;; Use lsp-deferred for better Spacemacs performance
  (add-hook 'telomare-mode-hook #'lsp-deferred 'append)

  ;; Essential Spacemacs-style keybindings
  (spacemacs/set-leader-keys-for-major-mode 'telomare-mode
    "g" #'lsp-find-definition
    "G" #'lsp-find-references
    "h" #'lsp-describe-thing-at-point
    "r" #'lsp-rename
    "a" #'lsp-execute-code-action))

;; Initialize
(telomare-spacemacs-setup)

(provide 'telomare-mode-spacemacs)
;;; telomare-mode-spacemacs.el ends here
