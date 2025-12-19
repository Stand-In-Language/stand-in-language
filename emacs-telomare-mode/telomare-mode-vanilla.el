;;; telomare-mode-vanilla.el --- Telomare mode configuration for vanilla Emacs -*- lexical-binding: t; -*-

;; Author: Your Name
;; Version: 0.1.0
;; Package-Requires: ((emacs "26.1") (lsp-mode "8.0.0"))

;;; Commentary:

;; Vanilla Emacs specific configuration for Telomare mode.
;; Add (require 'telomare-mode-vanilla) to your init.el

;;; Code:

;; Load common functionality
(require 'telomare-mode-common)

;; Ensure lsp-mode is available
(require 'lsp-mode)

;; Vanilla Emacs specific setup
(defun telomare-vanilla-setup ()
  "Set up Telomare mode for vanilla Emacs."
  ;; Register LSP client
  (telomare-register-lsp-client)

  ;; Add LSP hook
  (add-hook 'telomare-mode-hook #'lsp-deferred 'append)

  ;; Set up minimal keybindings
  (define-key telomare-mode-map (kbd "M-.") #'lsp-find-definition)
  (define-key telomare-mode-map (kbd "M-?") #'lsp-find-references)
  (define-key telomare-mode-map (kbd "C-c h") #'lsp-describe-thing-at-point)
  (define-key telomare-mode-map (kbd "C-c r") #'lsp-rename)
  (define-key telomare-mode-map (kbd "C-c a") #'lsp-execute-code-action))

;; Initialize
(telomare-vanilla-setup)

(provide 'telomare-mode-vanilla)
;;; telomare-mode-vanilla.el ends here
