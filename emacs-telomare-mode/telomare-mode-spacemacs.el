(defun telomare-setup (project-path)
  "Set up Telomare major mode and LSP using PROJECT-PATH."

  (message "telomare-setup called")

  ;; --- Major mode ---
  (define-derived-mode telomare-mode prog-mode "Telomare"
    "Major mode for editing Telomare files."
    (setq-local comment-start "-- ")
    (setq-local comment-end ""))

  ;; --- File association ---
  (add-to-list 'auto-mode-alist '("\\.tel\\'" . telomare-mode))

  ;; --- Ensure lsp-mode is loaded ---
  (require 'lsp-mode)

  ;; --- Language ID ---
  (add-to-list 'lsp-language-id-configuration
               '(telomare-mode . "telomare"))

  ;; --- Register LSP client ---
  (lsp-register-client
   (make-lsp-client
    :server-id 'telomare-lsp
    :major-modes '(telomare-mode)
    :command-fn
    (lambda ()
      (message "🚀 Launching Telomare LSP")
      (list "nix" "run" (concat project-path "#lsp") "--"))))

  ;; --- Auto-start LSP ---
  (add-hook 'telomare-mode-hook #'lsp-deferred))

(provide 'telomare-config)
