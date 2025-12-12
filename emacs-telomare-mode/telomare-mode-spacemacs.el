;; Define Telomare mode
(define-derived-mode telomare-mode prog-mode "Telomare"
  "Major mode for editing Telomare files."
  (setq-local comment-start "-- ")
  (setq-local comment-end ""))

;; Associate .tel files with telomare-mode
(add-to-list 'auto-mode-alist '("\\.tel\\'" . telomare-mode))


;; Configure LSP for Telomare
(with-eval-after-load 'lsp-mode
  ;; Register the Telomare language server
  (lsp-register-client
   (make-lsp-client
    :new-connection (lsp-stdio-connection '("path/to/your/telomare-lsp-exe"))
    :activation-fn (lsp-activate-on "telomare")
    :server-id 'telomare-lsp
    :priority -1
    :initialization-options '()
    :notification-handlers (lsp-ht)
    :request-handlers (lsp-ht)
    :completion-in-comments? t))

  (add-to-list 'lsp-language-id-configuration
               '(telomare-mode . "telomare"))

  )

;; Configure LSP for Telomare
(with-eval-after-load 'lsp-mode
  ;; Enable semantic tokens
  (setq lsp-semantic-tokens-enable t)

  (add-to-list 'lsp-language-id-configuration '(telomare-mode . "telomare"))

  (lsp-register-client
   (make-lsp-client
    :new-connection (lsp-stdio-connection
                     (lambda ()
                       (list "nix" "run" "/home/hhefesto/src/telomare#lsp" "--")))
    :activation-fn (lsp-activate-on "telomare")
    :major-modes '(telomare-mode)
    :server-id 'telomare-lsp))
  (add-to-list 'lsp-language-id-configuration
               '(telomare-mode . "telomare")))

;; Auto-start LSP in telomare-mode
(add-hook 'telomare-mode-hook #'lsp)

(provide 'telomare-mode-spacemacs)
;;; telomare-config.el ends here
