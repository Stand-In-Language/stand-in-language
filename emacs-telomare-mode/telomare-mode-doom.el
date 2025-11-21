;; ;; telomare lsp:

;; Define Telomare mode
(define-derived-mode telomare-mode prog-mode "Telomare"
  "Major mode for editing Telomare files."
  (setq-local comment-start "-- ")
  (setq-local comment-end ""))

;; Associate .tel files with telomare-mode
(add-to-list 'auto-mode-alist '("\\.tel\\'" . telomare-mode))

;; Configure LSP for Telomare using nix run
(with-eval-after-load 'lsp-mode
  ;; (add-to-list 'lsp-language-id-configuration '(telomare-mode . "telomare"))

  ;; Enable semantic tokens
  (setq lsp-semantic-tokens-enable t)

  (lsp-register-client
   (make-lsp-client
    :new-connection (lsp-stdio-connection
                     (lambda ()
                       (list "nix" "run" "/home/hhefesto/src/telomare#lsp" "--")))
    :activation-fn (lsp-activate-on "telomare")
    :major-modes '(telomare-mode)
    :server-id 'telomare-lsp
    ))
  )

;; Auto-start LSP in telomare-mode
;; (add-hook 'telomare-mode-hook #'lsp-deferred) ;; lazier/non-blocking
(add-hook 'telomare-mode-hook #'lsp)
