;;; telomare-mode-spacemacs.el --- Telomare major-mode + LSP for Spacemacs -*- lexical-binding: t; -*-

(defgroup telomare nil
  "Support for the Telomare language."
  :group 'languages)

(defcustom telomare-project-root
  (or (getenv "TELOMARE_ROOT")
      ;; If this file lives inside the repo, try to auto-detect the flake root:
      (let* ((this (or load-file-name (buffer-file-name)))
             (dir  (and this (file-name-directory this)))
             (root (and dir (locate-dominating-file dir "flake.nix"))))
        (when root (expand-file-name root))))
  "Path to the Telomare flake directory (the folder containing flake.nix).

Users should set this to something like \"~/src/telomare\".
You can also set TELOMARE_ROOT in your environment."
  :type '(choice (const :tag "Auto-detect / unset" nil)
                 (directory :tag "Telomare flake directory"))
  :group 'telomare)

(defcustom telomare-lsp-flake-attr "lsp"
  "Flake app/package attribute to run for the Telomare language server."
  :type 'string
  :group 'telomare)

(defun telomare--lsp-command ()
  "Return the command list used to start the Telomare LSP server."
  (unless (and telomare-project-root
               (file-exists-p (expand-file-name "flake.nix" telomare-project-root)))
    (user-error "telomare-project-root is not set (or has no flake.nix). Set it to your Telomare repo path"))
  (let* ((root  (file-truename (expand-file-name telomare-project-root)))
         (flake (format "%s#%s" root telomare-lsp-flake-attr)))
    (list "nix" "run" flake "--")))

;; Define Telomare mode
(define-derived-mode telomare-mode prog-mode "Telomare"
  "Major mode for editing Telomare files."
  (setq-local comment-start "-- ")
  (setq-local comment-end ""))

;; Associate .tel files with telomare-mode
(add-to-list 'auto-mode-alist '("\\.tel\\'" . telomare-mode))

;; Configure LSP for Telomare
(with-eval-after-load 'lsp-mode
  (setq lsp-semantic-tokens-enable t)
  (add-to-list 'lsp-language-id-configuration '(telomare-mode . "telomare"))
  (lsp-register-client
   (make-lsp-client
    :new-connection (lsp-stdio-connection #'telomare--lsp-command)
    :activation-fn (lsp-activate-on "telomare")
    :major-modes '(telomare-mode)
    :server-id 'telomare-lsp)))

;; Auto-start LSP in telomare-mode
(add-hook 'telomare-mode-hook #'lsp)

(provide 'telomare-mode-spacemacs)
;;; telomare-mode-spacemacs.el ends here
