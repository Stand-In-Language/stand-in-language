;;; telomare-mode-common.el --- Common Telomare mode functionality -*- lexical-binding: t; -*-

;; Author: Your Name
;; Version: 0.1.0
;; Package-Requires: ((emacs "26.1"))
;; Keywords: languages, telomare, lsp

;;; Commentary:

;; Common functionality for Telomare mode shared across all Emacs variants.
;; The LSP server provides semantic tokens, hover, and text synchronization.

;;; Code:

(defgroup telomare nil
  "Support for the Telomare language."
  :group 'languages)

(defcustom telomare-lsp-command
  '("nix" "run" "/home/hhefesto/src/telomare#lsp" "--")
  "Command to start the Telomare LSP server."
  :type '(repeat string)
  :group 'telomare)

;; Define the major mode
;;;###autoload
(define-derived-mode telomare-mode prog-mode "Telomare"
  "Major mode for editing Telomare files."
  (setq-local comment-start "-- ")
  (setq-local comment-end "")
  (setq-local comment-start-skip "--+\\s-*"))

;; File association
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.tel\\'" . telomare-mode))

;; Common LSP setup function
(defun telomare-register-lsp-client ()
  "Register the Telomare LSP client."
  (when (fboundp 'lsp-register-client)
    (lsp-register-client
     (make-lsp-client
      :new-connection (lsp-stdio-connection
                       (lambda () telomare-lsp-command))
      :activation-fn (lsp-activate-on "telomare")
      :major-modes '(telomare-mode)
      :server-id 'telomare-lsp))))

(provide 'telomare-mode-common)
;;; telomare-mode-common.el ends here
