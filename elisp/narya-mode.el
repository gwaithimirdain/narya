(defvar narya-dynamic-terms '()
  "List of dynamically identified terms for highlighting.")

(defun narya-update-dynamic-terms ()
  "Parse the buffer for user-defined constants following 'axiom|def|echo const' and update dynamic terms."
  (save-excursion
    (goto-char (point-min))
    (let ((terms '()))
      (setq my-proof-dynamic-terms '())
      (while (re-search-forward "\\(axiom\\|def\\|echo\\) \\([a-zA-Z0-9]+\\(?:_+[a-zA-Z0-9]+\\)*\\)\\s-*:" nil t)
        (let ((const-name (match-string 2)))
          (unless (member const-name terms)
            (push const-name terms))))
      ;; Remove duplicates and update the global list
      (setq narya-dynamic-terms (delete-dups terms)))))

(defun narya-apply-dynamic-highlighting ()
  "Apply dynamic highlighting for terms in `narya-dynamic-terms`."
  (font-lock-add-keywords nil `((,(regexp-opt narya-dynamic-terms 'words) . 'font-lock-variable-name-face)) t))

;; Define the syntax highlighting
(defvar narya-font-lock-keywords
  `(
    ;; Line comments
    ("`.*$" . 'font-lock-comment-face)
    ;; Block comments
    ("{`\\(.*?\\)`}" . 'font-lock-comment-face)
    ("\\<\\(axiom\\|def\\|echo\\)\\>" . 'font-lock-keyword-face)
    ("\\<\\(Type\\|Id\\|refl\\|sym\\|Gel\\|ungel\\)\\>" . 'font-lock-builtin-face)
    ))

;; Define the mode
(define-derived-mode narya-mode fundamental-mode "Narya"
  "A mode for editing my language files."
  (setq font-lock-defaults '(narya-font-lock-keywords))
  ;; Modify the syntax table for multi-line block comments
  (modify-syntax-entry ?\{ "(}1n" (syntax-table))
  (modify-syntax-entry ?\` ". 23n" (syntax-table))
  (modify-syntax-entry ?\} "){4n" (syntax-table))
  ;; Apply dynamic highlighting after changes
  (add-hook 'after-change-functions (lambda (start end old-len)
                                      (narya-update-dynamic-terms)
                                      (narya-apply-dynamic-highlighting))
            nil t)
  ;; Initialize dynamic highlighting
  (narya-update-dynamic-terms)
  (narya-apply-dynamic-highlighting))

(provide 'narya)

;; Automatically use narya-mode for .ny files
(add-to-list 'auto-mode-alist '("\\.ny\\'" . narya-mode))
