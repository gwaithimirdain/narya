;; narya-syntax.el --- Proof General instance for Narya - syntax file

(require 'subr-x)

;; We omit "display", "solve", "split", "show", "undo", and "chdir" because these should NOT appear in source files.
(defconst narya-commands
  "\\_<\\(axiom\\|def\\|echo\\|synth\\|notation\\|import\\|export\\|quit\\|section\\|option\\|end\\)\\_>")

;; As noted in the PG source, the default function proof-generic-state-preserving-p is not really correct; it thinks that things like "def" are state-preserving.  These are the commands that it makes sense for PG to issue directly to the prover without their being in the file.
(defun narya-state-preserving-p (cmd)
  (string-match "^echo\\|synth\\|show\\|display" cmd))

;; TODO: Do this for everything else too.
(defun narya-highlight-abstractions (limit)
  "Font-lock search function to find abstractions.
Only finds abstractions with a sequence of variables separated by
whitespace (no comments).  Finds the arguments of a simple match pattern
like \"constr. x y z ↦\", but not variables deeper inside nested or
multiple match patterns.  Unfortunately, also highlights underscores.
Does not handle sequences of abstraction variables broken across lines."
  (when (re-search-forward "[^[:word:][:space:]_'][[:space:]]*\\([[:word:][:space:]_']+\\)\\(↦\\||->\\|⤇\\||=>\\)" limit 'move)
    ;; Move back across the ↦, so it can be the non-word-non-space character that predelimits another abstraction afterwards.
    (backward-char 1)
    t))

(defun narya-next-hole-subdivision (limit)
  "Look for the next hole-ending or subdivision-delimiting sequence.
Skips over nested holes.

Returns nil if it found nothing before the LIMIT.

Returns (t start end) if it found a subdivision-delimiting sequence
from START to END, and moves point to END.

Returns (nil start end) if it found a hole-ending sequence from START to
END, and moves point to END."
  (let ((found nil)
        (nesting 0))
    (while
        (and (setq found (re-search-forward "\\(⁇[[:digit:]]+\\)?\\(¿\\)\\|\\(!\\|\\(ʔ\\)\\)" limit t))
             (progn
               (cond
                ((match-string 2)     ; ¿
                 (setq nesting (+ nesting 1)))
                ((match-string 4)     ; ʔ
                 (setq nesting (- nesting 1))))
               ;; If nesting > 0, we are still inside a nested hole, and we keep going.
               ;; If nesting = -1, we hit the overall ending ʔ, in which case we stop.
               ;; If nesting = 0, we might have hit a top-level !, in which case we stop,
               ;;   or we might have just exited a nested hole, in which case we *don't* stop yet.
               (or (> nesting 0)
                   (and (= nesting 0) (match-string 4))))))
    (if found
        (list (= nesting 0) (match-beginning 3) (match-end 3))
      nil)))

(defun narya-highlight-holes (limit)
  "Font-lock search function to find holes.
Highlights their starting, ending, and subdivider sequences as
subexpressions 1 and 3 (with 3 sometimes missing), and their interiors
as subexpression 2.  Skips across nested holes, including their
subdivisions."
  ;; First find the next hole-beginning or subdivision-delimiting
  ;; sequence, assuming that it is not nested inside any other hole.
  (when (re-search-forward "\\(⁇[[:digit:]]+\\)?¿\\|!" limit t)
    (let ((start-start (set-marker (make-marker) (match-beginning 0)))
          (start-end (set-marker (make-marker) (match-end 0))))
      ;; Now look for the next hole-ending or subdivision-delimiting
      ;; sequence, skipping over nested holes.
      (let ((data (narya-next-hole-subdivision limit)))
        (if data
            (let ((end-start (set-marker (make-marker) (nth 1 data)))
                  (end-end (set-marker (make-marker) (nth 2 data))))
              (if (nth 0 data)
                  ;; We must have found a top-level !.
                  (progn
                    ;; Back across it so the next search will start there.
                    (goto-char end-start)
                    ;; Highlight the starting sequence, and the intermediate region as default, but not the !.
                    (set-match-data (list start-start end-start
                                          start-start start-end
                                          start-end end-start))
                    ;; Continue searching
                    t)
                ;; We must have found the ending ʔ.  Highlight it too.
                (set-match-data (list start-start end-end
                                      start-start start-end
                                      start-end end-start
                                      end-start end-end))
                ;; Continue searching to find more holes.
                t))
          ;; The hole drops off the end of the fontification region.  Just highlight the start sequence and the intermediate region.
          (set-match-data (list start-start (point-marker)
                                start-start start-end
                                start-end (point-marker)))
          ;; Stop searching, we've found all the holes
          nil)))))

;; Yes, the face names here actually have to be *quoted*, even though the entire list is *also* quoted.  I think font lock expects an expression there that it *evaluates*, and while some of the faces are also variables whose value is the face of the same name, some aren't.  So we ought to quote them all.
;; Many of these regexps are simplistic and will get confused if there are comments interspersed.  They also depend on font-lock-multiline being set to t.
(defconst narya-core-font-lock-keywords
  `(
    ;; Holes with contents
    (narya-highlight-holes
     (1 'font-lock-warning-face)
     (2 'default t)
     (3 'font-lock-warning-face nil t))

    (,narya-commands . 'font-lock-keyword-face)
    ("\\_<\\(Type\\|let\\|rec\\|in\\|and\\|match\\|return\\|sig\\|data\\|codata\\|Id\\|refl\\|sym\\)\\_>" 1 'font-lock-builtin-face)

    ;; Constants being defined.
    ("\\_<\\(axiom\\|def\\|and\\)[[:space:]\n]+\\([[:word:]_.']+\\)\\_>" 2 'font-lock-function-name-face)

    ;; Fields/methods
    ("\\_<\\.[[:word:]_.']+\\_>" . 'font-lock-property-name-face)
    ;; Field names in sig definitions.
    ("\\(\\_<sig[[:space:]\n]*(\\|,\\)[[:space:]\n]*\\([[:word:]_.']+\\)[[:space:]\n]*:" 2 'font-lock-property-name-face)
    ;; Field names in tuples.
    ("[(,][[:space:]\n]*\\([[:word:]_.']+\\)[[:space:]]*\\(≔\\|:=\\)" 1 'font-lock-property-name-face)

    ;; Constructors
    ("\\_<\\([[:word:]_.']+\\.\\)\\_>" . 'font-lock-constant-face)
    ("\\_<\\([[:digit:]]+\\)\\_>" . 'font-lock-number-face) ; these are really like constructors.
    ("\\_<\\([[:digit:]][[:digit:].]+[[:digit:]]\\)\\_>" . 'font-lock-number-face) ; decimal numbers

    ;; Variables bound by let-bindings
    ("\\_<\\(let[[:space:]\n]+rec\\|let\\|and\\)[[:space:]\n]+\\([[:word:]_']+\\)\\_>" 2 'font-lock-variable-name-face)
    ;; Variables bound by abstractions
    (narya-highlight-abstractions 1 'font-lock-variable-name-face)
    ;; Self variables in codata declarations.
    ("[[|][[:space:]\n]*\\([[:word:]_']+\\)[[:space:]\n]*\\(↦\\||->\\)" 1 'font-lock-variable-name-face)
    ;; Variables bound in telescopes (parameters or dependent-function arguments)
    ("([[:space:]\n]*\\([[:word:]_'[:space:]\n]+\\):" 1 'font-lock-variable-name-face)

    ;; Symbols
    ("[][(){}]" . 'font-lock-bracket-face)
    ("[→↦⤇≔~@#$%&*/=+\\|,<>:;-]" . 'font-lock-operator-face)

    ;; Holes without contents
    ("\\?" 0 'font-lock-warning-face)

    ;; "keywords" used only in import statements.  We put them last so they don't prevent other things.
    ("\\_<\\(all\\|id\\|none\\|only\\|except\\|renaming\\|seq\\|union\\)\\_>" . 'font-lock-builtin-face)
    )
  "Narya core language font-lock keywords")

(defconst narya-script-font-lock-keywords
  (append narya-core-font-lock-keywords))

(defconst narya-mode-syntax-table-entries
  (append
   ;; By default, everything can be part of a word.
   `((128 . ,(max-char)) "w")
   ;; Comments.  This is kind of black magic to deal with both block and line comments.
   '(?\` "< 23b")
   '(?\n "> b")
   '(?\{ "(}1nb")
   '(?\} "){4nb")
   ;; Whitespace
   '(?  " ")
   '(?\t " ")
   ;; Symbol constituents, which for Narya means things that can appear in identifiers like "namespace.function" or "x.01" or "long_function_name" or "f''", but which are not part of "words".  Thus an identifier can consist of multiple "words" which are moved through separately by commands like forwards-word.  That means that we can't use \< and \> in regexps to detect the beginning or end of identifiers; we have to use \_< and \_> instead.
   '(?. "_")
   '(?_ "_")
   '(?' "_")
   ;; Parentheses
   '(?( "(")
   '(?[ "(")
   '(?) ")")
   '(?] ")")
   ;; Hole delimiters are treated as parenthesis-like
   '(?¿ "(")
   '(?ʔ ")")
   ;; Quotes
   '(?\" "\"")
   ;; Punctuation: characters that can appear in operators (and hence mark the beginning or end of a symbol).
   '(?~ ".")
   '(?@ ".")
   '(?# ".")
   '(?$ ".")
   '(?% ".")
   '(?& ".")
   '(?* ".")
   '(?/ ".")
   '(?= ".")
   '(?+ ".")
   '(?\ ".")
   '(?| ".")
   '(?, ".")
   '(?< ".")
   '(?> ".")
   '(?: ".")
   '(?\;  ".")
   '(?- ".")
   ;; Single-character operators are also punctuation
   '(?≔ ".")
   '(?⩴ ".")
   '(?→ ".")
   '(?↦ ".")
   '(?⤇ ".")
   '(?… ".")
   '(?⩲ ".")
   ;; As are hole characters
   '(?! ".")
   '(?\? ".")
   '(?⁇ ".")
   ))

(defvar narya-mode-syntax-table-for-terms
  (let ((table (make-syntax-table))
        (entries narya-mode-syntax-table-entries))
    (while entries
      (modify-syntax-entry (pop entries) (pop entries) table))
    table)
  "A syntax table built from `narya-mode-syntax-table-entries'.
Used for examining Narya terms in temporary buffers, which are not in
Narya mode and hence don't have its syntax table.")

(defconst narya-atomic-term-regexp
  (concat
   ;; An identifier is a maximal run of characters that are not
   ;; whitespace, comment-starters, hole characters, ASCII symbols, or
   ;; single-character operators (including the superscript
   ;; parentheses).  Dots are allowed, since they only separate the
   ;; pieces of an identifier (or mark a constructor or a field).
   "\\`[^][(){}~!@#$%&*/=+|,<>:;^`?⁇¿ʔ↦⤇→⇒≔⩴⩲…⁽⁾ \t\n\r"
   ;; Unicode tag characters are special too.
   (string #xE0020) "-" (string #xE007F)
   "-]+\\'")
  "Regexp matching a Narya term that consists of a single identifier.
Such a term never needs to be parenthesized to be used as an argument.
This is an approximation of the Narya lexer, which is what decides where
one identifier ends and the next token begins.")

(defun narya-delimited-term-p (term)
  "Whether TERM is entirely enclosed in one matching pair of brackets.
The brackets can be parentheses, square brackets, or curly braces."
  (and (string-match-p "\\`[[({]" term)
       (with-temp-buffer
         (set-syntax-table narya-mode-syntax-table-for-terms)
         (insert term)
         (let ((end (ignore-errors (scan-sexps (point-min) 1))))
           (and end (= end (point-max)))))))

(defun narya-term-needs-parentheses-p (term)
  "Whether TERM must be parenthesized to be used as an argument.
This is a pure-elisp approximation of what Narya itself would say: we
answer no if TERM is a single identifier, or if it is already enclosed in
a matching pair of parentheses, brackets, or braces, and yes otherwise.
Thus we may parenthesize a term unnecessarily, but the result should
always be correct."
  (let ((term (string-trim term)))
    (not (or (string-match-p narya-atomic-term-regexp term)
             (narya-delimited-term-p term)))))

(defun narya-parenthesize-term (term)
  "Parenthesize TERM if necessary for it to be used as an argument."
  (let ((term (string-trim term)))
    (if (narya-term-needs-parentheses-p term)
        (concat "(" term ")")
      term)))

(provide 'narya-syntax)

;; Local Variables:
;; indent-tabs-mode: nil
;; End:
