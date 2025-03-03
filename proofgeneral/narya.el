;;;narya.el --- Proof General instance for Narya

(eval-and-compile
  (require 'proof-site)
  (require 'pg-custom)
  (require 'proof)
  (require 'proof-config)
  (require 'proof-easy-config)
  (proof-ready-for-assistant 'narya))        ;; compilation for narya

(require 'narya-syntax)
(require 'font-lock)
(require 'ansi-color)

(defun narya-script-preprocess (file start end cmd)
  "Add a formfeed at the end of a command, as a delimiter."
  (list (concat cmd "\n\x0C\n")))

(defvar narya-hole-overlays nil
  "List of overlays marking the locations of open holes")
  
(defun narya-delete-all-holes ()
  "Delete all hole overlays and reset `narya-hole-overlays' to nil."
  (mapc #'delete-overlay narya-hole-overlays)
  (setq narya-hole-overlays nil))

(add-hook 'proof-shell-kill-function-hooks #'narya-delete-all-holes)

(defface narya-hole-face '((t . (:background "SlateGray4" :foreground "white" :weight bold)))
  "Face used for open holes in Narya")

(defvar narya-pending-hole-positions nil
  "Temporary storage for hole positions when executing commands invisibly.")

(defun narya-create-hole-overlays (start-position relative-positions)
  "Create overlays for holes given a starting position and a list of relative positions.
Each entry in RELATIVE-POSITIONS should be a list of the form (START-OFFSET END-OFFSET HOLE-ID)."
  (dolist (pos relative-positions)
    (let* ((start-offset (nth 0 pos))
           (end-offset (nth 1 pos))
           (hole-id (nth 2 pos))
           ;; Adjust offsets relative to the starting position
           (char-start (byte-to-position (+ start-position start-offset)))
           (char-end (byte-to-position (+ start-position end-offset))))
      ;; Create overlay only if positions are valid
      (when (and char-start char-end)
        (let ((ovl (make-overlay char-start char-end nil nil nil)))
          (overlay-put ovl 'narya-hole hole-id)
          (overlay-put ovl 'face 'narya-hole-face)
          (push ovl narya-hole-overlays))))))

(defun narya-skip-comments-backwards ()
  "Skip backwards to the last non-whitespace, non-comment character."
  (let ((continue t)
	(line-comment nil)
	(block-comment nil))
    (while (and continue (> (point) (point-min)))
      (setq block-comment (numberp (nth 4 (syntax-ppss)))
	    line-comment (eq (nth 4 (syntax-ppss)) t))
      (backward-char 1)
      ;; Skip all whitespace and comments
      (unless (or (looking-at "[ \t\n]")
		  (nth 4 (syntax-ppss)))
	;; If our new character is not a whitespace or a comment, we're going to stop unless it's the beginning of a comment.
	(cond
	 (block-comment (backward-char 1))
	 (line-comment)
	 (t (setq continue nil))))))
  ;; Move back across the non-whitespace, non-comment character we found
  (forward-char 1))

(defun narya-parse-cmdstart ()
  "Parse a complete command, not including any comments that follow it."
  (let ((parsed (proof-script-generic-parse-cmdstart)))
    (when (eq parsed 'cmd)
      (narya-skip-comments-backwards))
    parsed))

(defun narya-handle-output (cmd string)
  "Parse and handle Narya's output.
If called with an invisible command, store hole data in a global
variable instead of creating overlays immediately. Otherwise,
create overlays for new holes.

This function also performs part of `proof-shell-handle-delayed-output`'s
role, updating `proof-shell-last-output-kind` to avoid duplicated output
handling in Proof General."
  ;; Retrieve action information from `proof-action-list`.
  (let ((span (caar proof-action-list))
        (cmd (nth 1 (car proof-action-list)))
        (flags (nth 3 (car proof-action-list)))
        ;; Variables to mark positions in `string` as we parse.
        (rstart 0) (rend 0) (gstart 0) (gend 0) (dpos 0)
        ;; Temporary storage for hole data.
        (parsed-hole-data nil)
        (error-found nil))
    ;; Check for errors in the output first.
    (when (string-match proof-shell-error-regexp string)
      (setq error-found t
            proof-shell-last-output-kind 'error))
    ;; If no errors, proceed with normal processing.
    (unless error-found
      ;; Check for the goals marker in the output, setting positions to slice
      ;; out goals and data sections.
      (when (string-match "\x0C\\[goals\\]\x0C\n" string rstart)
        (setq rend (match-beginning 0)
              gstart (match-end 0))
        (string-match "\x0C\\[data\\]\x0C\n" string gstart)
        (setq gend (match-beginning 0)
              dpos (match-end 0))
        ;; Parse hole data from the data section
        (setq parsed-hole-data
              (cl-loop while (string-match "^\\([0-9]+\\) \\([0-9]+\\) \\([0-9]+\\).*\n" string dpos)
                       collect (let* ((hole (string-to-number (match-string 1 string)))
                                      (hstart-offset (string-to-number (match-string 2 string)))
                                      (hend-offset (string-to-number (match-string 3 string))))
                                 (setq dpos (match-end 0))
                                 (list hstart-offset hend-offset hole))))
        ;; Handle parsed hole data based on the visibility of the command
        (if (member 'invisible flags)
            ;; For invisible commands, store the parsed data globally
            (setq narya-pending-hole-positions parsed-hole-data)
          ;; For visible commands, create overlays directly
          (when span ;; Only proceed if `span` is non-nil
            (proof-with-script-buffer
             (let ((bpos (position-bytes (save-excursion
                                           (goto-char (overlay-start span))
                                           (skip-chars-forward " \t\n")
                                           (point)))))
               (narya-create-hole-overlays bpos parsed-hole-data))))))
      ;; Handle the goals section output if `proof-shell-exec-loop` is active
      (when (proof-shell-exec-loop)
        (setq proof-shell-last-goals-output (substring string gstart gend))
        (proof-shell-display-output-as-response flags (substring string rstart rend))
        (unless (memq 'no-goals-display flags)
          (pg-goals-display proof-shell-last-goals-output t)))
      ;; Update output kind to avoid redundant handling by `proof-shell-handle-delayed-output`
      (setq proof-shell-last-output-kind 'goals))
    ;; Optionally handle proof tree output
    (when proof-tree-external-display
      (proof-tree-handle-delayed-output old-proof-marker cmd flags span))))

(defun narya-delete-undone-holes ()
  "Delete overlays for holes that are (now) outside the processed region."
  (let ((pend (proof-unprocessed-begin)))
    (setq narya-hole-overlays
	  (seq-filter
	   (lambda (ovl)
	     (if (and (overlay-start ovl) (< (overlay-start ovl) pend))
		 t
	       (delete-overlay ovl)
	       nil))
	   narya-hole-overlays))))

;; Use Asai's ANSI coloring of error messages
(defun narya-insert-and-color-text (&rest args)
  (let ((start (point)))
    (apply 'insert args)
    (ansi-color-apply-on-region start (point))))

;; Easy configuration
(proof-easy-config 
 ;; The two names below should be the same as in proof-site.el
 'narya "Narya"      
 proof-prog-name                       "narya"
 narya-prog-args                       `("-proofgeneral")
 proof-toolbar-enable                  t
 
 ;; when not nil, a space is added to the beginning of the previous line at each new line transition.
 narya-script-indent                   nil  
 
 ;; Syntax and font-lock
 proof-script-syntax-table-entries     narya-mode-syntax-table-entries
 proof-script-font-lock-keywords       narya-script-font-lock-keywords
 proof-goals-font-lock-keywords        narya-script-font-lock-keywords
 proof-response-font-lock-keywords     narya-script-font-lock-keywords
 
 ;; Comment syntax
 proof-script-comment-start            "`"       ;; For line comments
 proof-script-comment-end              ""        ;; For line comments
 ;; So far, it appears that it really does work for these two to be separately disjunctive.
 proof-script-comment-start-regexp     "{`\\|`"  ;; Matches either block or line comment start
 proof-script-comment-end-regexp       "`}\\|\n" ;; Matches either block comment end or newline for line comments
 comment-quote-nested                  nil			 ;; Nested comments are allowed
 
 ;; Commands
 proof-script-command-start-regexp     narya-commands
 proof-script-parse-function           'narya-parse-cmdstart

 ;; Undo
 proof-non-undoables-regexp            "undo"
 proof-ignore-for-undo-count           "echo\\|synth\\|show\\|undo"
 proof-undo-n-times-cmd                "undo %s\n\x0C" ;; has to end with a formfeed to terminate a PG-mode command
 proof-state-preserving-p              'narya-state-preserving-p
 ;; The difference between proof-count-undos-fn and proof-find-and-forget-fn seems to be that the former is called iff staying inside a single proof.  However, as far as I can see, for Narya the default value of the former also works for the latter.
 proof-find-and-forget-fn              'proof-generic-count-undos

 ;; multiple file management
 proof-no-fully-processed-buffer       t
 ;; TODO: more?

 ;; Delimiting input commands
 ;; Narya allows internal CR in interactive command, and has line-comments ended by CR that could appear internally to a command, so we *have* to leave the CRs in place.  The preprocessing function adds a formfeed as an end-of-command marker instead.
 proof-shell-strip-crs-from-input      nil
 proof-script-preprocess               'narya-script-preprocess
 ;; This won't get used for parsing commands since proof-script-command-start-regexp takes priority, but it will get added automatically to the end of minibuffer-read commands.
 proof-terminal-string                 "\n\x0C\n"
 proof-shell-auto-terminate-commands   t
 ;; Detect holes for goals buffer
 ;; proof-shell-start-goals-regexp        "\x0C\\[holes\\]\x0C\n\\(\\)"
 ;; proof-shell-end-goals-regexp          "\x0C\\[data\\]\x0C\n"
 proof-shell-handle-output-system-specific 'narya-handle-output
 ;; We don't have "save" commands yet, so silence the warning about their absence.
 proof-save-command-regexp             ""
 proof-really-save-command-p           (lambda (span cmd) nil)

 ;; Silencing unnecessary output (TODO)
                                        ;proof-shell-start-silent-cmd          ""
                                        ;proof-shell-stop-silent-cmd           ""

 ;; Parsing output
 ;; The PG-mode prompt doesn't need to be human-readable or writeable, so we use formfeed characters to ensure no accidental collisions with ordinary output.
 proof-shell-annotated-prompt-regexp   "\x0C\\[narya\\]\x0C"
 proof-shell-error-regexp              "^ ￫ .*\\(error\\|bug\\)" ; the .* skips the ANSI color codes
 proof-shell-truncate-before-error     nil
 proof-script-color-error-messages     nil
 pg-insert-text-function               'narya-insert-and-color-text

 ;; interactive proof (TODO)
                                        ;proof-shell-proof-completed-regexp    ""
                                        ;proof-shell-start-goals-regexp        ""
                                        ;proof-shell-end-goals-regexp          ""

 ;; Settings for generic user-level commands
 proof-assistant-home-page             "https://github.com/mikeshulman/narya/"
 )

;; The Emacs comment functions are a bit weird and inconsistent.
;; comment-dwim (M-;) checks if the line is empty.
;; - if the line is empty:
;;   - if comment-insert-comment-function is non-nil, it calls that.
;;   - otherwise, it directly inserts comment-start and comment-end.
;; - if the line is not empty, it calls comment-indent.
;; comment-indent *also* checks if comment-insert-comment-function is non-nil.
;; - if so, it calls it.
;; - if not, it *also* checks whether the line is empty.
;;   - if so, it inserts block-comment-start and block-comment end.
;;   - if not, it inserts comment-start and comment-end.
;; Thus, to avoid infinite loops and get block comments exactly on empty lines, we define our value of comment-insert-comment-function as follows:
(defun narya-insert-comment ()
  ;; If the line is empty,
  (if (save-excursion (beginning-of-line) (looking-at "\\s-*$"))
      ;; Directly insert block-comment-start and block-comment-end, like comment-dwim does but using the block ones.
      (progn
	(indent-according-to-mode)
        (insert (comment-padright block-comment-start nil))
        (save-excursion
          (insert (comment-padleft block-comment-end nil))
          (indent-according-to-mode)))
    ;; Otherwise, call comment-indent, but dynamically unbinding comment-insert-comment-function so that we don't get called again in an infinite loop.
    (let ((comment-insert-comment-function nil))
      (comment-indent))))

;; Make commenting out regions use block comments.
(defun narya-comment-region (beg end &optional arg)
  (let ((comment-start block-comment-start)
	(comment-end block-comment-end)
	(comment-continue "")
	(comment-style 'extra-line))
    (comment-region-default beg end arg)))

(defun narya-mode-extra-config ()
  (set (make-local-variable 'block-comment-start) "{` ")
  (set (make-local-variable 'block-comment-end) " `}")
  (set (make-local-variable 'comment-insert-comment-function) 'narya-insert-comment)
  (set (make-local-variable 'comment-region-function) 'narya-comment-region)
  (add-hook 'proof-state-change-hook 'narya-delete-undone-holes))

(add-hook 'narya-mode-hook 'narya-mode-extra-config)

;; Interactive commands

(defun narya-previous-hole ()
  "Move point to the previous open hole, if any."
  (interactive)
  (let ((pos
	 (seq-reduce
	  (lambda (pos ovl)
	    (let ((opos (overlay-start ovl)))
	      (if (and (< opos (point))
		       (if pos (< pos opos) t))
		  opos
		pos)))
	  narya-hole-overlays
	  nil)))
    (if pos
	(goto-char pos)
      (message "No more holes."))))

(defun narya-next-hole ()
  "Move point to the next open hole, if any."
  (interactive)
  (let ((pos
	 (seq-reduce
	  (lambda (pos ovl)
	    (let ((opos (overlay-start ovl)))
	      (if (and (< (point) opos)
		       (if pos (< opos pos) t))
		  opos
		pos)))
	  narya-hole-overlays
	  nil)))
    (if pos
	(goto-char pos)
      (message "No more holes."))))

(defun narya-show-hole ()
  "Show the goal and context for the current open hole, if any."
  (interactive)
  (let ((n (get-char-property (point) 'narya-hole)))
    (if n
	(proof-shell-invisible-command (concat "show hole " (number-to-string n)))
      (message "Place the cursor in a hole to use this command."))))

(defun narya-show-all-holes ()
  "Show the goal and context for all open holes."
  (interactive)
  (proof-shell-invisible-command "show holes"))

(defun narya-solve-hole ()
  "Solve the current hole with a user-provided term, using any
pending hole data stored by `narya-handle-output`."
  (interactive)
  ;; Check for an overlay marking the current hole at point.
  (let ((hole-overlay (car (seq-filter (lambda (ovl)
                                         (overlay-get ovl 'narya-hole))
                                       (overlays-at (point)))))
        insert-start term-length byte-insert-start) ;; Declare insert-start and byte-insert-start
    ;; If no hole overlay is found, prompt the user to place the cursor on a hole.
    (if (not hole-overlay)
        (message "Place the cursor on a hole.")
      ;; Otherwise, proceed to solve the hole with a user-provided term.
      (let ((term (read-string "Enter the term to solve the hole: ")))
        ;; Send the solution command invisibly to the proof shell.
        (proof-shell-invisible-command
         (format "solve %d := %s" (overlay-get hole-overlay 'narya-hole) term) t)
        ;; Check for errors in the proof shell output.
        (if (eq proof-shell-last-output-kind 'error)
            (message "You entered an incorrect term.")
          ;; If no errors, insert the solution term at the hole position and update overlays.
          (let ((inhibit-read-only t))
            (setq insert-start (overlay-start hole-overlay)) ;; Store start position for later use
            (setq byte-insert-start (position-bytes insert-start)) ;; Get byte-based start position
            (goto-char insert-start)
	    ;; Insert the term and delete the hole.  We do it in this
	    ;; order so that if the hole is at the very end of the
	    ;; processed region, the inserted term will end up
	    ;; *inside* the processed region.
            (insert "(" term ")") ;; Use parentheses to guarantee correct parsing.
            (delete-region (point) (overlay-end hole-overlay))
            ;; Delete the overlay for the solved hole and update the hole list.
            (delete-overlay hole-overlay)
            (setq narya-hole-overlays (delq hole-overlay narya-hole-overlays))
            (message "Hole solved."))
          ;; Process any pending hole positions saved in `narya-handle-output`.
          (when narya-pending-hole-positions
            ;; Use the helper function to create overlays for new holes.
            (narya-create-hole-overlays (+ byte-insert-start 1) narya-pending-hole-positions)) ;;adjust start-pos for added parenthesis
          ;; Clear the global pending hole data after processing.
          (setq narya-pending-hole-positions nil))))))

(keymap-set narya-mode-map "C-c C-SPC" 'narya-solve-hole)

(defun narya-echo (term)
  "Normalize and display the value and type of a term."
  (interactive "sTerm to normalize: ")
  (proof-shell-invisible-command (concat "echo " term)))

(defun narya-synth (term)
  "Display the type of a term."
  (interactive "sTerm to synthesize: ")
  (proof-shell-invisible-command (concat "synth " term)))

(defvar narya-minibuffer-commands
  '("echo"
    "synth"
    "show hole"
    "show holes"
    "display style ≔ compact"
    "display style ≔ noncompact"
    "display chars ≔ unicode"
    "display chars ≔ ascii"))

(defun narya-minibuffer-cmd (cmd)
  "Wrapper around `proof-minibuffer-cmd' with completion for Narya commands."
  (interactive
   (list (completing-read
          "Command: " narya-minibuffer-commands nil nil
	  (and current-prefix-arg (region-active-p)
	       (concat
                " "
                (replace-regexp-in-string
	         "[ \t\n]+" " "
	         (buffer-substring (region-beginning) (region-end)))))
	  'proof-minibuffer-history nil t)))
  (proof-minibuffer-cmd cmd))

;; Proof General key bindings, with suggested Narya bindings marked
;; C-c C-a --> apply/refine in a hole
;; C-c C-b proof-process-buffer
;; C-c C-c proof-interrupt-process
;; C-c C-d proof-tree-external-display-toggle
;; C-c C-e
;; C-c C-f proof-find-theorems
;; C-c C-g
;; C-c C-h (help)
;; C-c TAB proof-query-identifier
;; C-c C-j --> next goal
;; C-c C-k --> previous goal
;; C-c C-l proof-layout-windows
;; C-c RET proof-goto-point
;; C-c C-n proof-assert-next-command-interactive
;; C-c C-o proof-display-some-buffers
;; C-c C-p proof-prf (show current proof state)
;; C-c C-q --> about/searchabout ("query")
;; C-c C-r proof-retract-buffer
;; C-c C-s proof-toggle-active-scripting
;; C-c C-t proof-ctxt (show current context)
;;         --> show current hole if any, focused proof if any
;; C-c C-u proof-undo-last-successful-command
;; C-c C-v proof-minibuffer-cmd
;;         --> narya-minibuffer-cmd (wrapped)
;; C-c C-w pg-response-clear-displays
;; C-c C-x proof-shell-exit
;; C-c C-y --> case split (Y looks like a split)
;; C-c C-z proof-frob-locked-end
;; C-c >   proof-autosend-toggle
;; C-c <
;; C-c {
;; C-c }
;; C-c :   --> synthesize type (: is typing), incl context and goal in a hole
;; C-c ;   --> normalize (echo), incl context and goal in a hole
;; C-c . (also minor modes)
;; C-c , (also minor modes)
;; C-c 0
;; C-c 1
;; C-c 2
;; C-c 3
;; C-c 4
;; C-c 5
;; C-c 6
;; C-c 7
;; C-c 8
;; C-c 9
;; C-c `   proof-next-error
;; C-c C-. proof-goto-end-of-locked
;; C-c C-,
;; C-c C-; pg-insert-last-output-as-comment
;; C-c C-:
;; C-c ?   (help)
;; C-c C-? --> show all goals
;; C-c C-SPC --> fill hole

;; For comparison, Agda global bindings
;; C-c C-? show all goals
;; C-c C-b previous goal
;; C-c C-d deduce (synthesize) type
;; C-c C-f next goal
;; C-c C-n compute normal form
;; C-c C-z search definitions in scope

;; For comparison, Agda hole bindings
;; C-c C-, goal type and context
;; C-c C-. goal type and context, plus type of current term
;; C-c C-SPC fill hole
;; C-c C-a automatic proof search
;; C-c C-c case split
;; C-c C-d deduce type of current term
;; C-c C-e context (environment)
;; C-c C-h create helper function
;; C-c C-m normalize and fill
;; C-c C-n normalize current term
;; C-c C-r refine/apply
;; C-c C-t show goal type
;; C-c C-w why in scope

(keymap-set narya-mode-map "C-c C-t" 'narya-show-hole)
(keymap-set narya-mode-map "C-c C-?" 'narya-show-all-holes)
(keymap-set narya-mode-map "C-c C-j" 'narya-next-hole)
(keymap-set narya-mode-map "C-c C-k" 'narya-previous-hole)
(keymap-set narya-mode-map "C-c ;" 'narya-echo)
(keymap-set narya-mode-map "C-c :" 'narya-synth)
(keymap-set narya-mode-map "C-c C-v" 'narya-minibuffer-cmd)

(provide 'narya)

;;; narya.el ends here

;; Local Variables:
;; indent-tabs-mode: nil
;; End:
