;;; narya-pg-tests.el --- Tests for the Narya ProofGeneral mode  -*- lexical-binding: t -*-

;; Run by run-ert.sh, which sets NARYA_PG_DIR to the directory containing
;; narya.el and puts the narya executable being tested first on the PATH.
;;
;; Every test is skipped if ProofGeneral can't be found.  The tests that
;; start a narya process do everything in a temporary directory, and never
;; save the buffers they edit.

(require 'ert)
(require 'cl-lib)
(require 'subr-x)
(require 'seq)

;;; Loading ProofGeneral and the Narya mode

(setq proof-splash-enable nil
      create-lockfiles nil
      make-backup-files nil
      auto-save-default nil)

(defvar narya-pg-test-have-pg
  (or (require 'proof-site nil t)
      ;; ProofGeneral installed from ELPA/MELPA isn't on the load-path until
      ;; the package system is initialized.
      (progn
        (package-initialize)
        (require 'proof-site nil t)))
  "Non-nil if ProofGeneral could be loaded.")

;; Load the Narya mode from NARYA_PG_DIR explicitly, so that we test those
;; files and not any copy (or symlink) installed in ProofGeneral's own "narya"
;; subdirectory.  Errors here are not caught: if ProofGeneral is present but
;; the Narya mode fails to load, that should be a failure, not a skip.
(when narya-pg-test-have-pg
  (let ((dir (or (getenv "NARYA_PG_DIR")
                 (error "NARYA_PG_DIR is not set"))))
    (unless (assq 'narya proof-assistant-table)
      (push '(narya "Narya" "ny" nil (".nyo")) proof-assistant-table))
    (proof-ready-for-assistant 'narya)
    (push dir load-path)
    (load (expand-file-name "narya-syntax.el" dir) nil t)
    (load (expand-file-name "narya.el" dir) nil t)))

(defmacro narya-pg-test-with-buffer (contents &rest body)
  "Run BODY in a `narya-mode' buffer visiting a new temporary file with CONTENTS.
Afterwards, kill the narya process if there is one, and delete the file."
  (declare (indent 1))
  `(progn
     (skip-unless narya-pg-test-have-pg)
     (let* ((dir (make-temp-file "narya-pg-test" t))
            (file (expand-file-name "test.ny" dir)))
       (unwind-protect
           (progn
             (with-temp-file file (insert ,contents))
             (with-current-buffer (find-file-noselect file)
               (unwind-protect
                   (progn
                     (unless (derived-mode-p 'narya-mode) (narya-mode))
                     ,@body)
                 (when (proof-shell-live-buffer) (proof-shell-exit t))
                 (set-buffer-modified-p nil)
                 (kill-buffer))))
         (delete-directory dir t)))))

;;; Splitting a buffer into commands (no narya process)

(defun narya-pg-test-segments ()
  "Split the current buffer into spans as ProofGeneral would.
Return a list of (cmd TEXT) and (comment) elements, in buffer order."
  (mapcar (lambda (seg)
            (if (eq (car seg) 'cmd) (list 'cmd (nth 1 seg)) (list (car seg))))
          (reverse (proof-segment-up-to-parser (point-max)))))

(ert-deftest narya-pg-segments-keywords-in-comments ()
  "Command keywords inside comments don't start new commands."
  (narya-pg-test-with-buffer
      "axiom A : Type

{` Here we def ine the identity; see the end. `}
def f : A → A ≔ x ↦ x

{` Mutual with g; nothing to say about it, def, end. `}

and g : A → A ≔ x ↦ x

` a line comment mentioning def and end
axiom a : A
"
    (should
     (equal (narya-pg-test-segments)
            '((cmd "axiom A : Type")
              (comment)
              (cmd "def f : A → A ≔ x ↦ x

{` Mutual with g; nothing to say about it, def, end. `}

and g : A → A ≔ x ↦ x")
              (comment)
              (cmd "axiom a : A"))))))

(ert-deftest narya-pg-segments-about ()
  "An \"about\" command is a command of its own."
  (narya-pg-test-with-buffer "axiom A : Type\n\nabout A\n\naxiom a : A\n"
    (should (equal (narya-pg-test-segments)
                   '((cmd "axiom A : Type") (cmd "about A") (cmd "axiom a : A"))))))

;;; Classifying commands (no narya process)

(ert-deftest narya-pg-ignore-for-undo-count ()
  "Only commands that start with a query keyword are left out of undo counts."
  (narya-pg-test-with-buffer ""
    (dolist (cmd '("echo a" "synth a" "about f" "\n  echo a"))
      (should (proof-stringfn-match proof-ignore-for-undo-count cmd)))
    (dolist (cmd '("def f : A ≔ {` I thought about it `} a"
                   "def echoes : A ≔ a"
                   "axiom undone : A"
                   "def f : A ≔ a\n\nand g : B ≔ synth"))
      (should-not (proof-stringfn-match proof-ignore-for-undo-count cmd)))))

(ert-deftest narya-pg-state-preserving ()
  "Only commands that start with a query keyword are state-preserving."
  (narya-pg-test-with-buffer ""
    (dolist (cmd '("echo a" "synth a" "about f" "show holes" "display chars"))
      (should (funcall proof-state-preserving-p cmd)))
    (dolist (cmd '("def f : A ≔ {` show me `} a" "undo 1" "def shown : A ≔ a"))
      (should-not (funcall proof-state-preserving-p cmd)))))

;;; Processing and retracting with a real narya process

(defvar narya-pg-test-sent nil
  "The commands sent to narya so far, most recent first.")

(defun narya-pg-test-record-sent (strings &rest _)
  "Record STRINGS, the argument of `proof-shell-insert', in `narya-pg-test-sent'."
  (let ((str (if (listp strings) (apply #'concat strings) strings)))
    (push (string-trim str "[ \t\n\f]+" "[ \t\n\f]+") narya-pg-test-sent)))

(advice-add 'proof-shell-insert :before #'narya-pg-test-record-sent)

(defun narya-pg-test-take-sent ()
  "Return the commands sent to narya since the last call, in order.
Omit the \"chdir\" commands that ProofGeneral sends on its own."
  (prog1 (seq-remove (lambda (s) (string-prefix-p "chdir " s))
                     (reverse narya-pg-test-sent))
    (setq narya-pg-test-sent nil)))

(defun narya-pg-test-wait ()
  "Wait until narya has finished processing everything queued."
  (let ((deadline (+ (float-time) 120)))
    (while (or proof-shell-busy proof-action-list)
      (when (> (float-time) deadline)
        (error "Timed out waiting for narya"))
      (accept-process-output nil 0.1))))

(defun narya-pg-test-response ()
  "Return the contents of the response buffer."
  (with-current-buffer proof-response-buffer
    (buffer-substring-no-properties (point-min) (point-max))))

(defun narya-pg-test-process ()
  "Process the whole buffer and wait for it to finish."
  (setq narya-pg-test-sent nil)
  (proof-process-buffer)
  (narya-pg-test-wait))

(defun narya-pg-test-retract-to (str)
  "Retract to the beginning of the line containing the first occurrence of STR.
If STR is nil, retract the whole buffer."
  (setq narya-pg-test-sent nil)
  (goto-char (point-min))
  (when str
    (search-forward str)
    (beginning-of-line))
  (proof-retract-until-point)
  (narya-pg-test-wait))

(ert-deftest narya-pg-undo-counts ()
  "Retracting sends the right number of undos.
Commands with keywords in comments must count as one command each, and
\"about\" commands mustn't be counted."
  (narya-pg-test-with-buffer
      "axiom A : Type

def f : A → A ≔ x ↦ x

{` Mutual with g; nothing to say about it, def, end. `}

and g : A → A ≔ x ↦ x

about A

axiom a : A
"
    (narya-pg-test-process)
    (should (equal (narya-pg-test-take-sent)
                   '("axiom A : Type"
                     "def f : A → A ≔ x ↦ x

{` Mutual with g; nothing to say about it, def, end. `}

and g : A → A ≔ x ↦ x"
                     "about A"
                     "axiom a : A")))
    (should (string-match-p "axiom a assumed" (narya-pg-test-response)))
    (narya-pg-test-retract-to "about A")
    (should (equal (narya-pg-test-take-sent) '("undo 1")))
    (narya-pg-test-retract-to nil)
    (should (equal (narya-pg-test-take-sent) '("undo 2")))))

(ert-deftest narya-pg-undo-removes-holes ()
  "Retracting and reprocessing a mutual definition with a hole leaves one hole.
This used to leave two, because the word \"about\" in a comment made
ProofGeneral think the definition was a query command that needed no undo."
  (narya-pg-test-with-buffer
      "axiom A : Type

axiom a : A

def f : A ≔ ?

{` Nothing to say about g. `}

and g : A ≔ a
"
    (narya-pg-test-process)
    (should (string-match-p "there is 1 open hole" (narya-pg-test-response)))
    (narya-pg-test-retract-to "def f")
    (should (equal (narya-pg-test-take-sent) '("undo 1")))
    (narya-pg-test-process)
    (let ((response (narya-pg-test-response)))
      (should-not (string-match-p "redefining" response))
      (should (string-match-p "there is 1 open hole" response)))))

;;; narya-pg-tests.el ends here
