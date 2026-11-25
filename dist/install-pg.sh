#!/usr/bin/env bash

echo -n "Checking for Narya..."

if command -v narya >/dev/null 2>&1
then
    echo "Found."
else
    if [ -e ../lib/core/check.ml ]
    then
        echo "Failed."
        echo
        echo "I can't find narya in your PATH."
        echo "Please build and install it, then run this script again."
        echo "If installing with opam/dune, make sure that you ran both commands:"
        echo
        echo "dune build @install"
        echo "dune install"
        echo
        echo "If you are running Narya from Nix without installing it locally, make"
        echo "a shell script wrapper around it called 'narya' and put it in your PATH."
        echo
        echo "If you did those and it still doesn't work, please open an issue at"
        echo "https://github.com/gwaithimirdain/narya/issues."
        exit 1
    else
        echo "Failed."
        echo
        echo "I can't find narya in your PATH."
        echo "Please copy it to a directory such as $HOME/bin and make sure that"
        echo "that directory is in your PATH, then run this script again."
        echo "For example, you could start with the following commands:"
        echo
        echo "mkdir -p ~/bin"
        echo "cp narya ~/bin"
        echo
        echo "If that still doesn't work, you may need to add $HOME/bin to your PATH.  Try this:"
        echo
        echo 'echo export PATH="\$HOME/bin:\$PATH" >>~/.bashrc'
        echo
        echo "If that still doesn't work, please open an issue at"
        echo "https://github.com/gwaithimirdain/narya/issues."
        exit 1
    fi
fi

echo -n "Checking for Emacs..."

if command -v emacs >/dev/null 2>&1
then
    echo "Found."
else
    echo "Failed."
    echo
    echo "I can't find emacs in your PATH."
    echo "Please install Emacs, then run this script again."
    echo "If you are having trouble, you can open an issue at"
    echo "https://github.com/gwaithimirdain/narya/issues."
    exit 1
fi

echo -n "Checking whether Emacs can find Narya..."

EXEC_PATH_FROM_SHELL=false

if emacs -Q -batch --eval='(call-process "narya")' >/dev/null 2>&1
then
    echo "Found."
else
    echo "Failed."
    echo "Trying to fix the problem by installing exec-path-from-shell..."
    TEMPINIT=$(mktemp)
    cat >"$TEMPINIT" <<EOF
(require 'package)
(setq package-archives '(("melpa" . "https://melpa.org/packages/")
                         ("gnu" . "https://elpa.gnu.org/packages/")))
(package-initialize)
(package-refresh-contents)
(package-install 'exec-path-from-shell)
(exec-path-from-shell-initialize)
(call-process "narya")
EOF
    if emacs -Q --batch -l "$TEMPINIT"
    then
        echo "Succeeded."
        rm -f "$TEMPINIT"
        EXEC_PATH_FROM_SHELL=true
    else
        echo "Failed."
        echo
        echo "Your Emacs can't find Narya, and I don't know how to fix it."
        echo "Please open an issue at https://github.com/gwaithimirdain/narya/issues."
        rm -f "$TEMPINIT"
        exit 1
    fi
fi

echo -n "Checking for ProofGeneral..."

# Don't use -Q here, so that we also find a ProofGeneral installed in
# site-lisp, e.g. by a system package manager or Nix.
if emacs --batch --eval="(progn (require 'package) (package-initialize) (unless (locate-library \"proof-site\") (kill-emacs 1)))" >/dev/null 2>&1
then
    echo "Found."
else
    echo "Not found."
    echo "Installing ProofGeneral..."

    TEMPINIT=$(mktemp)
    cat >"$TEMPINIT" <<EOF2
(require 'package)
(setq package-archives '(("melpa" . "https://melpa.org/packages/")
                         ("gnu" . "https://elpa.gnu.org/packages/")))
(package-initialize)
(package-refresh-contents)
(package-install 'proof-general)
EOF2

    if emacs -Q --batch -l "$TEMPINIT"
    then
        echo "Succeeded."
        rm -f "$TEMPINIT"
    else
        echo "Failed."
        echo
        echo "Please open an issue at https://github.com/gwaithimirdain/narya/issues."
        rm -f "$TEMPINIT"
        exit 1
    fi
fi

echo -n "Locating the Narya ProofGeneral files..."

if [ -e narya.el ]
then
    NARYA_EL_SRC=`pwd`
    NARYA_EL_LINK=false
    echo "Found."
elif [ -e ../proofgeneral/narya.el ]
then
    pushd ../proofgeneral >/dev/null
    NARYA_EL_SRC=`pwd`
    popd >/dev/null
    NARYA_EL_LINK=true
    echo "Found."
    echo "You appear to be running this script from the Narya source tree,"
    echo "so the elisp files will be symlinked rather than copied."
else
    echo "Failed."
    echo
    echo "I can't find narya.el."
    echo "Please run this script from the unpacked static distribution directory"
    echo "or from the dist/ directory in the Narya source tree."
    exit 1
fi

echo "Installing the Narya ProofGeneral mode as an Emacs package..."

# We install Narya's elisp files as a package in the directory of the Emacs
# package manager, so that Emacs activates it automatically at startup.  This
# works wherever ProofGeneral came from, since it doesn't modify ProofGeneral.
# We don't record a dependency on ProofGeneral in the package description,
# since the package manager would refuse to activate Narya if ProofGeneral
# was installed some other way (e.g. with Nix).
TEMPINIT=$(mktemp)
cat >"$TEMPINIT" <<'EOF2'
(require 'package)
(require 'lisp-mnt)
(let* ((src (file-name-as-directory (getenv "NARYA_EL_SRC")))
       (link (equal (getenv "NARYA_EL_LINK") "true"))
       (main (expand-file-name "narya.el" src))
       (version (lm-version main))
       (dir (expand-file-name (concat "narya-" version) package-user-dir)))
  ;; Remove files installed by older versions of this script, which put
  ;; Narya inside the ProofGeneral installation directory.  (Any leftover
  ;; entry for Narya in ProofGeneral's proof-site.el is ignored once that
  ;; directory is gone.)
  (dolist (old (file-expand-wildcards
                (expand-file-name "proof-general-*/narya" package-user-dir)))
    (princ (format "Removing old installation %s\n" old))
    (delete-directory old t))
  ;; Remove previously installed versions of the Narya package.
  (dolist (old (file-expand-wildcards (expand-file-name "narya-*" package-user-dir)))
    (when (file-exists-p (expand-file-name "narya-pkg.el" old))
      (princ (format "Removing old installation %s\n" old))
      (if (file-symlink-p old) (delete-file old) (delete-directory old t))))
  (make-directory dir t)
  (dolist (file (directory-files src t "\\.el\\'"))
    (let ((target (expand-file-name (file-name-nondirectory file) dir)))
      (if link
          (condition-case nil
              (make-symbolic-link file target)
            (error
             (princ (format "Couldn't symlink %s, copying it instead\n" file))
             (copy-file file target)))
        (copy-file file target))))
  (package-generate-description-file
   (package-desc-create :name 'narya
                        :version (version-to-list version)
                        :summary (lm-summary main))
   (expand-file-name "narya-pkg.el" dir))
  (package-generate-autoloads 'narya dir)
  (princ (format "Installed in %s\n" dir)))
EOF2

if NARYA_EL_SRC="$NARYA_EL_SRC" NARYA_EL_LINK="$NARYA_EL_LINK" emacs -Q --batch -l "$TEMPINIT"
then
    echo "Succeeded."
    rm -f "$TEMPINIT"
else
    echo "Failed."
    echo
    echo "Please open an issue at https://github.com/gwaithimirdain/narya/issues."
    rm -f "$TEMPINIT"
    exit 1
fi

echo -n "Checking that Emacs can start the Narya ProofGeneral mode..."

# As above, don't use -Q, so that ProofGeneral can be found anywhere.
if emacs --batch --eval="(progn (require 'package) (package-initialize) (with-temp-buffer (setq buffer-file-name \"test.ny\") (set-auto-mode) (unless (eq major-mode 'narya-mode) (kill-emacs 1))))" >/dev/null 2>&1
then
    echo "Succeeded."
else
    echo "Failed."
    echo
    echo "Something went wrong installing the Narya ProofGeneral mode."
    echo "Please open an issue at https://github.com/gwaithimirdain/narya/issues."
    exit 1
fi

echo "Narya ProofGeneral mode installed."

CTAGS=false

echo -n "Checking for Universal Ctags..."

if command -v ctags >/dev/null 2>&1
then
    if ctags --version | grep 'Universal Ctags' >/dev/null 2>&1
    then
        echo "Found."
        echo -n "Installing Narya ctags configuration..."

        if mkdir -p $HOME/.ctags.d
        then
            if [ -e narya.ctags ]
            then
                rm -f $HOME/.ctags.d/narya.ctags
                if cp -f narya.ctags $HOME/.ctags.d
                then
                    echo "Succeeded."
                    CTAGS=true
                else
                    echo "Failed."
                fi
            elif [ -e ../ctags/narya.ctags ]
            then
                echo
                echo "You appear to be running this script from the Narya source tree."
                echo -n "Symlinking the Narya .ctags file..."
                pushd ../ctags >/dev/null
                NARYA_CTAGS=`pwd`
                popd >/dev/null
                pushd $HOME/.ctags.d >/dev/null
                rm -f narya.ctags
                if ln -s $NARYA_CTAGS/narya.ctags .
                then
                    echo "Succeeded."
                    CTAGS=true
                else
                    echo "Failed."
                    echo -n "Trying to copy it instead..."
                    if cp $NARYA_CTAGS/narya.ctags .
                    then
                        echo "Succeeded."
                        CTAGS=true
                    else
                        echo "Failed."
                    fi
                fi
                popd >/dev/null
            else
                echo "Failed."
            fi
        else
            echo "Failed."
        fi
    else
        echo "Failed."
        echo
        echo "The version of ctags in your PATH is not Universal Ctags."
        echo "Please install Universal Ctags and ensure it is in your PATH".
        echo "If you are using the Emacs-Mac port for MacOS, you may need to"
        echo "reinstall it without the --with-ctags option."
    fi
else
    echo "Failed."
    echo
    echo "If you want to use Ctags, please install Universal Ctags."
fi

echo
echo "It is highly recommended to add the following lines to your $HOME/.emacs file,"
echo "if they are not already there:"
echo "  (setq proof-output-tooltips nil)"
echo "  (setq proof-three-window-mode-policy 'hybrid)"
echo "  (setq proof-three-window-enable t)"
echo "You can also set these values through the Emacs customization interface."
echo

if $EXEC_PATH_FROM_SHELL
then
    echo "You MUST also add the following line to your $HOME/.emacs file,"
    echo "if it is not already there:"
    echo "  (exec-path-from-shell-initialize)"
    echo
fi

if $CTAGS
then
    if [ `emacs -Q --batch --eval '(print (or (and (= emacs-major-version 30) (>= emacs-minor-version 1)) (> emacs-major-version 30)))'` = "t" ]
    then
        echo "To use Ctags, add the following lines to your $HOME/.emacs file,"
        echo "if they are not already there:"
        echo "  (etags-regen-mode t)"
        echo "  (setq etags-regen-program \"ctags -e\")"
        echo "  (add-to-list 'etags-regen-file-extensions \"ny\")"
    else
        echo 'To use ctags, you must first create a "TAGS" file by running the command'
        echo "  find . -name '*.ny' | ctags -e -L -"
        echo "in the root directory of your Narya project.  You'll need to do this again"
        echo "whenever new definitions are added to imported files."
        echo '(If you upgrade Emacs to version 30.1 or newer, you can instead use'
        echo '"etags-regen-mode" to automatically generate and regenerate the TAGS file.)'
    fi
fi

echo
echo "Then restart any open instances of Emacs."
echo
echo "The Narya ProofGeneral mode is activated by the Emacs package manager when Emacs"
echo "starts.  If your Emacs configuration disables that (for instance, by setting"
echo "package-enable-at-startup to nil, as some configuration frameworks do), you"
echo "will need to call (package-initialize) or (package-activate-all) yourself."
echo
if $NARYA_EL_LINK
then
    echo "Since the Narya elisp files were symlinked from the source tree, updates to"
    echo "them take effect when you restart Emacs.  You only need to run this script"
    echo "again if the set of files in the proofgeneral directory changes."
else
    echo "You will need to run this script again every time Narya is updated."
fi
