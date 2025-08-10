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
        echo "Make sure that you ran both commands:"
        echo
        echo "dune build @install"
        echo "dune install"
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

echo "Installing ProofGeneral..."

TEMPINIT=$(mktemp)
cat >"$TEMPINIT" <<EOF
(require 'package)
(setq package-archives '(("melpa" . "https://melpa.org/packages/")
                         ("gnu" . "https://elpa.gnu.org/packages/")))
(package-initialize)
(package-refresh-contents)
(package-install 'proof-general)
EOF

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

echo -n "Locating the ProofGeneral installation directory..."

PGDIR=$(find ~/.emacs.d/elpa/ -maxdepth 1 -type d -name "proof-general-*" | sort -r | head -n1)

if [ -d $PGDIR ]
then
    echo "Found."
else
    echo "Failed."
    echo
    echo "I can't find the ProofGeneral installation directory."
    echo "Please open an issue at https://github.com/gwaithimirdain/narya/issues."
    exit 1
fi

echo -n "Copying the Narya ProofGeneral files..."

if mkdir -p $PGDIR/narya
then
    :
else
    echo "Failed."
    echo
    echo "I can't create a narya directory in the ProofGeneral directory."
    echo "Make sure you have write/execute permissions to $PGDIR."
    exit 1
fi    

# Install the narya elisp files, replacing any old ones.
if [ -e narya.el ]
then
    rm -f $PGDIR/narya/*.el $PGDIR/narya/*.elc
    if cp -f *.el $PGDIR/narya
    then
        echo "Succeeded."
    else
        echo "Failed."
        echo
        echo "Error copying elisp files."
        echo "Please open an issue at https://github.com/gwaithimirdain/narya/issues."
        exit 1
    fi
elif [ -e ../proofgeneral/narya.el ]
then
    echo
    echo "You appear to be running this script from the Narya source tree."
    echo -n "Symlinking the elisp files..."
    pushd ../proofgeneral >/dev/null
    NARYA_PGDIR=`pwd`
    popd >/dev/null
    pushd $PGDIR/narya >/dev/null
    rm -f *.el *.elc
    if ln -s $NARYA_PGDIR/*.el .
    then
        echo "Succeeded."
    else
        echo "Failed."
        echo -n "Trying to copy them instead..."
        if cp $NARYA_PGDIR/*.el .
        then
            echo "Succeeded."
        else
            echo "Failed."
            echo
            echo "Make sure you have write/execute permissions to $PGDIR/narya."
            echo "You can also open an issue at https://github.com/gwaithimirdain/narya/issues."
            exit 1
        fi
    fi
    popd >/dev/null
else
    echo "Failed."
    echo
    echo "I can't find narya.el."
    echo "Please run this script from the unpacked static distribution directory"
    echo "or from the dist/ directory in the Narya source tree."
    exit 1
fi

# Insert Narya into the ProofGeneral configuration, if it isn't already there
if grep narya $PGDIR/generic/proof-site.el >/dev/null
then
    echo "ProofGeneral is already configured for Narya."
else
    echo -n "Configuring ProofGeneral for Narya..."

    if [ -e proof-site.patch ]
    then
        # Also remove old byte-compiled version, if any, so the new source version is loaded instead
        if patch -d $PGDIR/generic <proof-site.patch && rm -f $PGDIR/generic/proof-site.elc
        then
            echo "Succeeded."
        else
            echo "Failed."
            echo
            echo "Please open an issue at https://github.com/gwaithimirdain/narya/issues."
            exit 1
        fi
    else
        echo "Failed."
        echo
        echo "I can't find proof-site.patch."
        echo "Please run this script from the unpacked static distribution directory"
        echo "or from the dist/ directory in the Narya source tree."
        exit 1
    fi
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
echo "You will need to run this script again every time Emacs, ProofGeneral, or Narya is updated."
