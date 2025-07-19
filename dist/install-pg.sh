#!/bin/bash

echo
echo Installing ProofGeneral...

# Write a minimal init file to enable MELPA and package.el
TEMPINIT=$(mktemp)
cat >"$TEMPINIT" <<EOF
(require 'package)
(setq package-archives '(("melpa" . "https://melpa.org/packages/")
                         ("gnu" . "https://elpa.gnu.org/packages/")))
(package-initialize)
(unless package-archive-contents
  (package-refresh-contents))
(package-install 'proof-general)
EOF

# Run Emacs in batch mode to install proof-general
if ! emacs -Q --batch -l "$TEMPINIT"
then
    echo Error running Emacs; is it installed correctly?
    exit 1
fi

# Clean up temporary init file
rm -f "$TEMPINIT"

echo
echo Installing the Narya ProofGeneral mode...

# Locate the installed directory
PGDIR=$(find ~/.emacs.d/elpa/ -maxdepth 1 -type d -name "proof-general-*" | sort -r | head -n1)

if ! [ -d $PGDIR ]
then
    echo I can\'t find the ProofGeneral installation directory!
    exit 1
fi

mkdir -p $PGDIR/narya

# Install the narya elisp files, replacing any old ones.
if [ -e narya.el ]
then
    rm -f $PGDIR/narya/*.el $PGDIR/narya/*.elc
    if ! cp -f *.el $PGDIR/narya
    then
        echo Error copying elisp files
        exit 1
    fi
elif [ -e ../proofgeneral/narya.el ]
then
     echo You appear to be running this script from the Narya source tree,
     echo so I will symlink the Narya .el files instead of copying them.
     pushd ../proofgeneral >/dev/null
     NARYA_PGDIR=`pwd`
     popd >/dev/null
     pushd $PGDIR/narya >/dev/null
     rm -f *.el *.elc
     ln -s $NARYA_PGDIR/*.el .
     popd >/dev/null
else
    echo I can\'t find the Narya .el files!
    exit 1
fi

# Insert Narya into the ProofGeneral configuration, if it isn't already there
if ! grep narya $PGDIR/generic/proof-site.el >/dev/null
then
    if [ -e proof-site.patch ]
    then
        patch -d $PGDIR/generic <proof-site.patch
        # Remove old byte-compiled version, if any, so the new source version is loaded instead
        rm -f $PGDIR/generic/proof-site.elc
    else
        echo I can\'t find proof-site.patch!
    fi
fi

echo
echo Installing Narya ctags configuration...

mkdir -p $HOME/.ctags.d

# Install the Narya ctags configuration file, replacing any old one
if [ -e narya.ctags ]
then
    rm -f $HOME/.ctags.d/narya.ctags
    if ! cp -f narya.ctags $HOME/.ctags.d
    then
        echo Error copying tags file
    fi
elif [ -e ../ctags/narya.ctags ]
then
     echo You appear to be running this script from the Narya source tree,
     echo so I will symlink the Narya .ctags file instead of copying it.
     pushd ../ctags >/dev/null
     NARYA_CTAGS=`pwd`
     popd >/dev/null
     pushd $HOME/.ctags.d >/dev/null
     rm -f narya.ctags
     ln -s $NARYA_CTAGS/narya.ctags .
     popd >/dev/null
else
    echo I can\'t find the Narya .ctags file!
    exit 1
fi

echo
echo Narya ProofGeneral and Ctags installed.
echo
echo To use ctags, add the following lines to your $HOME/.emacs file:
echo "  (etags-regen-mode t)"
echo "  (add-to-list 'etags-regen-file-extensions \"ny\")"
echo 
echo Then restart any open instances of Emacs.
echo "(You will need to run this script again every time Emacs, ProofGeneral, or Narya is updated.)"
