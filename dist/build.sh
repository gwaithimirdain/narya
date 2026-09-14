#!/bin/bash

# Usage: ./build.sh [BINARY [PLATFORM [INSTALL]]]
# Bundles the narya executable BINARY with the ProofGeneral and ctags files
# and the installation instructions INSTALL into
# build/releases/narya-master-PLATFORM.tar.gz.
BINARY=${1:-../result/bin/narya}
PLATFORM=${2:-static}
INSTALL=${3:-INSTALL.txt}

NAME=narya-`git show -s --format=%h`-`date +'%Y%m%d'`
mkdir -p $NAME
cp ../proofgeneral/*.el $NAME
cp ../ctags/narya.ctags $NAME
cp $BINARY $NAME/narya
cp $INSTALL $NAME/INSTALL.txt
cp install-pg.sh proof-site.patch $NAME
tar -czf narya-master-$PLATFORM.tar.gz $NAME
mkdir -p build/releases
mv narya-master-$PLATFORM.tar.gz build/releases
