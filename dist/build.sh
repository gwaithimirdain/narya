#!/bin/bash

NAME=narya-`git show -s --format=%h`-`date +'%Y%m%d'`
mkdir -p $NAME
cp ../proofgeneral/*.el $NAME
cp ../result/bin/narya $NAME
cp INSTALL.txt $NAME
tar -czf narya-master-static.tar.gz $NAME
mkdir -p build/releases
mv narya-master-static.tar.gz build/releases
