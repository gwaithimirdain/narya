#!/bin/bash

NAME=narya-`git show -s --format=%h`-`date +'%Y%m%d'`
mkdir -p $NAME
cp ../proofgeneral/*.el $NAME
cp ../result/bin/narya $NAME
tar -czf $NAME.tar.gz $NAME
mkdir -p build/releases
mv $NAME.tar.gz build/releases
