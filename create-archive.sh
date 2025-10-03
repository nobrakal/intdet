#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

if command -v gnutar >/dev/null ; then
  # On MacOS, run "sudo port install gnutar" to obtain gnutar.
  TAR=gnutar
else
  TAR=tar
fi

ARCHIVE=intdet

rm -rf $ARCHIVE $ARCHIVE.tar.gz

mkdir $ARCHIVE

make clean

cp -r \
   dune-project \
   README.md \
   src \
   setup.sh \
   Makefile \
   packages.switch \
   LICENSE \
   INSTALL.md \
   $ARCHIVE

$TAR cvfz $ARCHIVE.tar.gz \
     --exclude-vcs-ignores \
     --exclude-vcs \
     --owner=0 --group=0 \
     $ARCHIVE

rm -rf $ARCHIVE
