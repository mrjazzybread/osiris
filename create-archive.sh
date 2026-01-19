#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

if command -v gnutar >/dev/null ; then
  # On MacOS, run "sudo port install gnutar" to obtain gnutar.
  TAR=gnutar
else
  TAR=tar
fi

ARCHIVE=../osiris-archive

rm -rf $ARCHIVE $ARCHIVE.tar.gz

git clone . $ARCHIVE
rm -rf $ARCHIVE/.git
rm     $ARCHIVE/.gitlab-ci.yml
rm     $ARCHIVE/AUTHORS.md
rm     $ARCHIVE/TODO.md
rm     $ARCHIVE/create-archive.sh
rm -r  $ARCHIVE/misc
rm     $ARCHIVE/osiris/osiris.opam
rm     $ARCHIVE/rocq-osiris/rocq-osiris.opam
rm     $ARCHIVE/rocq-osiris/rocq-osiris-examples.opam
sed -i '/[Pp]ottier/d'    $ARCHIVE/README.md
sed -i '/[Pp]ottier/d'    $ARCHIVE/{,rocq-}osiris/dune-project
sed -i '/Daby-Seesaram/d' $ARCHIVE/{,rocq-}osiris/dune-project
sed -i '/Madiot/d'        $ARCHIVE/{,rocq-}osiris/dune-project
sed -i '/Seassau/d'       $ARCHIVE/{,rocq-}osiris/dune-project
sed -i '/Yoon/d'          $ARCHIVE/{,rocq-}osiris/dune-project
git init $ARCHIVE

$TAR cvfz $ARCHIVE.tar.gz \
  --exclude-ignore-recursive=.gitignore \
  --owner=0 --group=0 \
  $ARCHIVE

rm -rf $ARCHIVE
