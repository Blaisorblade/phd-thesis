#!/bin/sh -e

# Config

dstBase=paperSources
dst=../$dstBase
output=$dstBase.tar.gz
main=pldi14-ilc

getDeps() {
  # Update latexmk database
  # Redirect to stderr to avoid disturbing the return value (given on the output)
  runLatexMk 1>&2
  # Extract dependencies from latexmk output. .aux files are excluded on purpose, since they aren't send.
  egrep -v '/usr/local|\.aux$' pldi14-ilc.fls |gsed -rn -e 's!INPUT (\./)?!!p'|sort|uniq
}

cleanOutput() {
  # Wipe output clean!
  printf "\nRemoving $dst!\n\n"

  rm -rf $dst
  mkdir -p $dst
}

copyNonTeX() {
  cp $(getDeps|grep -v '\.tex$') $dst/
}

createNonTeXExtras() {
  # http://arxiv.org/help/00README
  echo nohypertex > $dst/00README.XXX
}

stripCommentsFromTeX() {
  # Only include used files.; unused ones (only included under conditinal compilation directives)
  # should be treated as comments, hence removed.
  for i in $(getDeps|grep '\.tex$'); do
    cat $i |
    perl -pe 's/(^|[^\\])%.*/\1%/' |
    awk 'BEGIN {exclude=0;} /begin{oldSec}/ {exclude=1} exclude==0 {print;} /end{oldSec}/ {exclude=0;}' > \
	$dst/$i
  done
}

runLatexMk() {
  latexmk -pdf $main
}

compile() {
  runLatexMk
}

testOutput() {
  compile
  cd $dst
  compile

  printf "\nCheck the following diff, only timestamps and the ID should be different\n\n"

  diff -U0 --text $main.pdf ~- || true

  printf "\nEnd of diff\n"
}

archiveOutput() {
  # This is what arXiv would remove. Note we do must keep the .bbl file, per
  # https://arxiv.org/help/submit_tex#bibtex (arXiv won't run BibTeX).
  rm $main.pdf $main.aux $main.blg $main.log $main.fls $main.fdb_latexmk

  cd ..

  tar czf $output $dstBase/

  printf "Output saved in $output inside $PWD\n"
}

# Entry point.

cleanOutput
copyNonTeX
createNonTeXExtras
stripCommentsFromTeX
testOutput
archiveOutput
