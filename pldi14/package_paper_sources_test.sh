cd $(dirname "$0")

(cd ..; [ -d arxivPaper ] && { rm -rf arxivPaper-sav; cp -a arxivPaper arxivPaper-sav; })

./package_paper_sources.sh

cd ..

[ -d arxivPaper-sav ] && { diff -ur --brief arxivPaper arxivPaper-sav && echo "Output did not change; diff exitcode $?" || echo "Output did change!"; }
