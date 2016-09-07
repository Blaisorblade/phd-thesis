MAIN=main

all: main rest
main:
	latexmk $(MAIN)
demon:
	latexmk -pvc $(MAIN)

OTHER=new
rest: $(OTHER).pdf

%.pdf: %.tex
	latexmk -pv $*
%.tex: %.lhs
	lhs2TeX -o $@ $<
