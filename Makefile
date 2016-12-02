MAIN=main

LATEXMK=latexmk -e '$$pdf_previewer = "./open.sh %S"; $$pdf_update_command = "./open.sh %S";'
all: main rest
main:
	$(LATEXMK) $(MAIN)
demon:
	$(LATEXMK) -pvc $(MAIN)

OTHER=new
rest: $(OTHER).pdf

%.pdf: %.tex
	$(LATEXMK) -pv $*
%.tex: %.lhs
	lhs2TeX -o $@ $<
.PRECIOUS: %.tex
