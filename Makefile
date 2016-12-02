MAIN=thesis-main

LATEXMK=latexmk -e '$$pdf_previewer = "./open.sh %S"; $$pdf_update_command = "./open.sh %S";'
all: main rest
main: mylhs2tex.sty
	$(LATEXMK) $(MAIN)
demon: mylhs2tex.sty
	$(LATEXMK) -pvc $(MAIN)

mylhs2tex.sty: mylhs2tex.lhs
	lhs2TeX mylhs2tex.lhs -o mylhs2tex.sty
