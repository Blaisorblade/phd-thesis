MAIN=thesis-main

LATEXMK=latexmk -e '$$pdf_previewer = "./open.sh %S"; $$pdf_update_command = "./open.sh %S";'
all: main rest
main:
	$(LATEXMK) $(MAIN)
demon:
	$(LATEXMK) -pvc $(MAIN)
