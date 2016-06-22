MAIN=main
all:
	latexmk $(MAIN)
demon:
	latexmk -pvc $(MAIN)
