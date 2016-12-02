# Makefile to compile the paper. Taken from my functors repo with Cai.
#
# Usage: `make`
#
# To recompile on changes, if you install fswatch (see below): `make demon`.
# Optional parameter: OPEN='opening command', V=1 (for verbose latex compilation)
# `make demon OPEN=''`.
#
# Installing fswatch easily on Mac:
# 1. install homebrew
# 2. brew install fswatch
#
# If you suspect stale build products, then `make fresh`.

# Name of the main build product.
# XXX add underscore
PAPERNAME = thesis-main
PDF_NAME=$(PAPERNAME).pdf
# Sources that will be watched for changes.
sources=$(wildcard *.tex) $(wildcard Bibs/*.bib)
INTERM_PRODUCTS=newlhs/new.tex mylhs2tex.sty

all:	open
OPEN = ./open.sh

open: $(PDF_NAME)
	$(OPEN) $(PDF_NAME)

ifeq ($V, 1)
  REDIR=
else
  REDIR=> /dev/null
endif

%.tex: %.lhs
	lhs2TeX -o $*.tex $*.lhs
mylhs2tex.sty: mylhs2tex.lhs
	lhs2TeX -o $@ $<
%.pdf: %.tex $(sources) $(INTERM_PRODUCTS)
	latexmk $* $(REDIR)

.PRECIOUS: %.tex

# Remove lhs2TeX and LaTeX build products.
clean:
	rm -f \
	$(PAPERNAME).aux $(PAPERNAME).bbl $(PAPERNAME).blg $(PAPERNAME).log \
	$(PAPERNAME).pdf $(PAPERNAME).ptb $(PAPERNAME).toc $(INTERM_PRODUCTS)

fresh:
	make clean
	make

fswatch = fswatch -0o

# `cmd1 | $(xargs) cmd2` will run cmd2 each time cmd1 outputs a '\0'-terminated
# string.
xargs = xargs -0 -n 1 -I '{}' -t

demon:
	make
	$(fswatch) $(sources) Makefile | $(xargs) make & \
	wait
