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
PAPER_NAME = thesis-main
PDF_NAME=$(PAPER_NAME).pdf
# Sources that will be watched for changes.
lhsFmt=$(wildcard *.fmt)
lhsSources=$(patsubst %,%.lhs,new-stuff change-theory-reconstruct \
	$(patsubst %,pldi14/%,sec-intro sec-change-theory sec-function-change sec-differentiate))
lhsCompiled=$(patsubst %.lhs,%.tex,$(lhsSources))
sources=$(shell find . -name '*.tex') $(wildcard Bibs/*.bib) $(lhsSources) $(lhsFmt)
INTERM_PRODUCTS=mylhs2tex.sty $(lhsCompiled)


all:	open
OPEN = ./open.sh

open: $(PDF_NAME)
	$(OPEN) $(PDF_NAME)

ifeq ($V, 1)
  REDIR=
else
  REDIR=> /dev/null
endif

.PHONY: FORCE
%.tex: %.lhs $(lhsFmt)
	lhs2TeX -P .: -o $*.tex $*.lhs
mylhs2tex.sty: mylhs2tex.lhs
	lhs2TeX -o $@ $<
%.pdf: %.tex $(INTERM_PRODUCTS) FORCE
	latexmk $* $(REDIR)

.PRECIOUS: %.tex

# Remove lhs2TeX and LaTeX build products.
clean:
	rm -f \
	$(PAPER_NAME).aux $(PAPER_NAME).bbl $(PAPER_NAME).blg $(PAPER_NAME).log \
	$(PAPER_NAME).pdf $(PAPER_NAME).ptb $(PAPER_NAME).toc $(INTERM_PRODUCTS)

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
