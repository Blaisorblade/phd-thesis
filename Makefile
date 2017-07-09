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
lhsSources=$(patsubst %,%.lhs, \
	chap-intro-incr chap-diff-examples chap-diff-correct-formal chap-chs \
	chap-eq-reason chap-th-extensions \
	new-stuff backmatter \
	fig-syntactic-ilc chap-operationally \
	$(patsubst %,pldi14/%,sec-preliminaries \
	fig-differentiation sec-rw))
lhsCompiled=$(patsubst %.lhs,%.tex,$(lhsSources))
# Sources to watch for changes but that don't need to be compiled on their own,
# because they're included elsewhere.
sourcesIncluded=$(shell find . -name '*.tex') $(wildcard Bibs/*.bib) $(lhsFmt) defunc.lhs
sources=$(lhsSources) $(sourcesIncluded)
INTERM_PRODUCTS=mylhs2tex.sty $(lhsCompiled)


all:	check open
OPEN = ./open.sh

open: $(PDF_NAME)
	$(OPEN) $(PDF_NAME)

ifeq ($V, 1)
  REDIR=
else
  REDIR=> /dev/null
endif

new-stuff.tex: defunc.lhs

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
	-make
	$(fswatch) $(sources) Makefile | $(xargs) make & \
	wait


%.hs: %.lhs $(lhsFmt)
	lhs2TeX --newcode -P .: -o $*.hs $*.lhs
check: defunc.hs
