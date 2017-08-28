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
# $(PAPER_NAME).fmt is a TeX format not a lhs2TeX format.
lhsFmt=$(filter-out $(PAPER_NAME).fmt, $(wildcard *.fmt))
lhsSources=$(patsubst %,%.lhs, \
	chap-intro-incr chap-diff-examples chap-diff-correct-formal chap-chs \
	chap-eq-reason chap-th-extensions chap-towards-sysf \
	defunc new-stuff backmatter \
	fig-syntactic-ilc chap-operationally \
	$(patsubst %,pldi14/%,\
		sec-preliminaries fig-differentiation sec-rw) \
	$(patsubst %,popl18/%, \
		cts-intro cts-motivation \
		cts-case-studies cts-relwork cts-conclusion))
lhsCompiled=$(patsubst %.lhs,%.tex,$(lhsSources))
# Sources to watch for changes but that don't need to be compiled on their own,
# because they're included elsewhere.
sourcesIncluded=$(shell find . -name '*.tex' -o -name '*.sty') $(wildcard Bibs/*.bib) $(lhsFmt)
# Sources that will be watched for changes.
sources=$(lhsSources) $(sourcesIncluded)

INTERM_PRODUCTS=mylhs2tex.sty $(lhsCompiled)


all: check open
OPEN = ./open.sh

open: $(PDF_NAME)
	$(OPEN) $(PDF_NAME)

ifeq ($V, 1)
  REDIR=
else
  REDIR=> /dev/null
endif

# Name of base processor and TeX base format.
baseProcessor = pdflatex
# Name of TeX base format. Often coincides with baseProcessor.
baseFormat = $(baseProcessor)

TeXOpts := -synctex=1 -file-line-error -recorder
TeXOpts += -interaction=nonstopmode -halt-on-error
#TeXOpts += -interaction=errorstopmode

.PHONY: FORCE
%.tex: %.lhs $(lhsFmt)
	lhs2TeX -P .:popl18: -o $*.tex $*.lhs
mylhs2tex.sty: mylhs2tex.lhs
	lhs2TeX -o $@ $<
# After the first build, this file will be recompiled by latexmk accounting for
# all other dependencies thanks to code in .latexmkrc.
# This line is hence only for the first build. Keep it in sync with .latexmkrc!
%.fmt: %.ltx mylhs2tex.sty
	$(baseProcessor) -ini -recorder -jobname="$*" "&${baseFormat} $*.ltx \dump"
# Save log file.
	mv $*.log $*-fmt.log
%.pdf: %.tex %.fmt $(INTERM_PRODUCTS) FORCE
	latexmk $* $(REDIR)
# Pass pdflatex the same options as latexmk would.
quick: $(PAPER_NAME).tex $(PAPER_NAME).fmt $(INTERM_PRODUCTS) FORCE
	$(baseProcessor) $(TeXOpts) $(PAPER_NAME)
	$(OPEN) $(PDF_NAME)

.PRECIOUS: %.tex

# Remove lhs2TeX and LaTeX build products.
clean:
	rm -f \
	$(PAPER_NAME).aux $(PAPER_NAME).bbl $(PAPER_NAME).blg $(PAPER_NAME).log \
	$(PAPER_NAME).pdf $(PAPER_NAME).ptb $(PAPER_NAME).toc $(PAPER_NAME).thm \
	$(PAPER_NAME).fmt \
	$(INTERM_PRODUCTS) \
	$(find . -name '*.aux')

fresh:
	make clean
	make

fswatch = fswatch -0o

# `cmd1 | $(xargs) cmd2` will run cmd2 each time cmd1 outputs a '\0'-terminated
# string.
xargs = xargs -0 -n 1 -I '{}' -t

demon:
	-make
	$(fswatch) $(sources) Makefile | $(xargs) time make & \
	wait

quickdemon:
	-make quick
	$(fswatch) $(sources) Makefile | $(xargs) time make quick & \
	wait

%.hs: %.lhs $(lhsFmt)
	lhs2TeX --newcode -P .: -o $*.hs $*.lhs
check: defunc.hs chap-towards-sysf.hs
