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
PAPER_NAME = static-caching
PDF_NAME=$(PAPER_NAME).pdf

lhsFormat = changes.fmt

lhsSources = \
	cts-intro.lhs cts-motivation.lhs \
	cts-case-studies.lhs cts-relwork.lhs cts-conclusion.lhs
lhsCompiled=$(patsubst %.lhs,%.tex,$(lhsSources))
# Sources to watch for changes but that don't need to be compiled on their own,
# because they're included elsewhere.
sourcesIncluded=$(wildcard *.tex) $(wildcard ../Bibs/*.bib) syntaxmacros.sty $(lhsFormat)
# Sources that will be watched for changes.
sources=$(lhsSources) $(sourcesIncluded)

INTERM_PRODUCTS=$(lhsCompiled)

all: open
OPEN = ./open.sh

open: $(PDF_NAME)
	$(OPEN) $(PDF_NAME)

ifeq ($V, 1)
  REDIR=
else
  REDIR=> /dev/null
endif

.PHONY: FORCE
%.tex: %.lhs $(lhsFormat)
	lhs2TeX -P .: -o $*.tex $*.lhs
%.pdf: %.tex $(INTERM_PRODUCTS) $(sources) FORCE
	latexmk -pdf $* $(REDIR)
quick: $(PAPER_NAME).tex $(INTERM_PRODUCTS) $(sources)
	# Pass pdflatex the same options as latexmk would.
	pdflatex -synctex=1 -file-line-error -recorder $(PAPER_NAME)
	$(OPEN) $(PDF_NAME)

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

quickdemon:
	-make quick
	$(fswatch) $(sources) Makefile | $(xargs) make quick & \
	wait
