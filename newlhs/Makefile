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
PAPERNAME = new
# Sources that will be watched for changes.
sources=$(PAPERNAME).lhs $(wildcard *.tex) $(wildcard ../Bibs/*.bib)

all:	open
OPEN = ./open.sh
open: $(PAPERNAME).pdf
	$(OPEN) $<

ifeq ($V, 1)
  REDIR=
else
  REDIR=> /dev/null
endif

%.tex: %.lhs
	lhs2TeX -o $*.tex $*.lhs
%.pdf: %.tex $(sources)
	latexmk -pv $* $(REDIR)

.PRECIOUS: %.tex

# Remove lhs2TeX and LaTeX build products.
clean:
	rm -f \
	$(PAPERNAME).aux $(PAPERNAME).bbl $(PAPERNAME).blg $(PAPERNAME).log $(PAPERNAME).tex \
	$(PAPERNAME).pdf $(PAPERNAME).ptb $(PAPERNAME).toc

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
