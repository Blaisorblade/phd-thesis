#!/bin/sh
lhs2TeX mapReduce.lhs > fig-mapReduce.tex
latexmk --pdf fig-mapReduce.tex
