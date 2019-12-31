#!/bin/sh
lhs2TeX fig-mapReduce.lhs > fig-mapReduce.tex
latexmk --pdf fig-mapReduce.tex
