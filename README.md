# Paolo G. Giarrusso's phd-thesis

# Compilation instructions

## For archival

To recompile with the fewest dependencies, proceed as follows:
```
pdflatex -shell-escape thesis-main
bibtex thesis-main
```
And then repeat `pdflatex -shell-escape thesis-main` until convergence.

## Development

Install lhs2TeX and compile with `make`. This thesis was compiled with lhs2TeX
1.22. An up-to-date snapshot of the lhs2TeX output is included.
