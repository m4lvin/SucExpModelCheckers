
.PHONY: default

default:
	stack build

results.csv:
	stack bench --benchmark-arguments "--csv results.csv"

results.dat: results.csv
	cat $< | stack exec criterion2pgfplotcsv > results.dat

results.pdf: graph/results.tex results.csv
	latexmk -pdf graph/results.tex

clean:
	rm -f results.*
	stack clean
