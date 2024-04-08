
.PHONY: default

default:
	stack build

results.csv:
	stack bench --benchmark-arguments "--csv $@"

results.dat: results.csv graph/criterion2pgfplotcsv.csv
	cat $< | stack exec criterion2pgfplotcsv > $@

results.pdf: graph/results.tex results.csv
	latexmk -pdf graph/results.tex

clean:
	rm -f results.*
	stack clean
