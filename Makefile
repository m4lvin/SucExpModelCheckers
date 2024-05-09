
.PHONY: default

default:
	stack build

results.csv: bench/Main.hs
	rm -rf results.csv
	stack bench --benchmark-arguments "--csv $@"

results.dat: results.csv graph/criterion2pgfplotcsv.hs
	cat $< | stack exec criterion2pgfplotcsv > $@

results.pdf: results.tex results.dat
	latexmk -pdf results.tex

clean:
	rm -f results.*
	stack clean
