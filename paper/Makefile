default: generate

generate:
	lhs2TeX -o Report.tex Report.lagda --agda
	bibtex Report
	pdflatex Report.tex
