default: generate

generate:
	lhs2TeX -o Report.tex Report.lagda --agda
	pdflatex Report.tex
	bibtex Report
	pdflatex Report.tex
	pdflatex Report.tex
