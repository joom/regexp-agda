default: generate

generate:
	lhs2TeX -o Report.tex Report.lagda --agda
	sed -i -e 's/ˢ/\\(^s\\)/g' Report.tex  # replace unrecognized unicode char
	pdflatex Report.tex
