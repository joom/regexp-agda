default: generate

generate:
	lhs2TeX -o Report.tex Report.lagda --agda
# replace unrecognized unicode chars
	sed -i -e 's/ˢ/\\(^s\\)/g; s/ᵏ/\\(^k\\)/g' Report.tex
	pdflatex Report.tex
