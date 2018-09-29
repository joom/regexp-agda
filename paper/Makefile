FILENAME=report
SOURCENAME=source
OUTPUTNAME=output
LATEX=xelatex

default: preview

compile:
	@cp $(SOURCENAME).lagda $(FILENAME).lagda
	lhs2TeX -o $(FILENAME).tex $(FILENAME).lagda --agda
	pdflatex $(FILENAME).tex
	bibtex $(FILENAME)
	pdflatex $(FILENAME).tex
	pdflatex $(FILENAME).tex
	@mv $(FILENAME).pdf $(OUTPUTNAME).pdf

open:
	@open -a /Applications/Preview.app $(OUTPUTNAME).pdf

clean:
	@rm *.aux
	@rm $(FILENAME).*

preview: compile open clean
