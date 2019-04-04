SOURCENAME=Report
FILENAME=file
OUTPUTNAME=output
LATEX=pdflatex

default: preview

lagda:
	lhs2TeX --poly -o $(FILENAME).tex $(SOURCENAME).lagda --agda

compile:
	@$(LATEX) $(FILENAME).tex
	@bibtex $(FILENAME) > /dev/null
	@$(LATEX) $(FILENAME).tex 2> /dev/null
	@$(LATEX) $(FILENAME).tex 2> /dev/null
	@$(LATEX) $(FILENAME).tex
	@mv $(FILENAME).pdf $(OUTPUTNAME).pdf

debug:
	cp $(SOURCENAME).tex $(FILENAME).tex
	$(LATEX) $(FILENAME).tex
	bibtex $(FILENAME)
	$(LATEX) $(FILENAME).tex
	$(LATEX) $(FILENAME).tex
	$(LATEX) $(FILENAME).tex
	mv $(FILENAME).pdf $(OUTPUTNAME).pdf

open:
	@open -a /Applications/Preview.app $(OUTPUTNAME).pdf

clean:
	@rm *.aux
	@rm *.log
	@rm $(FILENAME).*

preview: lagda compile open clean
normal: lagda compile clean
