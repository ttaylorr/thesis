.DEFAULT_GOAL := thesis.pdf

SECTIONS =
SECTIONS += abstract.tex
SECTIONS += acknowledgements.tex
SECTIONS += dedication.tex
SECTIONS += introduction.tex
SECTIONS += overview.tex
SECTIONS += results.tex
SECTIONS += title.tex

FIGURES =
FIGURES += figures/1/semi-lattice.pdf

ISABELLE ?= /Applications/Isabelle2019.app/Isabelle/bin/isabelle
ISABELLE_STY = comment.sty isabelle.sty isabellesym.sty pdfsetup.sty railsetup.sty

$(ISABELLE_STY) :
	$(ISABELLE) latex -o sty

thesis.pdf : thesis.tex thesis.cls $(SECTIONS) $(FIGURES) $(ISABELLE_STY)
	pdflatex -shell-escape $^
	bibtex $(patsubst %.tex,%,$<)
	pdflatex -output-directory $(dir $@) $<

%.pdf : %.tex
	pdflatex -output-directory $(dir $@) $<

.PHONY : clean
clean:
	$(RM) -rf *.aux *.log *.pdf *.pyc *.toc *.out $(ISABELLE_STY)
