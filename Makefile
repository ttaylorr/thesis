.DEFAULT_GOAL := thesis.pdf

SECTIONS =
SECTIONS += abstract.tex
SECTIONS += acknowledgements.tex
SECTIONS += background.tex
SECTIONS += dedication.tex
SECTIONS += introduction.tex
SECTIONS += overview.tex
SECTIONS += results.tex
SECTIONS += title.tex

ISABELLE ?= /Applications/Isabelle2019.app/Isabelle/bin/isabelle
ISABELLE_STY = comment.sty isabelle.sty isabellesym.sty pdfsetup.sty railsetup.sty

$(ISABELLE_STY) :
	$(ISABELLE) latex -o sty

ifdef WEB
PREAMBLE=\newcommand{\forweb}{1}
else
PREAMBLE=\newcommand{\forprint}{1}
endif

thesis.pdf : thesis.tex thesis.cls $(SECTIONS) $(FIGURES) $(ISABELLE_STY)
	pdflatex -shell-escape "${PREAMBLE} \input{$(patsubst %.tex,%,$<)}"
	bibtex $(patsubst %.tex,%,$<)
	pdflatex -shell-escape "${PREAMBLE} \input{$(patsubst %.tex,%,$<)}"

.PHONY : clean
clean:
	$(RM) -rf *.aux *.log *.pdf *.pyc *.toc *.out $(ISABELLE_STY)
