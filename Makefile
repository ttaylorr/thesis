.DEFAULT_GOAL := thesis.pdf

SECTIONS =
SECTIONS += abstract.tex
SECTIONS += acknowledgements.tex
SECTIONS += dedication.tex
SECTIONS += introduction.tex
SECTIONS += title.tex

FIGURES =
FIGURES += figures/1/semi-lattice.pdf

thesis.pdf : thesis.tex thesis.cls $(SECTIONS) $(FIGURES)
	pdflatex -shell-escape $^
	bibtex $(patsubst %.tex,%,$<)
	pdflatex -output-directory $(dir $@) $<

%.pdf : %.tex
	pdflatex -output-directory $(dir $@) $<

.PHONY : clean
clean:
	$(RM) -rf *.aux *.log *.pdf *.pyc *.toc *.out
