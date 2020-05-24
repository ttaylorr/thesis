PDFLATEX ?= $(shell which pdflatex)
BIBER ?= $(shell which biber)
RM ?= rm

reading-summary.pdf : reading-summary.tex reading-summary.bib
	$(PDFLATEX) $<
	$(BIBER) $(patsubst %.tex,%,$<)
	$(PDFLATEX) $<

.PHONY : clean
clean :
	$(RM) -rf *.aux *.log *.nav *.out *.pdf *.snm *.toc
