PDFLATEX ?= $(shell which pdflatex)
BIBER ?= $(shell which biber)
RM ?= rm

plse-nov.pdf : plse-nov.tex plse-nov.bib
	$(PDFLATEX) $<
	$(BIBER) $(patsubst %.tex,%,$<)
	$(PDFLATEX) $<

.PHONY : clean
clean :
	$(RM) -rf *.aux *.log *.nav *.out *.pdf *.snm *.toc *.bbl *.bcf *.blg *.run.xml
