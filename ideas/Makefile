ideas.pdf : ideas.tex references.bib
	pdflatex $^
	bibtex ideas
	pdflatex $^

RM ?= rm
CRUFT = *.aux *.fls *.log *.pdf *.toc

.PHONY : clean
clean :
	$(RM) $(CRUFT)
