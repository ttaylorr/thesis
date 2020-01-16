.DEFAULT_GOAL := thesis.pdf

thesis.pdf : thesis.tex abstract.tex title.tex thesis.cls
	pdflatex -shell-escape $^

%.pdf : %.tex
	pdflatex -output-directory $(dir $@) $<

.PHONY : clean
clean:
	$(RM) -rf *.aux *.log *.pdf *.pyc *.toc *.out
