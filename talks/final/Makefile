.DEFAULT_GOAL := final.pdf

ifdef HANDOUT
PREAMBLE=\newcommand{\handout}{1}
else
PREAMBLE=\newcommand{\nohandout}{1}
endif

final.pdf : final.tex
	pdflatex -shell-escape "${PREAMBLE} \input{$(patsubst %.tex,%,$<)}"

.PHONY : clean
clean :
	rm -rf *.aux *.log *.nav *.out *.pdf *.snm *.toc
