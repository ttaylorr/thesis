.DEFAULT_GOAL := thesis.pdf

SECTIONS =
SECTIONS += abstract.tex
SECTIONS += acknowledgements.tex
SECTIONS += appendix.tex
SECTIONS += background.tex
SECTIONS += conclusion.tex
SECTIONS += crdt-instantiations.tex
SECTIONS += crdt-reductions.tex
SECTIONS += dedication.tex
SECTIONS += example-crdts.tex
SECTIONS += future-work.tex
SECTIONS += introduction.tex
SECTIONS += title.tex

ISABELLE ?= /Applications/Isabelle2019.app/Isabelle/bin/isabelle
ISABELLE_STY = comment.sty isabelle.sty isabellesym.sty pdfsetup.sty railsetup.sty

THEORIES =
THEORIES += src/DeltaGCounter.thy
THEORIES += src/DeltaGSet.thy
THEORIES += src/GCounter.thy
THEORIES += src/GSet.thy

THEORY = src/output/document.pdf

FIGURES =
FIGURES += figures/theories/delta-gcounter-appendix.tex
FIGURES += figures/theories/delta-gcounter.tex

FIGURES += figures/theories/restricted-delta-gset-appendix.tex
FIGURES += figures/theories/delta-gset-appendix.tex
FIGURES += figures/theories/delta-gset.tex

FIGURES += figures/theories/restricted-delta-gcounter-appendix.tex
FIGURES += figures/theories/delta-gcounter-refined-ops.tex
FIGURES += figures/theories/delta-gcounter-refined-state.tex
FIGURES += figures/theories/delta-gset-refined-ops.tex
FIGURES += figures/theories/delta-gset-refined-state.tex

FIGURES += figures/theories/gcounter-appendix.tex
FIGURES += figures/theories/gcounter-comm-assoc.tex
FIGURES += figures/theories/gcounter-commute.tex
FIGURES += figures/theories/gcounter-convergence.tex
FIGURES += figures/theories/gcounter-misc.tex
FIGURES += figures/theories/gcounter-state-op.tex
FIGURES += figures/theories/gcounter-state-sec.tex
FIGURES += figures/theories/gcounter-state.tex
FIGURES += figures/theories/gcounter.tex

FIGURES += figures/theories/gset-appendix.tex
FIGURES += figures/theories/gset-state-op.tex
FIGURES += figures/theories/gset-state-sec.tex
FIGURES += figures/theories/gset-state.tex
FIGURES += figures/theories/gset.tex

FIGURES += figures/scalar-state.pdf
FIGURES += figures/vector-delta.pdf
FIGURES += figures/vector-state.pdf

FIGURES += figures/sec-delta.pdf

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

figures/%.pdf : figures/%.tex
	pdflatex -output-directory $(dir $@) $

arXiv.tar.gz : thesis.pdf classicthesis.sty
	tar -czf $@ thesis.tex thesis.cls thesis.bib thesis.bbl $(FIGURES) \
		isabelle.sty isabellesym.sty classicthesis.sty $(SECTIONS)

classicthesis.sty :
	curl http://ctan.math.washington.edu/tex-archive/macros/latex/contrib/classicthesis/classicthesis.sty > classicthesis.sty

$(THEORY) : $(THEORIES)
	$(ISABELLE) build -D src || true

.PHONY : clean
clean:
	$(RM) -rf *.aux *.log *.pdf *.pyc *.toc *.out $(ISABELLE_STY)
