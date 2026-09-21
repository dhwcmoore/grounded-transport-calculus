# Build the draft.  Requires pdflatex, bibtex (latexmk optional).
all: paper.pdf

paper.pdf: paper.tex refs.bib sections/*.tex
	latexmk -pdf -interaction=nonstopmode paper.tex

clean:
	latexmk -C
	rm -f *.bbl *.blg *.aux *.log *.out *.fls *.fdb_latexmk

.PHONY: all clean
