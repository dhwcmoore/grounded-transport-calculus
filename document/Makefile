# Build the paper with the official LMCS class (lmcs.cls).
# Requires pdflatex and bibtex; latexmk optional.
all: paper.pdf

paper.pdf: paper.tex refs.bib lmcs.cls sections/*.tex
	latexmk -pdf -interaction=nonstopmode paper.tex

clean:
	latexmk -C
	rm -f *.bbl *.blg *.aux *.log *.out *.fls *.fdb_latexmk

.PHONY: all clean

# arXiv source package (arXiv needs the .bbl, not the .bib): tex sources, class,
# bibliography output.  Test-compiled from a clean directory.
arxiv: paper.pdf
	rm -rf arxiv-src && mkdir -p arxiv-src/sections
	cp paper.tex lmcs.cls paper.bbl arxiv-src/
	cp sections/*.tex arxiv-src/sections/
	cd arxiv-src && tar czf ../arxiv-source.tar.gz .
	rm -rf arxiv-test && mkdir arxiv-test && tar xzf arxiv-source.tar.gz -C arxiv-test
	cd arxiv-test && pdflatex -interaction=nonstopmode paper.tex >/dev/null && pdflatex -interaction=nonstopmode paper.tex >/dev/null && pdfinfo paper.pdf | grep Pages
	rm -rf arxiv-test arxiv-src

.PHONY: arxiv
