# Paper draft

`paper.tex` is a FIRST DRAFT of *Grounded Transport: A Proof-Relevant Rewriting
Calculus for Lineage-Sensitive Systems*.

    make          # builds paper.pdf (pdflatex + bibtex via latexmk)
    make clean

Layout: `paper.tex` (preamble, abstract), `sections/NN-*.tex` (one file per
section of the outline), `sections/appendix-ledger.tex` (theorem spine T1-T20
mapped to Coq identifiers), `refs.bib`.

Status of the draft
- ~23 pages, compiles cleanly (a few minor overfull boxes).
- Every Coq identifier in the appendix ledger (36) was checked mechanically to
  exist and be closed under the global context.
- **Citations are from memory and must be verified** (`refs.bib`).
- Author block is a placeholder; the companion manuscript is cited as anonymous.
- The three figures are TikZ (the outline's Mermaid sketches were redrawn).
- Related work (section 14) is short and needs real engagement, especially with
  proof-relevant / groupoid-style treatments of rewriting and with provenance
  semirings; only the citations that were confidently recalled are included.

Two claims in the outline were changed to match what is actually proved
(see STATUS.md, "Paper-driven corrections"): witness identity/associativity hold
only modulo an explicit equivalence, and refuted verdicts no longer drop open
obligations from the *report*.
