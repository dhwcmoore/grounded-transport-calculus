# Paper: Grounded Transport (bundled historical LMCS layout)

This directory reproduces the historical LMCS manuscript with `lmcs.cls` and
`alphaurl`. The current intended venue is **Journal of Logic and Computation**.
The revised standalone submission source is a separate manuscript and must be
formatted and rebuilt independently; an LMCS page count is not a JLC count.

    make          # 39 pages in the repaired bundled layout (2026-10-02)
    make arxiv    # builds arxiv-source.tar.gz and test-compiles it from a clean directory
    make clean

Layout: `paper.tex` (class, macros, abstract, metadata), `sections/NN-*.tex`,
`sections/appendix-ledger.tex` (theorem spine with proof status), `refs.bib`,
`archive/draft1/` (the earlier article-class draft).

## Structure
1 Introduction. 2 Minimal separating example. 3 Preliminaries.
Formal core: 4 Grounded transport (incl. 4.4 contexts at two levels).
5 Evidential erasure (incl. Prop. 5.7, the observational obstruction).
6 The grounded-seam instance. 7 Dynamic preservation and failure (incl. Thm 7.3,
certificate reissue and its impossibility). 8 Evidence-bearing assessment.
9 Certified lineage checking. 10 Mechanisation and regression evidence.
11 Related work. 12 Discussion and limitations. 13 Conclusion. Appendix: ledger.

## Changes in this revision (response to review)
1. **Contexts at two levels.** `CrossingProper` (crossings only, with an action on
   crossed seam elements) and `CertificateProper` (complete certified witnesses,
   commuting with the first erasure up to that action), with composition at both
   levels, the chain certificate-proper => crossing-proper => Proper, and problem
   morphisms with an EVIDENCE LIFT giving certificate-proper instances. Seam
   evolutions are crossing-proper; certificate-proper only under a lift, which exists
   in one model (reissue) and provably cannot in the other.
2. **`Transportable` bridges.** `TransportableFull` = `TransportableLegacy` + an
   extra authority conjunct, so it is strictly stronger; refuting it does not refute
   the legacy instantiation. Proved: every non-institutional failure refutes the
   legacy instantiation; an institutional failure refutes only the authority conjunct.
3. **Deep-ancestry test populations** (six, 300 graphs each) and two more saturation
   mutants. The shallow populations missed M12/M13; the deep ones kill both.
4. **Current mutation statement** (Table 5): union 17/17; stratified alone 13/17;
   shallow 11/17; deep 8/17; random 12/17; fixed 5/17; edge 4/17.
   Only the edge suite detects M14--M17.
5. Author block and citation treatment; related work rewritten as a comparative
   argument against five technical neighbours; every reference verified at a
   primary source (Crossref, publisher/journal page, arXiv, W3C).

## Before submission
- Confirm the corresponding author's contact details in the final source.
- Keep self-citation titles and publication status accurate. Unpublished
  manuscripts may be described as such; no public preprint or publication
  status should be invented.
- JLC's current guidelines request a PDF and a covering message:
  https://academic.oup.com/logcom/pages/General_Instructions.
  They do not specify a mandatory LaTeX class for initial submission.
- Archive the pinned artefact with a persistent identifier, verify public
  retrieval, and insert the exact identifier and manifest digest.
- The merged manuscript cites 123 non-classical Coq identifiers, plus the
  isolated classical `constant_factors`. The latter is not in the axiom-free
  main dependency closure. See the fresh assumption audit for the exact list.

The merged milestone reported 38 pages. After these documentation repairs,
the bundled LMCS layout freshly builds to 39 pages with the CTAN `alphaurl.bst`
from urlbst 0.9.1. This is not the standalone V17 or a JLC submission count.

The tracked `paper.pdf` remains the historical milestone PDF. The repaired
source build is recorded separately; neither PDF is the missing revised
standalone submission manuscript. `alphaurl.bst` is a LaTeX dependency,
available from CTAN urlbst; it is not a new project theorem or source pin.
