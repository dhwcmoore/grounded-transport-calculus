# Paper: Grounded Transport (LMCS)

Target: **Logical Methods in Computer Science**, official `lmcs.cls` (downloaded from
https://lmcs.episciences.org/public/lmcs.cls; re-download the current version before
submission, as the journal asks). Bibliography style `alphaurl`, as required.

    make          # builds paper.pdf (36 pages; limit 50)
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
4. **Mutation statement made exact** (Table 5): union 13/13; stratified alone 13/13;
   shallow 11/13; deep 8/13; random 12/13; fixed 5/13.
5. Author block and citation treatment; related work rewritten as a comparative
   argument against five technical neighbours; every reference verified at a
   primary source (Crossref, publisher/journal page, arXiv, W3C).

## Before submission
- **Confirm the e-mail address** in `paper.tex` (currently dhwcmoore@gmail.com).
- **The author's earlier manuscript** is cited as `moore2026` (unpublished). If it has
  no public preprint by submission, remove that bib entry and its four citations
  (sections 6, 8, 12); the theorem statements used are self-contained.
- LMCS requires an arXiv (CoRR) preprint with `cs.LO` among the subjects and the
  choice of one handling editor. `make arxiv` produces the source package.
- Archive the Coq artefact with a DOI and cite it.
- 120 Coq identifiers are cited; all exist and are axiom-free (the classical
  `constant_factors` is cited but excluded by design).
