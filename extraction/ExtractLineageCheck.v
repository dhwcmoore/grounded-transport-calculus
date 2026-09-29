(** Extraction of the CHECKED lineage audit (Debt/LineageCheck.v).

    Build (from the project root, after building the library):

      coqc -R legacy/exactness-2026 Exactness -R theories GTC -R examples GTCExamples \
           extraction/ExtractLineageCheck.v

    writes [lineage_check_extracted.ml(i)].  Proof fields vanish; the decision
    procedures and the certificate issuer remain.  See run_lineage_regression.sh
    for the comparison against the handwritten OCaml audit. *)

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From GTC.Debt Require Import Certificates LineageCheck.

Extraction Language OCaml.
Extraction "lineage_check_extracted.ml"
  lineage_check lineage_defect issue_certificate wf_defect
  ground_eq_a ground_eq_b descends_a descends_b check_L1
  distinguished_b undisclosed check_L3 ancestors.
