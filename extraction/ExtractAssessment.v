(** Extraction check: evidence must SURVIVE extraction.

    Not part of [_CoqProject].  Build manually (from the project root, after
    building the library):

      coqc -R legacy/exactness-2026 Exactness -R theories GTC -R examples GTCExamples \
           extraction/ExtractAssessment.v

    It writes [assessment_extracted.ml]: the located obstructions, the lineage
    graph, custodians and coverage are all present as OCaml data; the proof
    fields are gone. *)

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From GTC.Debt Require Import Certificates TransportAssessment GroundedWitness.
From GTCExamples Require Import LineageCertificates CopiedCoordinates
  MaintenanceFailure DifferentWarrants.

Extraction Language OCaml.
Extraction "assessment_extracted.ml"
  copied_assessment copied_missing_lineage copied_partial_lineage
  failure_assessment open_assessment both_assessment certified_assessment
  witness_summary two_ev d0 d1 w1 w2 w3.
