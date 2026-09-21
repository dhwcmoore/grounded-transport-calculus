(* Extraction of the two runtime decision procedures used by the sealed
   OCaml interface (certified_temporal_seam.ml). Their correctness is stated
   by squares_bool_reflect and grounding_bool_reflect in GroundedSeam.v.
   Trusted in this step: the Coq extraction mechanism and the realisation of
   nat as OCaml int (ExtrOcamlNatInt), which is exact for the small
   non-negative identifiers used here. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From Exactness Require Import GroundedSeam.

Extraction Language OCaml.
Extraction "seam_checks.ml" squares_bool grounding_bool.
