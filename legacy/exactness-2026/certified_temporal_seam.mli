type 't a
type 't b
type 't seam
type ('t, 'u) evolution
type ('t, 'u) candidate
type 't grounded_candidate
type seam_witness

val identity : ('t, 't) evolution
val compose : ('t, 'u) evolution -> ('u, 'v) evolution -> ('t, 'v) evolution
val evolve_seam : ('t, 'u) evolution -> 't seam -> 'u seam
val evolve_a : ('t, 'u) evolution -> 't a -> 'u a
val evolve_b : ('t, 'u) evolution -> 't b -> 'u b
val back : 't seam -> 't a
val fwd : 't seam -> 't b

type certification_error =
  | BackSquareFailure of seam_witness
  | FwdSquareFailure of seam_witness
  | GroundedAFailure of seam_witness
  | GroundedBFailure of seam_witness

val candidate_of_int_maps :
  carrier:int list -> seam_map:(int -> int) ->
  a_map:(int -> int) -> b_map:(int -> int) -> ('t, 'u) candidate
val grounded_candidate_of_int_values :
  carrier:int list -> phi_a:(int -> bool) -> phi_b:(int -> bool) ->
  phi_seam:(int -> bool) -> 't grounded_candidate
val witness_value : seam_witness -> int
val certify :
  ('t, 'u) candidate -> (('t, 'u) evolution, certification_error) result
val certify_grounded :
  't grounded_candidate -> (unit, certification_error) result
