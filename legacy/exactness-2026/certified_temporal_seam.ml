type 't a = int
type 't b = int
type 't seam = int
type ('t, 'u) evolution = {
  es : int -> int;
  ea : int -> int;
  eb : int -> int;
}
type ('t, 'u) candidate = {
  carrier : int list;
  cs : int -> int;
  ca : int -> int;
  cb : int -> int;
}
type 't grounded_candidate = {
  gcarrier : int list;
  phi_a : int -> bool;
  phi_b : int -> bool;
  phi_seam : int -> bool;
}
type seam_witness = int

let identity = { es = (fun x -> x); ea = (fun x -> x); eb = (fun x -> x) }

let compose e1 e2 = {
  es = (fun r -> e2.es (e1.es r));
  ea = (fun a -> e2.ea (e1.ea a));
  eb = (fun b -> e2.eb (e1.eb b));
}

let evolve_seam e = e.es
let evolve_a e = e.ea
let evolve_b e = e.eb
let back x = x
let fwd x = x

type certification_error =
  | BackSquareFailure of seam_witness
  | FwdSquareFailure of seam_witness
  | GroundedAFailure of seam_witness
  | GroundedBFailure of seam_witness

let candidate_of_int_maps ~carrier ~seam_map ~a_map ~b_map =
  { carrier; cs = seam_map; ca = a_map; cb = b_map }

let grounded_candidate_of_int_values ~carrier ~phi_a ~phi_b ~phi_seam =
  { gcarrier = carrier; phi_a; phi_b; phi_seam }

let witness_value x = x

(* The accept/reject decision in [certify] and [certify_grounded] is made by
   procedures extracted from GroundedSeam.v (see SeamExtraction.v), whose
   correctness is stated by squares_bool_reflect and grounding_bool_reflect.
   The witness searches below are diagnostics run only after the extracted
   procedure has rejected; they do not decide acceptance. The record type,
   identity, and composition are a hand-written realisation of the Coq
   SeamEvolution record and are trusted, not extracted. *)
let id_int (x : int) = x

let certify c =
  if Seam_checks.squares_bool c.carrier id_int id_int id_int id_int c.cs c.ca c.cb
  then Ok { es = c.cs; ea = c.ca; eb = c.cb }
  else
    match List.find_opt (fun r -> c.cs r <> c.ca r) c.carrier with
    | Some r -> Error (BackSquareFailure r)
    | None ->
        (match List.find_opt (fun r -> c.cs r <> c.cb r) c.carrier with
         | Some r -> Error (FwdSquareFailure r)
         | None -> failwith "extracted square check rejected without a witness")

let certify_grounded c =
  if Seam_checks.grounding_bool c.gcarrier id_int id_int c.phi_a c.phi_b c.phi_seam
  then Ok ()
  else
    match List.find_opt (fun r -> c.phi_a r <> c.phi_seam r) c.gcarrier with
    | Some r -> Error (GroundedAFailure r)
    | None ->
        (match List.find_opt (fun r -> c.phi_b r <> c.phi_seam r) c.gcarrier with
         | Some r -> Error (GroundedBFailure r)
         | None -> failwith "extracted grounding check rejected without a witness")
