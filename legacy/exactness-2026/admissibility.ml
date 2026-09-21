module type OBSERVATION = sig
  type state
  type obs
  val m         : state -> obs
  val phi       : state -> bool
  val obs_equal : obs -> obs -> bool
end

module Admissibility_check (O : OBSERVATION) = struct
  (* A factor table lists one representative of each observed value together
     with the predicate value on that fibre. It is a table for the factor on
     the image of M; off the image the factor is unconstrained, and
     [eval_factor] returns [None] there. *)
  type factor_table = (O.obs * bool) list

  type verdict =
    | MalformedCertificate of string
    | Inadmissible of O.state * O.state
    | Admissible of factor_table
    | NoWitnessFound

  let eval_factor (table : factor_table) (o : O.obs) : bool option =
    match List.find_opt (fun (o', _) -> O.obs_equal o o') table with
    | Some (_, b) -> Some b
    | None -> None

  (* Pre-check of what is checkable on the supplied data: [obs_equal] must be
     reflexive on every observed value and symmetric on the representatives.
     Transitivity is not checked directly; a failure that matters is caught
     when the factor table is verified. Completeness of [states] remains the
     caller's declaration and cannot be verified here. *)
  let precheck (image : O.obs list) (reps : O.obs list) : string option =
    if not (List.for_all (fun o -> O.obs_equal o o) image) then
      Some "obs_equal is not reflexive on the observed image"
    else if not (List.for_all (fun o1 -> List.for_all (fun o2 ->
               O.obs_equal o1 o2 = O.obs_equal o2 o1) reps) reps) then
      Some "obs_equal is not symmetric on the observed image"
    else None

  (* [complete] is the caller's declaration that [states] enumerates S
     exhaustively. The function cannot verify that declaration. *)
  let check ~(complete : bool) (states : O.state list) : verdict =
    let rec dedup = function
      | [] -> []
      | o :: rest -> if List.exists (O.obs_equal o) rest then dedup rest
                     else o :: dedup rest in
    let image = List.map O.m states in
    let reps = dedup image in
    match precheck image reps with
    | Some reason -> MalformedCertificate reason
    | None ->
        let fibre_of o = List.filter (fun s -> O.obs_equal (O.m s) o) states in
        let rec scan acc = function
          | [] -> `Constant (List.rev acc)
          | o :: rest ->
              (match fibre_of o with
               | [] -> scan acc rest
               | s0 :: tail ->
                   (match List.find_opt (fun s -> O.phi s <> O.phi s0) tail with
                    | Some s1 -> `Witness (s0, s1)
                    | None -> scan ((o, O.phi s0) :: acc) rest)) in
        (match scan [] reps with
         | `Witness (s0, s1) -> Inadmissible (s0, s1)
         | `Constant table ->
             if not complete then NoWitnessFound
             else
               (* Verify the positive certificate before returning it:
                  Phi s = factor (M s) for every enumerated state. *)
               if List.for_all (fun s -> eval_factor table (O.m s) = Some (O.phi s)) states
               then Admissible table
               else MalformedCertificate "factor table failed verification")
end
