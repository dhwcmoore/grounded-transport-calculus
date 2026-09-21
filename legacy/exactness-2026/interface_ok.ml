open Certified_temporal_seam

type t0
type t1
type t2

let e01 : (t0, t1) evolution =
  match certify
    (candidate_of_int_maps ~carrier:[0; 1]
       ~seam_map:(fun x -> x + 1)
       ~a_map:(fun x -> x + 1)
       ~b_map:(fun x -> x + 1)) with
  | Ok e -> e
  | Error _ -> failwith "certification failed"

let e12 : (t1, t2) evolution =
  match certify
    (candidate_of_int_maps ~carrier:[0; 1]
       ~seam_map:(fun x -> x + 1)
       ~a_map:(fun x -> x + 1)
       ~b_map:(fun x -> x + 1)) with
  | Ok e -> e
  | Error _ -> failwith "certification failed"

let () =
  let e02 = compose e01 e12 in
  ignore e02;
  (match certify
     (candidate_of_int_maps ~carrier:[0; 1]
        ~seam_map:(fun x -> x + 1)
        ~a_map:(fun x -> x + 1)
        ~b_map:(fun x -> x + 2)) with
   | Error (FwdSquareFailure r) ->
       Printf.printf "non-commuting evolution rejected at element %d\n" (witness_value r)
   | _ -> failwith "non-commuting evolution unexpectedly certified");
  (match certify_grounded
     (grounded_candidate_of_int_values ~carrier:[0; 1]
        ~phi_a:(fun r -> r = 0) ~phi_b:(fun r -> r = 0)
        ~phi_seam:(fun r -> r = 0)) with
   | Ok () -> print_endline "grounded candidate certified"
   | Error _ -> failwith "grounded candidate unexpectedly rejected");
  let copied = grounded_candidate_of_int_values
    ~carrier:[0; 1]
    ~phi_a:(fun _ -> true)
    ~phi_b:(fun _ -> true)
    ~phi_seam:(fun request_id -> request_id = 0) in
  match certify_grounded copied with
  | Error (GroundedAFailure r) ->
      Printf.printf "rejected at request %d\n" (witness_value r)
  | _ -> failwith "ungrounded transport unexpectedly certified"
