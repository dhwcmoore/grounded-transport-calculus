(* Integrated case study: sales-tax jurisdiction through an address-schema
   migration. Uses Admissibility_check from admissibility.ml. *)
open Admissibility

(* ---------- The declared world ---------- *)
type goods = General | Food
type period = Before | After
type origin = Live | Backfill

let munis = List.init 10 (fun i -> i)
let zones = List.init 20 (fun i -> i)
let goods_all = [General; Food]
let periods = [Before; After]

let general_before = [|50; 55; 60; 65; 50; 70; 55; 60; 75; 45|]
let rate m g e =
  match g with
  | Food -> if m < 5 then 20 else 25
  | General ->
      (match e, m with
       | After, 3 -> 70
       | After, 7 -> 65
       | _ -> general_before.(m))

let primary z = z mod 10
let secondary z = match z with 2 -> Some 5 | 7 -> Some 8 | 13 -> Some 9 | 18 -> Some 1 | _ -> None
let munis_of z = primary z :: (match secondary z with Some m -> [m] | None -> [])

let rates = List.sort_uniq compare
  (List.concat_map (fun m -> List.concat_map (fun g -> List.map (rate m g) periods) goods_all) munis)

(* A static state: zone, delivery municipality, goods class, period, charged rate. *)
type st = { z : int; mu : int; g : goods; e : period; r : int }

let states =
  List.concat_map (fun z ->
  List.concat_map (fun mu ->
  List.concat_map (fun g ->
  List.concat_map (fun e ->
  List.map (fun r -> { z; mu; g; e; r }) rates) periods) goods_all) (munis_of z)) zones

(* Target claim: charged rate is the rate of the delivery municipality. *)
let phi s = s.r = rate s.mu s.g s.e
(* Old certified claim: charged rate equals the stage-t lookup table, which
   keys on zone and was issued before the rate change. *)
let lookup_stale z g = rate (primary z) g Before
let phi_old s = s.r = lookup_stale s.z s.g

(* ---------- Generic fibre statistics (same equality as the check) ---------- *)
let fibre_stats (m : 'a -> 'o) (p : 'a -> bool) (xs : 'a list) =
  let tbl = Hashtbl.create 1024 in
  List.iter (fun x ->
    let k = m x in
    let (t, f) = try Hashtbl.find tbl k with Not_found -> (0, 0) in
    Hashtbl.replace tbl k (if p x then (t + 1, f) else (t, f + 1))) xs;
  let fibres = Hashtbl.length tbl in
  let mixed = Hashtbl.fold (fun _ (t, f) acc -> if t > 0 && f > 0 then acc + 1 else acc) tbl 0 in
  (fibres, mixed)

let g_s = function General -> "general" | Food -> "food"
let e_s = function Before -> "before" | After -> "after"
let o_s = function Live -> "live" | Backfill -> "backfill"
let st_s s = Printf.sprintf "(z=%d,m=%d,%s,%s,r=%d)" s.z s.mu (g_s s.g) (e_s s.e) s.r

let report name (fib, mix) v show =
  Printf.printf "%-34s fibres=%4d mixed=%3d  " name fib mix;
  (match v with
   | `Adm n -> Printf.printf "Admissible; factor table %d entries, verified" n
   | `Malformed why -> Printf.printf "MalformedCertificate: %s" why
   | `Inadm (a, b) -> Printf.printf "Inadmissible; witness %s / %s" (show a) (show b)
   | `NWF -> print_string "NoWitnessFound");
  print_newline ()

(* ---------- Static checks ---------- *)
module Old_target = Admissibility_check (struct
  type state = st  type obs = int * goods * period * int
  let m s = (s.z, s.g, s.e, s.r)  let phi = phi  let obs_equal = ( = ) end)
module Old_cert = Admissibility_check (struct
  type state = st  type obs = int * goods * period * int
  let m s = (s.z, s.g, s.e, s.r)  let phi = phi_old  let obs_equal = ( = ) end)
module New_target = Admissibility_check (struct
  type state = st  type obs = int * goods * period * int
  let m s = (s.mu, s.g, s.e, s.r)  let phi = phi  let obs_equal = ( = ) end)

let conv_old = function Old_target.Admissible tb -> `Adm (List.length tb) | Old_target.NoWitnessFound -> `NWF
  | Old_target.Inadmissible (a, b) -> `Inadm (a, b) | Old_target.MalformedCertificate w -> `Malformed w
let conv_cert = function Old_cert.Admissible tb -> `Adm (List.length tb) | Old_cert.NoWitnessFound -> `NWF
  | Old_cert.Inadmissible (a, b) -> `Inadm (a, b) | Old_cert.MalformedCertificate w -> `Malformed w
let conv_new = function New_target.Admissible tb -> `Adm (List.length tb) | New_target.NoWitnessFound -> `NWF
  | New_target.Inadmissible (a, b) -> `Inadm (a, b) | New_target.MalformedCertificate w -> `Malformed w

(* ---------- Seam ---------- *)
type sigma = { s : st; o : origin; repaired : bool }
let m_new x = match x.o, x.repaired with
  | Live, _ -> x.s.mu            (* geocoded from the full address *)
  | Backfill, false -> primary x.s.z   (* derived from the old zone *)
  | Backfill, true -> x.s.mu     (* re-geocoded from retained free text *)
let phi_a x = phi_old x.s
let phi_b x = x.s.r = rate (m_new x) x.s.g x.s.e
let phi_sigma x = phi x.s        (* from the carrier delivery scan *)

let carrier repaired =
  List.concat_map (fun s -> [ { s; o = Live; repaired }; { s; o = Backfill; repaired } ]) states

let sig_s x = Printf.sprintf "%s[%s]" (st_s x.s) (o_s x.o)

let seam_counts repaired =
  let c = carrier repaired in
  let count p = List.length (List.filter p c) in
  let seamw x = phi_a x <> phi_b x in
  let groundw x = phi_a x <> phi_sigma x || phi_b x <> phi_sigma x in
  let copysig x = phi_a x = phi_b x && phi_b x <> phi_sigma x in
  let bwrong x = phi_b x <> phi_sigma x in
  Printf.printf "carrier=%d  seam_witnesses=%d  grounding_witnesses=%d  agree_but_ungrounded=%d  B_departs=%d\n"
    (List.length c) (count seamw) (count groundw) (count copysig) (count bwrong);
  List.iter (fun o ->
    Printf.printf "   %-8s seam=%3d grounding=%3d agree_but_ungrounded=%3d B_departs=%3d A_departs=%3d\n" (o_s o)
      (count (fun x -> x.o = o && seamw x)) (count (fun x -> x.o = o && groundw x))
      (count (fun x -> x.o = o && copysig x)) (count (fun x -> x.o = o && bwrong x))
      (count (fun x -> x.o = o && phi_a x <> phi_sigma x))) [Live; Backfill];
  (match List.find_opt copysig c with
   | Some x -> Printf.printf "   first agree_but_ungrounded: %s  A=%b B=%b Sigma=%b\n" (sig_s x) (phi_a x) (phi_b x) (phi_sigma x)
   | None -> print_endline "   no agree_but_ungrounded element");
  (match List.find_opt (fun x -> copysig x && phi_sigma x) c with
   | Some x -> Printf.printf "   agree-false-but-true example: %s  A=%b B=%b Sigma=%b\n" (sig_s x) (phi_a x) (phi_b x) (phi_sigma x)
   | None -> ())

(* Translation O_t -> O_{t+1} on the seam: the new municipality field must be
   a function of the old observation. Checked indicator by indicator. *)
let translation_check label xs =
  let rec go = function
    | [] -> Printf.printf "%-34s translation exists on declared subset (|D|=%d)\n" label (List.length xs)
    | k :: rest ->
        let module T = Admissibility_check (struct
          type state = sigma  type obs = int * goods * period * int
          let m x = (x.s.z, x.s.g, x.s.e, x.s.r)
          let phi x = m_new x = k  let obs_equal = ( = ) end) in
        (match T.check ~complete:true xs with
         | T.Inadmissible (a, b) ->
             Printf.printf "%-34s no translation; witness %s -> m_new=%d / %s -> m_new=%d\n" label
               (sig_s a) (m_new a) (sig_s b) (m_new b)
         | T.MalformedCertificate w ->
             Printf.printf "%-34s MalformedCertificate: %s\n" label w
         | T.Admissible _ | T.NoWitnessFound -> go rest) in
  go munis

(* Exhibition condition (iii): is phi_sigma a function of what a seam record
   retains?  Record retaining (zone, m_new, goods, period, rate, origin). *)
module Record_without_scan = Admissibility_check (struct
  type state = sigma  type obs = int * int * goods * period * int * origin
  let m x = (x.s.z, m_new x, x.s.g, x.s.e, x.s.r, x.o)
  let phi = phi_sigma  let obs_equal = ( = ) end)

(* ---------- Lineage audit of a claimed ground (Definition 12) ---------- *)
(* A lineage record declares derived fields with their parents, the raw
   inputs, which of them are claim-relevant, the three distinguished nodes,
   and a disposition for each shared non-raw ancestor of the coordinates. *)
type disposition = Justified of string | Open_defeater of string

type lineage = {
  derived : (string * string list) list;   (* derived field, its parents *)
  raw : string list;                        (* raw inputs: no parents *)
  claim_relevant : string list;             (* subset of raw *)
  d_a : string; d_b : string; ground : string;   (* coordinate and seam nodes *)
  dispositions : (string * disposition) list;
}

let parents l n = try List.assoc n l.derived with Not_found -> []

(* Well-formedness: unique names, raw inputs are not derived, every parent is
   declared, the distinguished nodes exist, claim-relevant inputs are raw,
   and the graph is acyclic. Returns the first defect found. *)
let well_formed l =
  let names = List.map fst l.derived @ l.raw in
  let declared n = List.mem n names in
  let rec dup = function [] -> None | x :: r -> if List.mem x r then Some x else dup r in
  match dup names with
  | Some n -> Some ("duplicate node " ^ n)
  | None ->
  match List.find_opt (fun (_, ps) -> List.exists (fun p -> not (declared p)) ps) l.derived with
  | Some (n, _) -> Some ("undeclared parent of " ^ n)
  | None ->
  match List.find_opt (fun n -> not (List.mem_assoc n l.derived)) [l.d_a; l.d_b; l.ground] with
  | Some n -> Some ("distinguished node not derived: " ^ n)
  | None ->
  match List.find_opt (fun n -> not (List.mem n l.raw)) l.claim_relevant with
  | Some n -> Some ("claim-relevant input not raw: " ^ n)
  | None ->
    (* depth-first search with colours; grey on the stack, black finished *)
    let colour = Hashtbl.create 32 in
    let rec visit n =
      match Hashtbl.find_opt colour n with
      | Some `Grey -> Some n
      | Some `Black -> None
      | None ->
          Hashtbl.replace colour n `Grey;
          let r = List.fold_left (fun acc p -> match acc with
                    | Some _ -> acc | None -> visit p) None (parents l n) in
          Hashtbl.replace colour n `Black; r in
    (match List.fold_left (fun acc n -> match acc with
             | Some _ -> acc | None -> visit n) None names with
     | Some n -> Some ("cycle through " ^ n)
     | None -> None)

(* Strict ancestors, computed with a visited set (terminates on any graph). *)
let ancestors l n =
  let seen = Hashtbl.create 32 in
  let rec go = function
    | [] -> ()
    | x :: rest ->
        if Hashtbl.mem seen x then go rest
        else (Hashtbl.replace seen x (); go (parents l x @ rest)) in
  go (parents l n);
  List.sort compare (Hashtbl.fold (fun k () acc -> k :: acc) seen [])

let pf b = if b then "pass" else "FAIL"

let audit label l =
  match well_formed l with
  | Some defect ->
      Printf.printf "%-28s MalformedLineage: %s\n" label defect
  | None ->
      let a_anc = ancestors l l.d_a and b_anc = ancestors l l.d_b in
      let g_anc = ancestors l l.ground in
      (* L1: the seam valuation descends from neither coordinate *)
      let l1 = not (List.mem l.d_a g_anc || List.mem l.d_b g_anc) in
      (* L2: shared non-raw ancestry, each entry with a disposition *)
      let shared = List.filter (fun n -> List.mem n b_anc && not (List.mem n l.raw)) a_anc in
      let undisposed = List.filter (fun n -> not (List.mem_assoc n l.dispositions)) shared in
      let l2 = undisposed = [] in
      let disp n = match List.assoc_opt n l.dispositions with
        | Some (Justified _) -> n ^ ":justified"
        | Some (Open_defeater _) -> n ^ ":open-defeater"
        | None -> n ^ ":UNDISCLOSED" in
      (* L3: ground-only ancestry contains a claim-relevant raw input *)
      let ground_only = List.filter (fun n ->
          not (List.mem n a_anc) && not (List.mem n b_anc) && n <> l.d_a && n <> l.d_b) g_anc in
      let relevant = List.filter (fun n -> List.mem n l.claim_relevant) ground_only in
      let l3 = relevant <> [] in
      Printf.printf "%-28s L1 %s; L2 %s shared=[%s]; L3 %s ground-only=[%s] claim-relevant raw=[%s]; lineage-grounded=%b\n"
        label (pf l1) (pf l2) (String.concat "; " (List.map disp shared))
        (pf l3) (String.concat "; " ground_only) (String.concat "; " relevant) (l1 && l2 && l3)

let raw_inputs = ["address_text"; "rate_charged"; "goods"; "period"; "delivery_event"; "table_v1"; "table_v2"]
let claim_relevant_inputs = ["delivery_event"; "rate_charged"; "goods"; "period"; "table_v2"]

let derived_backfill = [
  "zone", ["address_text"];
  "flag_old", ["zone"; "table_v1"; "rate_charged"; "goods"];
  "primary_map", ["zone"];
  "m_new", ["primary_map"];
  "flag_new", ["m_new"; "table_v2"; "rate_charged"; "goods"; "period"];
  "carrier_scan", ["delivery_event"];
  "m_delivered", ["carrier_scan"];
  "phi_seam", ["m_delivered"; "table_v2"; "rate_charged"; "goods"; "period"] ]

let base derived dispositions = {
  derived; raw = raw_inputs; claim_relevant = claim_relevant_inputs;
  d_a = "flag_old"; d_b = "flag_new"; ground = "phi_seam"; dispositions }

let zone_defeater =
  ["zone", Open_defeater "new municipality derived from the old zone via the primary-municipality map"]

let lineage_live =
  base (("geocoder", ["address_text"]) ::
        List.map (fun (n, ps) -> if n = "m_new" then ("m_new", ["geocoder"]) else (n, ps))
          derived_backfill) []
let lineage_backfill = base derived_backfill zone_defeater
let lineage_backfill_undisclosed = base derived_backfill []
let lineage_copied_ground =
  base (List.map (fun (n, ps) -> if n = "phi_seam" then ("phi_seam", ["flag_old"]) else (n, ps))
          derived_backfill) zone_defeater
(* Malformed record: a declared cycle between the zone and the new field. *)
let lineage_cyclic =
  base (List.map (fun (n, ps) -> if n = "zone" then ("zone", ["address_text"; "m_new"]) else (n, ps))
          derived_backfill) zone_defeater

let () =
  Printf.printf "|S| = %d, |rates| = %d, zones = %d, municipalities = %d\n"
    (List.length states) (List.length rates) (List.length zones) (List.length munis);
  Printf.printf "phi holds on %d states; phi_old holds on %d; they differ on %d\n"
    (List.length (List.filter phi states)) (List.length (List.filter phi_old states))
    (List.length (List.filter (fun s -> phi s <> phi_old s) states));
  let split s = s.mu <> primary s.z in
  let stale s = s.g = General && s.e = After && (primary s.z = 3 || primary s.z = 7) && not (split s) in
  let diff = List.filter (fun s -> phi s <> phi_old s) states in
  Printf.printf "   of which split-zone (secondary municipality): %d; stale-table (primary municipality 3 or 7, general, after): %d; other: %d\n"
    (List.length (List.filter split diff)) (List.length (List.filter stale diff))
    (List.length (List.filter (fun s -> not (split s) && not (stale s)) diff));
  Printf.printf "   stale-table states in single-municipality zones: %d\n"
    (List.length (List.filter (fun s -> stale s && secondary s.z = None) diff));
  print_endline "--- static ---";
  report "phi on M_t = (zone,g,e,r)" (fibre_stats (fun s -> (s.z, s.g, s.e, s.r)) phi states)
    (conv_old (Old_target.check ~complete:true states)) st_s;
  report "phi_old on M_t" (fibre_stats (fun s -> (s.z, s.g, s.e, s.r)) phi_old states)
    (conv_cert (Old_cert.check ~complete:true states)) st_s;
  report "phi on M_t+1 = (m,g,e,r)" (fibre_stats (fun s -> (s.mu, s.g, s.e, s.r)) phi states)
    (conv_new (New_target.check ~complete:true states)) st_s;
  let unsplit = List.filter (fun s -> secondary s.z = None) states in
  report "phi on M_t, unsplit zones, sample" (fibre_stats (fun s -> (s.z, s.g, s.e, s.r)) phi unsplit)
    (conv_old (Old_target.check ~complete:false unsplit)) st_s;
  let refined = fibre_stats (fun s -> (s.z, s.g, s.e, s.r, phi s)) phi states in
  Printf.printf "kernel of <M_t, phi>: %d blocks; M_t+1: %d blocks\n" (fst refined)
    (fst (fibre_stats (fun s -> (s.mu, s.g, s.e, s.r)) phi states));
  print_endline "--- seam, as migrated (backfill derives municipality from zone) ---";
  seam_counts false;
  print_endline "--- seam, repaired (backfill re-geocodes retained address text) ---";
  seam_counts true;
  print_endline "--- translation ---";
  let c = carrier false in
  translation_check "whole carrier" c;
  translation_check "backfill rows only" (List.filter (fun x -> x.o = Backfill) c);
  translation_check "live rows only" (List.filter (fun x -> x.o = Live) c);
  print_endline "--- exhibition condition (iii) ---";
  (match Record_without_scan.check ~complete:true c with
   | Record_without_scan.Inadmissible (a, b) ->
       Printf.printf "record without delivery scan: phi_sigma not determined; witness %s / %s\n" (sig_s a) (sig_s b)
   | Record_without_scan.Admissible _ -> print_endline "record without scan determines phi_sigma"
   | Record_without_scan.MalformedCertificate w -> print_endline ("MalformedCertificate: " ^ w)
   | Record_without_scan.NoWitnessFound -> print_endline "NoWitnessFound");
  print_endline "--- lineage audit ---";
  audit "live rows" lineage_live;
  audit "backfill rows" lineage_backfill;
  audit "backfill, zone undisclosed" lineage_backfill_undisclosed;
  audit "copied seam valuation" lineage_copied_ground;
  audit "cyclic record" lineage_cyclic
