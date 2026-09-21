(* Section 14 worked examples: tenant isolation, pressure telemetry, and
   composition of certified services. Uses Admissibility_check from
   admissibility.ml. *)
open Admissibility

let fibre_stats (m : 'a -> 'o) (p : 'a -> bool) (xs : 'a list) =
  let tbl = Hashtbl.create 64 in
  List.iter (fun x ->
    let k = m x in
    let (t, f) = try Hashtbl.find tbl k with Not_found -> (0, 0) in
    Hashtbl.replace tbl k (if p x then (t + 1, f) else (t, f + 1))) xs;
  let fibres = Hashtbl.length tbl in
  let mixed = Hashtbl.fold (fun _ (t, f) acc -> if t > 0 && f > 0 then acc + 1 else acc) tbl 0 in
  (fibres, mixed)

(* Run the generic checker for surface [m] and predicate [p]. *)
let run (type s) (type o) name ~complete (m : s -> o) (p : s -> bool) (xs : s list)
    (show : s -> string) =
  let module C = Admissibility_check (struct
    type state = s  type obs = o
    let m = m  let phi = p  let obs_equal = ( = ) end) in
  let (fib, mix) = fibre_stats m p xs in
  Printf.printf "%-40s fibres=%3d mixed=%2d  " name fib mix;
  (match C.check ~complete xs with
   | C.Admissible table ->
       Printf.printf "Admissible; factor table %d entries, verified" (List.length table)
   | C.MalformedCertificate why -> Printf.printf "MalformedCertificate: %s" why
   | C.NoWitnessFound -> print_string "NoWitnessFound"
   | C.Inadmissible (a, b) -> Printf.printf "Inadmissible; witness %s / %s" (show a) (show b));
  print_newline ()

let count p xs = List.length (List.filter p xs)

(* ---------- Tenant isolation ---------- *)
type tenant = A | B
type path = Direct | Admin
let t_s = function A -> "a" | B -> "b"
let p_s = function Direct -> "direct" | Admin -> "admin"
type ts = { c : tenant; o : tenant; path : path }
let tenant_states =
  List.concat_map (fun c -> List.concat_map (fun o ->
    List.map (fun path -> { c; o; path }) [Direct; Admin]) [A; B]) [A; B]
(* The direct path enforces ownership; the administrative path does not. *)
let code s = match s.path with Direct -> if s.c = s.o then 200 else 403 | Admin -> 200
let phi_tenant s = code s = 403 || s.c = s.o
let ts_s s = Printf.sprintf "(%s,%s,%s)" (t_s s.c) (t_s s.o) (p_s s.path)

(* ---------- Pressure telemetry ---------- *)
let levels = [0; 1; 2; 3]
let windows =
  List.concat_map (fun x -> List.concat_map (fun y -> List.map (fun z -> (x, y, z)) levels) levels) levels
let phi_env (x, y, z) = x <= 2 && y <= 2 && z <= 2
let w_s (x, y, z) = Printf.sprintf "(%d,%d,%d)" x y z
let sum (x, y, z) = x + y + z
let mx (x, y, z) = max x (max y z)

(* ---------- Composition of certified services ---------- *)
type tok = Tok of tenant | NoTok
let k_s = function Tok t -> t_s t | NoTok -> "none"
type cs = { cc : tenant; oo : tenant; d : bool; k : tok }
let comp_states =
  List.concat_map (fun cc -> List.concat_map (fun oo -> List.concat_map (fun d ->
    List.map (fun k -> { cc; oo; d; k }) [Tok A; Tok B; NoTok]) [false; true]) [A; B]) [A; B]
let cs_s s = Printf.sprintf "(%s,%s,%b,%s)" (t_s s.cc) (t_s s.oo) s.d (k_s s.k)
let returned s = s.cc = s.oo || s.d
let phi1 s = s.cc = s.oo || s.d                        (* gateway check *)
let phi2 s = (not s.d) || s.k <> NoTok                 (* token check *)
let psi s = (not (returned s && s.cc <> s.oo)) || (s.d && s.k = Tok s.oo)
(* Repair: token-boundary obligation over caller, owner, and token. *)
let phi3 s = s.cc = s.oo || s.k = Tok s.oo
(* Alternative that needs only the owner at the token boundary. *)
let phi3_owner_only s = (not s.d) || s.k = Tok s.oo

let () =
  print_endline "--- tenant isolation ---";
  Printf.printf "|S| = %d\n" (List.length tenant_states);
  run "phi on M1 = (code,c)" ~complete:true (fun s -> (code s, s.c)) phi_tenant tenant_states ts_s;
  run "phi on (code,c,path)" ~complete:true (fun s -> (code s, s.c, s.path)) phi_tenant tenant_states ts_s;
  run "phi on M2 = (code,c,o)" ~complete:true (fun s -> (code s, s.c, s.o)) phi_tenant tenant_states ts_s;
  let sample = List.filter (fun s -> s.c = s.o) tenant_states in
  run "phi on M1, c=o sample (incomplete)" ~complete:false (fun s -> (code s, s.c)) phi_tenant sample ts_s;
  Printf.printf "kernel of <M1, phi>: %d blocks\n"
    (fst (fibre_stats (fun s -> (code s, s.c, phi_tenant s)) phi_tenant tenant_states));
  print_endline "--- pressure telemetry ---";
  Printf.printf "|S| = %d; phi holds on %d\n" (List.length windows) (count phi_env windows);
  run "phi on raw window" ~complete:true (fun w -> w) phi_env windows w_s;
  run "phi on M_sum" ~complete:true sum phi_env windows w_s;
  run "phi on (sum,max)" ~complete:true (fun w -> (sum w, mx w)) phi_env windows w_s;
  Printf.printf "kernel of <M_sum, phi>: %d blocks\n"
    (fst (fibre_stats (fun w -> (sum w, phi_env w)) phi_env windows));
  print_endline "--- composition ---";
  Printf.printf "|S| = %d; phi1 holds on %d; phi2 holds on %d; phi3 holds on %d; psi fails on %d\n"
    (List.length comp_states) (count phi1 comp_states) (count phi2 comp_states)
    (count phi3 comp_states) (count (fun s -> not (psi s)) comp_states);
  run "phi1 on M_G = (c,o,d)" ~complete:true (fun s -> (s.cc, s.oo, s.d)) phi1 comp_states cs_s;
  run "phi2 on M_T = (d,k)" ~complete:true (fun s -> (s.d, s.k)) phi2 comp_states cs_s;
  run "psi on M_G x M_T" ~complete:true (fun s -> (s.cc, s.oo, s.d, s.k)) psi comp_states cs_s;
  run "psi on C = <phi1,phi2>" ~complete:true (fun s -> (phi1 s, phi2 s)) psi comp_states cs_s;
  run "psi on C' = <phi1,phi2,phi3>" ~complete:true (fun s -> (phi1 s, phi2 s, phi3 s)) psi comp_states cs_s;
  Printf.printf "psi = not phi1 or phi3 on every state: %b\n"
    (List.for_all (fun s -> psi s = ((not (phi1 s)) || phi3 s)) comp_states);
  Printf.printf "phi3 = psi on every state: %b; states where phi3 fails and psi holds: %d\n"
    (List.for_all (fun s -> phi3 s = psi s) comp_states)
    (count (fun s -> psi s && not (phi3 s)) comp_states);
  run "psi on <phi1,phi2,owner-only token>" ~complete:true
    (fun s -> (phi1 s, phi2 s, phi3_owner_only s)) psi comp_states cs_s;
  print_endline "--- pre-check ---";
  (* An observational equality that is not reflexive is rejected before any
     factorisation verdict is issued. *)
  let module Bad = Admissibility_check (struct
    type state = int * int * int  type obs = int
    let m = sum  let phi = phi_env  let obs_equal a b = a = b && a <> 4 end) in
  (match Bad.check ~complete:true windows with
   | Bad.MalformedCertificate why -> Printf.printf "non-reflexive obs_equal: MalformedCertificate: %s\n" why
   | _ -> failwith "malformed equality unexpectedly accepted")
