(* Regression / differential test: the EXTRACTED, PROVED lineage checker
   against the HANDWRITTEN OCaml audit in legacy/exactness-2026/jurisdiction.ml.

   1. The five case-study records: compared with the recorded output.
   2. Random records: compared with the handwritten [Jurisdiction.audit], whose
      printed line is captured from stdout.  Malformed records are included.

   This is a TEST, not a theorem: agreement on these inputs, not equivalence.
   Build/run: run_lineage_regression.sh. *)

module C = Lineage_check_extracted
module J = Jurisdiction

(* every stage runs; the process fails at the end if any stage disagreed, so a
   mutation can be attributed to the populations that detect it *)
let failed = ref false

(* ---- names to numbers ---- *)
let intern_tbl : (string, int) Hashtbl.t = Hashtbl.create 64
let intern s =
  match Hashtbl.find_opt intern_tbl s with
  | Some i -> i
  | None -> let i = Hashtbl.length intern_tbl in Hashtbl.add intern_tbl s i; i

let to_coq (l : J.lineage) : C.lineage =
  Hashtbl.reset intern_tbl;
  let derived = List.map (fun (n, ps) -> (intern n, List.map intern ps)) l.J.derived in
  let raw = List.map intern l.J.raw in
  let relevant = List.map intern l.J.claim_relevant in
  let disp = List.map (fun (n, d) ->
      (intern n, match d with J.Justified _ -> C.Justified 0 | J.Open_defeater _ -> C.OpenDefeater 0))
      l.J.dispositions in
  { C.lin_derived = derived; lin_raw = raw; lin_relevant = relevant;
    lin_dA = intern l.J.d_a; lin_dB = intern l.J.d_b; lin_ground = intern l.J.ground;
    lin_dispositions = disp }

(* ---- normalised verdicts ---- *)
type verdict =
  | Malformed of string                     (* defect kind *)
  | Flags of bool * bool * bool * bool      (* L1, L2, L3, lineage-grounded *)

let show = function
  | Malformed k -> "Malformed:" ^ k
  | Flags (a, b, c, g) -> Printf.sprintf "L1=%b L2=%b L3=%b grounded=%b" a b c g

let extracted (l : J.lineage) : verdict =
  let g = to_coq l in
  match C.wf_defect g with
  | Some C.DuplicateNode -> Malformed "duplicate"
  | Some C.UndeclaredParent -> Malformed "undeclared"
  | Some C.DistinguishedNotDerived -> Malformed "distinguished"
  | Some C.RelevantNotRaw -> Malformed "relevant"
  | Some (C.Cycle _) -> Malformed "cycle"
  | None ->
      let l1 = C.check_L1 g in
      let l2 = (C.undisclosed g = None) in
      let l3 = C.check_L3 g in
      let grounded = (C.lineage_defect g = None) in
      Flags (l1, l2, l3, grounded)

(* ---- parse the handwritten audit's printed line ---- *)
let contains s sub =
  let n = String.length s and m = String.length sub in
  let rec go i = i + m <= n && (String.sub s i m = sub || go (i + 1)) in
  go 0

let kind_of_defect line =
  if contains line "duplicate node" then "duplicate"
  else if contains line "undeclared parent" then "undeclared"
  else if contains line "distinguished node not derived" then "distinguished"
  else if contains line "claim-relevant input not raw" then "relevant"
  else if contains line "cycle through" then "cycle"
  else "other:" ^ line

let parse_line line : verdict =
  if contains line "MalformedLineage" then Malformed (kind_of_defect line)
  else
    let flag tag = contains line (tag ^ " pass") in
    Flags (flag "L1", flag "L2", flag "L3", contains line "lineage-grounded=true")

(* capture what [Jurisdiction.audit] prints, by redirecting stdout to a file *)
let handwritten (l : J.lineage) : verdict =
  let tmp = Filename.temp_file "audit" ".txt" in
  flush stdout;
  let saved = Unix.dup Unix.stdout in
  let fd = Unix.openfile tmp [Unix.O_WRONLY; Unix.O_TRUNC] 0o600 in
  Unix.dup2 fd Unix.stdout; Unix.close fd;
  J.audit "x" l;
  flush stdout;
  Unix.dup2 saved Unix.stdout; Unix.close saved;
  let ic = open_in tmp in
  let line = input_line ic in
  close_in ic; Sys.remove tmp;
  parse_line line

(* The handwritten audit implements the pre-v6 specification.
   Differential comparison is authoritative only where that specification and
   v6 have the same semantics.

   They intentionally diverge when:
   - ground = d_A or ground = d_B; or
   - ground is a directly raw, non-derived node.

   Outside this domain we test the v6 checker against explicit v6 expectations,
   not against the frozen handwritten audit. *)
let is_derived_name (l : J.lineage) n =
  List.exists (fun (m, _) -> m = n) l.J.derived

let is_raw_name (l : J.lineage) n =
  List.mem n l.J.raw

let legacy_overlap (l : J.lineage) =
  l.J.ground <> l.J.d_a &&
  l.J.ground <> l.J.d_b &&
  not (is_raw_name l l.J.ground &&
       not (is_derived_name l l.J.ground))

(* ---- 1. the five case-study records ---- *)
let () =
  print_endline "=== extracted lineage checker vs handwritten audit ===";
  let cases = [ "live rows", J.lineage_live; "backfill rows", J.lineage_backfill;
                "backfill, zone undisclosed", J.lineage_backfill_undisclosed;
                "copied seam valuation", J.lineage_copied_ground;
                "cyclic record", J.lineage_cyclic ] in
  let bad = ref 0 in
  List.iter (fun (name, l) ->
      let e = extracted l and h = handwritten l in
      let ok = e = h in
      if not ok then incr bad;
      Printf.printf "%-28s extracted: %-38s handwritten: %-38s %s\n" name (show e) (show h)
        (if ok then "AGREE" else "DISAGREE")) cases;
  Printf.printf "case study: %d/%d agree\n" (List.length cases - !bad) (List.length cases);
  if !bad > 0 then failed := true

(* ---- 2. random differential test ---- *)
let () =
  Random.init 20260921;
  let pick l = List.nth l (Random.int (List.length l)) in
  let gen () : J.lineage =
    let nraw = 1 + Random.int 4 and nder = 3 + Random.int 6 in
    let raw = List.init nraw (fun i -> Printf.sprintf "r%d" i) in
    let der = List.init nder (fun i -> Printf.sprintf "d%d" i) in
    let all = raw @ der in
    let undeclared = "ghost" in
    let derived = List.map (fun n ->
        let k = Random.int 4 in
        let parents = List.init k (fun _ ->
            (* mostly earlier nodes (acyclic), sometimes any node (possible cycle),
               rarely an undeclared node *)
            let r = Random.int 20 in
            if r = 0 then undeclared
            else if r <= 2 then pick all
            else
              let idx = try List.assoc n (List.mapi (fun i x -> (x, i)) der) with Not_found -> 0 in
              pick (raw @ List.filteri (fun i _ -> i < idx) der)) in
        (n, parents)) der in
    let derived = if Random.int 30 = 0 then derived @ [List.hd derived] else derived in
    let relevant = List.filter (fun _ -> Random.bool ()) raw in
    let relevant = if Random.int 25 = 0 then "d0" :: relevant else relevant in
    let pd () = if Random.int 40 = 0 then List.hd raw else pick der in
    let dispositions = List.filter_map (fun n ->
        if Random.int 3 = 0 then Some (n, if Random.bool () then J.Justified "j" else J.Open_defeater "o")
        else None) der in
    { J.derived = derived; raw; claim_relevant = relevant;
      d_a = pd (); d_b = pd (); ground = pd (); dispositions } in
  let n = 3000
  and compared = ref 0
  and skipped = ref 0
  and bad = ref 0
  and counts = Hashtbl.create 8 in
  for _ = 1 to n do
    let l = gen () in
    if legacy_overlap l then begin
      incr compared;
      let e = extracted l and h = handwritten l in
      let key =
        match e with
        | Malformed k -> "malformed:" ^ k
        | Flags (_, _, _, g) ->
            if g then "grounded" else "not-grounded"
      in
      Hashtbl.replace counts key
        (1 + try Hashtbl.find counts key with Not_found -> 0);
      if e <> h then begin
        incr bad;
        if !bad <= 5 then
          Printf.printf
            "DISAGREE: extracted %s, handwritten %s\n"
            (show e) (show h)
      end
    end else
      incr skipped
  done;
  Printf.printf
    "random differential: %d/%d agree (legacy-overlap only; %d/%d skipped)\n"
    (!compared - !bad) !compared !skipped n;
  Hashtbl.iter (fun k v -> Printf.printf "   %-24s %d\n" k v) counts;
  if !bad > 0 then failed := true


(* ---- 3. stratified populations, with INTENDED outcomes ----

   Each population is generated with a known intended verdict.  A graph is
   checked twice: the extracted checker's verdict must match the intent, and its
   L1/L2/L3 flags must match the handwritten audit's printed output.  Failing
   either is a disagreement. *)
type intent =
  | Accepted | OpenGaps | Descent_a | Descent_b | Undisclosed | No_source
  | Dup | Undeclared | Dist_not_derived | Rel_not_raw | Cyclic

let intent_name = function
  | Accepted -> "accepted" | OpenGaps -> "open (gaps)" | Descent_a -> "descent from d_A"
  | Descent_b -> "descent from d_B" | Undisclosed -> "undisclosed shared"
  | No_source -> "no independent source" | Dup -> "malformed: duplicate"
  | Undeclared -> "malformed: undeclared" | Dist_not_derived -> "malformed: distinguished"
  | Rel_not_raw -> "malformed: relevant" | Cyclic -> "malformed: cycle"

let full_cov = { C.cov_from = 0; cov_to = 1; cov_gaps = [] }
let gap_cov = { C.cov_from = 0; cov_to = 1; cov_gaps = [9] }

(* ---- v6-only edge cases ----

   These cases intentionally lie outside the domain in which the frozen
   handwritten audit is authoritative.  They are tested against the v6
   specification directly. *)

let () =
  let eq_a : J.lineage =
    { J.derived = [("da", ["ra"]); ("db", ["rb"])];
      raw = ["ra"; "rb"; "rg"];
      claim_relevant = ["rg"];
      d_a = "da"; d_b = "db"; ground = "da";
      dispositions = [] }
  in
  let eq_b : J.lineage =
    { J.derived = [("da", ["ra"]); ("db", ["rb"])];
      raw = ["ra"; "rb"; "rg"];
      claim_relevant = ["rg"];
      d_a = "da"; d_b = "db"; ground = "db";
      dispositions = [] }
  in
  let raw_ground : J.lineage =
    { J.derived = [("da", ["ra"]); ("db", ["rb"])];
      raw = ["ra"; "rb"; "rg"];
      claim_relevant = ["rg"];
      d_a = "da"; d_b = "db"; ground = "rg";
      dispositions = [] }
  in

  let ga = to_coq eq_a
  and gb = to_coq eq_b
  and gr = to_coq raw_ground in

  let checks =
    [
      ("ground=d_A rejected",
       match C.lineage_check ga full_cov with
       | C.LineageRejected C.GroundEqualsA -> true
       | _ -> false);

      ("ground=d_B rejected",
       match C.lineage_check gb full_cov with
       | C.LineageRejected C.GroundEqualsB -> true
       | _ -> false);

      ("raw ground accepted",
       match C.lineage_check gr full_cov with
       | C.LineageAccepted -> true
       | _ -> false);

      ("raw ground certificate issued",
       match C.issue_certificate gr full_cov with
       | Some _ -> true
       | None -> false);

      ("ground=d_A no certificate",
       match C.issue_certificate ga full_cov with
       | None -> true
       | Some _ -> false);

      ("ground=d_B no certificate",
       match C.issue_certificate gb full_cov with
       | None -> true
       | Some _ -> false);
    ]
  in

  let passed =
    List.fold_left
      (fun n (name, ok) ->
         Printf.printf "v6 %-32s %s\n"
           name (if ok then "PASS" else "FAIL");
         if ok then n + 1 else n)
      0 checks
  in

  Printf.printf "v6 edge cases: %d/%d pass\n"
    passed (List.length checks);

  if passed <> List.length checks then
    failed := true


(* Build an accepted graph; [shared] adds a disclosed shared non-raw ancestor.
   Nodes: raw rg (ground-only source), ra, rb, extras; derived ia, da, db, g,
   and optionally s (shared by da and db). *)
let build ~shared ~undisclosed ~extras ~pick_subset ~shuffle : J.lineage =
  let ex = List.init extras (fun i -> Printf.sprintf "e%d" i) in
  let raws = ["rg"; "ra"; "rb"] @ ex in
  let sh = if shared then ["s"] else [] in
  let da_par = ["ia"] @ sh @ pick_subset ex in
  let db_par = ["rb"] @ sh @ pick_subset ex in
  let g_par = ["rg"] @ pick_subset ("ra" :: "rb" :: ex) in
  let derived =
    (if shared then [("s", ["ra"])] else []) @
    [("ia", ["ra"]); ("da", da_par); ("db", db_par); ("g", g_par)] in
  let relevant = "rg" :: pick_subset ("ra" :: "rb" :: ex) in
  let disp = if shared && not undisclosed then [("s", J.Open_defeater "d")] else [] in
  { J.derived = shuffle derived; raw = raws; claim_relevant = relevant;
    d_a = "da"; d_b = "db"; ground = "g"; dispositions = disp }

(* A chain [p1 <- p2 <- ... <- pk <- root]: node [p_i] has parent [p_{i+1}] and [p_k]
   has parent [root].  Returns the derived entries and the head [p1]. *)
let chain prefix k root =
  let name i = Printf.sprintf "%s%d" prefix i in
  let entries = List.init k (fun i -> (name (i + 1), [if i + 1 = k then root else name (i + 2)])) in
  (entries, name 1)

(* DEEP graphs: every decisive ancestor is reachable only after several
   saturation rounds.  The ground reaches its independent raw source through a
   chain of [gdepth] (3..5) derived nodes, so that source is at depth >= 4; the
   coordinates reach their raw inputs (and any shared derived ancestor) through
   chains of 2..4 derived nodes. *)
type deep_kind = DAccepted | DDescent_a | DDescent_b | DUndisclosed | DNo_source

let build_deep kind ~shuffle : J.lineage =
  let gdepth = 3 + Random.int 3 in
  let shared = (kind = DUndisclosed) || (kind = DAccepted && Random.bool ()) in
  let ca, ha = chain "ia" (2 + Random.int 3) (if shared then "s" else "ra") in
  let cb, hb = chain "ib" (2 + Random.int 3) (if shared then "s" else "rb") in
  let cg, hg = chain "q" gdepth "rg" in
  let da = ("da", [ha]) and db = ("db", [hb]) in
  (* descent: the ground gets an extra branch h1 <- h2 <- h3 <- (da | db), depth 4 *)
  let branch target = let c, h = chain "h" 3 target in (c, h) in
  let extra_c, g_par =
    match kind with
    | DDescent_a -> let c, h = branch "da" in (c, [hg; h])
    | DDescent_b -> let c, h = branch "db" in (c, [hg; h])
    | _ -> ([], [hg]) in
  let g = ("g", g_par) in
  let derived = (if shared then [("s", ["ra"])] else []) @ ca @ cb @ cg @ extra_c @ [da; db; g] in
  let relevant = if kind = DNo_source then ["ra"] else ["rg"] in
  let disp = if shared && kind <> DUndisclosed then [("s", J.Open_defeater "d")] else [] in
  { J.derived = shuffle derived; raw = ["rg"; "ra"; "rb"]; claim_relevant = relevant;
    d_a = "da"; d_b = "db"; ground = "g"; dispositions = disp }

let stratified () =
  let n_each = 300 in
  let pick_subset l = List.filter (fun _ -> Random.int 3 = 0) l in
  let shuffle l = List.map snd (List.sort compare (List.map (fun x -> (Random.bits (), x)) l)) in
  let mk ?(shared = Random.bool ()) ?(undisclosed = false) () =
    build ~shared ~undisclosed ~extras:(Random.int 3) ~pick_subset ~shuffle in
  let add_parent l n p =
    { l with J.derived = List.map (fun (m, ps) -> if m = n then (m, ps @ [p]) else (m, ps)) l.J.derived } in
  let gen = function
    | Accepted | OpenGaps -> mk ()
    | Descent_a -> add_parent (mk ()) "g" "da"
    | Descent_b -> add_parent (mk ()) "g" "db"
    | Undisclosed -> mk ~shared:true ~undisclosed:true ()
    | No_source -> let l = mk () in { l with J.claim_relevant = ["ra"] }
    | Dup -> let l = mk () in { l with J.derived = l.J.derived @ [List.hd l.J.derived] }
    | Undeclared -> add_parent (mk ()) "da" "ghost"
    | Dist_not_derived -> let l = mk () in { l with J.ground = "ghost_ground" }
    | Rel_not_raw -> let l = mk () in { l with J.claim_relevant = "da" :: l.J.claim_relevant }
    | Cyclic -> add_parent (mk ()) "ia" "da" in
  let cov_of = function OpenGaps -> gap_cov | _ -> full_cov in
  (* the extracted checker's constructor, as an intent *)
  let observed l cov : intent option =
    let g = to_coq l in
    match C.lineage_check g cov with
    | C.LineageAccepted -> Some Accepted
    | C.LineageOpen _ -> Some OpenGaps
    | C.LineageRejected (C.Malformed C.DuplicateNode) -> Some Dup
    | C.LineageRejected (C.Malformed C.UndeclaredParent) -> Some Undeclared
    | C.LineageRejected (C.Malformed C.DistinguishedNotDerived) -> Some Dist_not_derived
    | C.LineageRejected (C.Malformed C.RelevantNotRaw) -> Some Rel_not_raw
    | C.LineageRejected (C.Malformed (C.Cycle _)) -> Some Cyclic
    | C.LineageRejected (C.GroundEqualsA | C.GroundEqualsB) -> None
    | C.LineageRejected C.DescentFromA -> Some Descent_a
    | C.LineageRejected C.DescentFromB -> Some Descent_b
    | C.LineageRejected (C.UndisclosedShared _) -> Some Undisclosed
    | C.LineageRejected C.NoIndependentSource -> Some No_source in
  (* populations: (label, intended verdict, generator, coverage) *)
  let shallow = List.map (fun it -> (intent_name it, it, (fun () -> gen it), cov_of it))
      [Accepted; OpenGaps; Descent_a; Descent_b; Undisclosed; No_source;
       Dup; Undeclared; Dist_not_derived; Rel_not_raw; Cyclic] in
  let deep k = build_deep k ~shuffle in
  let deep_pops = [
    ("deep: accepted (L3 source at depth >= 4)", Accepted, (fun () -> deep DAccepted), full_cov);
    ("deep: open (gaps)", OpenGaps, (fun () -> deep DAccepted), gap_cov);
    ("deep: descent from d_A (depth 4)", Descent_a, (fun () -> deep DDescent_a), full_cov);
    ("deep: descent from d_B (depth 4)", Descent_b, (fun () -> deep DDescent_b), full_cov);
    ("deep: undisclosed shared ancestor", Undisclosed, (fun () -> deep DUndisclosed), full_cov);
    ("deep: no independent source", No_source, (fun () -> deep DNo_source), full_cov) ] in
  print_endline "=== stratified populations (intended outcome + handwritten flags) ===";
  let all_ok = ref true in
  List.iter (fun (label, it, gen, cov) ->
      let ok_intent = ref 0 and ok_hand = ref 0 in
      for _ = 1 to n_each do
        let l = gen () in
        if observed l cov = Some it then incr ok_intent;
        if extracted l = handwritten l then incr ok_hand
      done;
      if !ok_intent <> n_each || !ok_hand <> n_each then all_ok := false;
      Printf.printf "%-42s n=%d  intended-verdict %d/%d  handwritten-flags %d/%d\n"
        label n_each !ok_intent n_each !ok_hand n_each)
    (shallow @ deep_pops);
  if not !all_ok then failed := true

let () = Random.init 20260922; stratified (); if !failed then exit 1
