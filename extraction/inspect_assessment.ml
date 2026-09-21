(* Consumer of the extracted assessments (see ExtractAssessment.v): shows that
   located obstructions, lineage graph, custodian and coverage survive extraction.
   Build: ocamlc -c assessment_extracted.mli assessment_extracted.ml &&
          ocamlc -o inspect assessment_extracted.cmo inspect_assessment.ml *)
open Assessment_extracted
let rec len = function [] -> 0 | _ :: t -> 1 + len t
let kind = function
  | ObservationalObstruction _ -> "Observational"
  | ConstructionObstruction (LineageDescent) -> "Construction(LineageDescent)"
  | ConstructionObstruction _ -> "Construction(other)"
  | MaintenanceObstruction _ -> "Maintenance"
  | InstitutionalObstruction _ -> "Institutional"
let show name = function
  | Certified _ -> Printf.printf "%-28s Certified (evidence attached)\n" name
  | Refuted (h, t) ->
      Printf.printf "%-28s Refuted [%s]\n" name (String.concat "; " (List.map kind (h :: t)))
  | Open os ->
      Printf.printf "%-28s Open, %d obligation(s)\n" name (len os)
let ws c w = witness_summary c (Obj.magic (Inl ())) (Obj.magic (Inr ())) w
let () =
  show "copied" copied_assessment;
  show "copied, lineage missing" copied_missing_lineage;
  show "copied, lineage partial" copied_partial_lineage;
  show "maintenance lost" failure_assessment;
  show "maintenance unassessed" open_assessment;
  show "copied + maintenance lost" both_assessment;
  show "grounded, preserved" certified_assessment;
  (match certified_assessment with
   | Certified ct ->
       let cc = ct.ct_construction in
       Printf.printf "certified evidence: custodian=%d record=%d lineage ground node=%d verdict=%s\n"
         cc.cc_exhibition.ex_custodian cc.cc_exhibition.ex_record_id
         cc.cc_lineage.lc_graph.lin_ground
         (match cc.cc_lineage.lc_audit with LineagePass -> "LineagePass" | LineageFail -> "LineageFail")
   | _ -> ());
  let s w = List.map (fun x -> Printf.sprintf "{record=%d custodian=%d coverage=(%d,%d) dispositions=%d}"
                        x.ws_record x.ws_custodian (fst x.ws_coverage) (snd x.ws_coverage) x.ws_dispositions) w in
  Printf.printf "w1 %s\nw2 %s\nw3 %s\n" (String.concat "" (s (ws (two_ev d0) w1)))
    (String.concat "" (s (ws (two_ev d0) w2))) (String.concat "" (s (ws (two_ev d1) w3)))
