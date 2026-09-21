type fake = { es : int -> int; ea : int -> int; eb : int -> int }

let forged : (int, int) Certified_temporal_seam.evolution =
  Obj.magic { es = (fun r -> r); ea = (fun x -> x); eb = (fun x -> x + 1) }

let () =
  ignore forged;
  print_endline "unsafe cast compiled"
