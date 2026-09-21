type t0
type t1
type t2

let bad (e01 : (t0, t1) Certified_temporal_seam.evolution)
        (e02 : (t0, t2) Certified_temporal_seam.evolution) =
  Certified_temporal_seam.compose e01 e02
