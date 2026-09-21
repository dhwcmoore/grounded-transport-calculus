# Notation

| Paper | Rocq |
|---|---|
| GTrans(x,y) | `GT G x y` |
| id_x | `gt_refl G x` |
| compose (diagrammatic) | `gt_compose G v w` |
| x ≼_G y | `erased G x y` |
| GroundedProper(F), map_F | `GroundedProper GX GY F`, `gp_map` |
| observational equivalence ~_M | `obs_equiv M` |
| Warrant debts | `Obs`, `Cons`, `Maint`, `Inst` in `Obligations`; `DebtReport` |
| grounded crossing at r | `op_step r ha hb` (both grounding equations against `Phi_seam`) |
| transport witness in a seam | `OPath` over `A + B` |
| structural / valuation naturality; preservation | `SeamEvolution`; `NaturalValuations e UV`; `PreservesGroundingOnImage` |
| maintenance obligation | `EvolutionMaintained` (Prop), `EvolutionMaintenanceEvidence` (Type) |
| obligation verdict | `Assessment` (`Discharged`/`Refuted`/`Open`); `WarrantStatus` |
| certificates | `ExhibitionCertificate`, `LineageCertificate g`, `AuthorisationCertificate` |
