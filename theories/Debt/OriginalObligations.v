(** * The four debts, bound to the original formal system.

    | Debt          | Concrete obligation                                        |
    |---------------|------------------------------------------------------------|
    | Observational | [Admissible M_A Phi_A] and [Admissible M_B Phi_B]          |
    | Construction  | inhabited seam, [Exhibited], [LineageGrounded], and the    |
    |               | original [GroundingEquations] with the seam valuation      |
    | Maintenance   | the [Functorial] slot; instantiated by evolution squares   |
    |               | that maintain grounding ([Debt/MaintenanceDebt.v])         |
    | Institutional | a supplied policy judgement (an INPUT, never derived)      |

    [Exhibited] and [LineageGrounded] remain abstract Props, as in the legacy
    [Transportable]: condition (b) is decided by the OCaml lineage audit
    (extraction/README.md), not in Coq. *)

From GTC.Debt Require Import WarrantDebt.
From Exactness Require Import GroundedSeam.

Record Candidate : Type := {
  cA : Type; cB : Type; cOA : Type; cOB : Type;
  cSpan : Span cA cB;
  cMA : cA -> cOA;  cPA : cA -> bool;
  cMB : cB -> cOB;  cPB : cB -> bool;
  cPs : seam cSpan -> bool;
  cExhibited : Prop;  cLineage : Prop;  cFunctorial : Prop
}.

(** Obligations for a single candidate (the problem type is [unit]); the
    institutional judgement is supplied by [policy]. *)
Definition candidate_obligations (c : Candidate) (policy : Prop)
  : Obligations unit :=
  {| Obs   := fun _ => Admissible (cMA c) (cPA c) /\ Admissible (cMB c) (cPB c);
     Cons  := fun _ => inhabited (seam (cSpan c)) /\ cExhibited c /\ cLineage c /\
                       GroundingEquations (cSpan c) (cPA c) (cPB c) (cPs c);
     Maint := fun _ => cFunctorial c;
     Inst  := fun _ => policy |}.

(** The original [Transportable] is exactly transport minus the institutional
    component: institutional warrant is not part of the legacy predicate. *)
Theorem transportable_iff_transport (c : Candidate) (policy : Prop) :
  Transport (candidate_obligations c policy) tt <->
  Transportable (cSpan c) (cMA c) (cPA c) (cMB c) (cPB c) (cPs c)
                (cExhibited c) (cLineage c) (cFunctorial c) /\ policy.
Proof.
  unfold Transport, Transportable, candidate_obligations. cbn. tauto.
Qed.

Corollary transportable_of_transport (c : Candidate) (policy : Prop) :
  Transport (candidate_obligations c policy) tt ->
  Transportable (cSpan c) (cMA c) (cPA c) (cMB c) (cPB c) (cPs c)
                (cExhibited c) (cLineage c) (cFunctorial c).
Proof. intro H. apply transportable_iff_transport in H. tauto. Qed.
