(** * Warrant debt.

    A transport *problem* [p : P] carries four independent obligations.
    Institutional warrant cannot be derived from mathematics: it is an *input*
    (a declared policy / authority relation).

    Problems are abstract: [P] can be a pair of states ([P := X * X], see
    [Pairwise] below), or a whole transport candidate
    ([Debt/OriginalObligations.v]). *)

From GTC.Core Require Import GroundedTransport Erasure.

Record Obligations (P : Type) : Type := {
  Obs   : P -> Prop;   (* the valuation factors through observations *)
  Cons  : P -> Prop;   (* an exhibited seam / derivation / ground     *)
  Maint : P -> Prop;   (* warrant preserved through update/evolution  *)
  Inst  : P -> Prop    (* declared rule / authority / practice        *)
}.

Arguments Obs {P} _ _.
Arguments Cons {P} _ _.
Arguments Maint {P} _ _.
Arguments Inst {P} _ _.

Definition Transport {P} (O : Obligations P) (p : P) : Prop :=
  Obs O p /\ Cons O p /\ Maint O p /\ Inst O p.

(** Independently checkable failure evidence: a refutation of the
    corresponding obligation. *)
Record DebtReport {P} (O : Obligations P) (p : P) : Type := {
  observational_debt : option (~ Obs O p);
  construction_debt  : option (~ Cons O p);
  maintenance_debt   : option (~ Maint O p);
  institutional_debt : option (~ Inst O p)
}.

Arguments observational_debt {P O p} _.
Arguments construction_debt  {P O p} _.
Arguments maintenance_debt   {P O p} _.
Arguments institutional_debt {P O p} _.

Definition Clean {P} {O : Obligations P} {p} (r : DebtReport O p) : Prop :=
  observational_debt r = None /\ construction_debt r = None /\
  maintenance_debt r = None /\ institutional_debt r = None.

(** Pairwise problems: when each obligation is reflexive and transitive as a
    relation on [X], transport is a grounded transport structure whose
    witnesses are the four pieces of evidence. *)
Section Pairwise.
  Context {X} (O : Obligations (X * X)).
  Hypothesis refl_obs   : forall x, Obs O (x, x).
  Hypothesis refl_cons  : forall x, Cons O (x, x).
  Hypothesis refl_maint : forall x, Maint O (x, x).
  Hypothesis refl_inst  : forall x, Inst O (x, x).
  Hypothesis trans_obs   : forall x y z, Obs O (x, y) -> Obs O (y, z) -> Obs O (x, z).
  Hypothesis trans_cons  : forall x y z, Cons O (x, y) -> Cons O (y, z) -> Cons O (x, z).
  Hypothesis trans_maint : forall x y z, Maint O (x, y) -> Maint O (y, z) -> Maint O (x, z).
  Hypothesis trans_inst  : forall x y z, Inst O (x, y) -> Inst O (y, z) -> Inst O (x, z).

  Definition pairwise_gtransport : GTransport X (fun x y => Transport O (x, y)).
  Proof.
    refine {| GT := fun x y => Transport O (x, y) |}.
    - intro x. repeat split; auto.
    - intros x y z (a & b & c & d) (a' & b' & c' & d').
      repeat split; eauto.
    - intros x y w. exact w.
  Defined.

  Lemma erased_iff_transport :
    forall x y, erased pairwise_gtransport x y <-> Transport O (x, y).
  Proof.
    intros x y. split.
    - exact (erasure_sound pairwise_gtransport x y).
    - intro H. exact (erase pairwise_gtransport H).
  Qed.
End Pairwise.
