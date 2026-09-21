(** * The original grounded seam as an instance of the generic calculus.

    Everything here is stated against the UNCHANGED legacy definitions
    [Span], [GroundingEquations], [seam_transport], [copied_not_grounded]
    (legacy/exactness-2026/GroundedSeam.v, SHA-256 efc4415f...).

    Design point.  A transport witness is a path of *grounded crossings*.  A
    crossing at a seam element [r] carries BOTH original grounding equations
    against the independent seam valuation:

        Phi_A (back r) = Phi_seam r     and     Phi_B (fwd r) = Phi_seam r.

    Erasure then yields only the pairwise agreement
    [Phi_A (back r) = Phi_B (fwd r)], and [copied_not_grounded] shows that the
    passage from grounded to pairwise is strictly lossy. *)

From Coq Require Import Bool.
From GTC.Core Require Import GroundedTransport Erasure.
From GTC.Obstructions Require Import FibreObstruction UngroundedAgreement.
From Exactness Require Import GroundedSeam.

Section OriginalSeam.
  Context {A B : Type} (S : Span A B)
          (PA : A -> bool) (PB : B -> bool) (Ps : seam S -> bool).

  Definition ost : Type := (A + B)%type.

  Definition oval (x : ost) : bool :=
    match x with inl a => PA a | inr b => PB b end.

  Inductive OPath : ost -> ost -> Type :=
  | op_refl  : forall x, OPath x x
  | op_step  : forall r : seam S,
      PA (back S r) = Ps r -> PB (fwd S r) = Ps r ->
      OPath (inl (back S r)) (inr (fwd S r))
  | op_trans : forall x y z, OPath x y -> OPath y z -> OPath x z.

  Lemma opath_sound : forall x y, OPath x y -> oval x = oval y.
  Proof.
    intros x y p. induction p as [x|r ha hb|x y z p1 IH1 p2 IH2].
    - reflexivity.
    - cbn. rewrite ha, hb. reflexivity.
    - etransitivity; eassumption.
  Qed.

  Definition orig_structure : GTransport ost (fun x y => oval x = oval y) :=
    {| GT := OPath; gt_refl := op_refl; gt_compose := op_trans;
       gt_sound := opath_sound |}.

  (** Inversion: a non-trivial path is exactly one grounded crossing. *)
  Lemma opath_inv : forall x y, OPath x y ->
    x = y \/ exists r : seam S,
      x = inl (back S r) /\ y = inr (fwd S r) /\
      PA (back S r) = Ps r /\ PB (fwd S r) = Ps r.
  Proof.
    intros x y p. induction p as [x|r ha hb|x y z p1 IH1 p2 IH2].
    - left. reflexivity.
    - right. exists r. repeat split; auto.
    - destruct IH1 as [->|(r & -> & -> & ha & hb)].
      + exact IH2.
      + destruct IH2 as [E|(r' & E1 & -> & ha' & hb')].
        * subst. right. exists r. repeat split; auto.
        * discriminate E1.
  Qed.

  (** The original grounding equations supply a crossing at every seam element. *)
  Lemma grounding_gives_crossing :
    GroundingEquations S PA PB Ps ->
    forall r : seam S, GT orig_structure (inl (back S r)) (inr (fwd S r)).
  Proof.
    intros HG r. destruct (HG r) as [ha hb]. exact (op_step r ha hb).
  Qed.

  (** Target 1.  Original grounding erases to pairwise extensional agreement. *)
  Theorem original_grounding_erases_to_extensional :
    GroundingEquations S PA PB Ps ->
    forall r : seam S, PA (back S r) = PB (fwd S r).
  Proof.
    intros HG r.
    exact (erasure_sound orig_structure _ _
             (erase orig_structure (grounding_gives_crossing HG r))).
  Qed.

  (** Two results, kept distinct.

      The endpoint equation needs only PAIRWISE agreement and a factorisation
      of [PA].  Grounding does not change the endpoint equation; it supplies a
      stronger warrant for using it. *)
  Definition ExtensionalSeamAgreement : Prop :=
    forall r : seam S, PA (back S r) = PB (fwd S r).

  Theorem extensional_factor_transport {OA : Type} (M_A : A -> OA)
      (h : OA -> bool) :
    ExtensionalSeamAgreement ->
    (forall a, PA a = h (M_A a)) ->
    forall r : seam S, PB (fwd S r) = h (M_A (back S r)).
  Proof.
    intros Hext Hh r. rewrite <- (Hh (back S r)). symmetry. exact (Hext r).
  Qed.

  (** Grounded corollary: erase grounded coherence to extensional coherence,
      then apply the extensional theorem. *)
  Corollary grounded_factor_transport {OA : Type} (M_A : A -> OA)
      (h : OA -> bool) :
    GroundingEquations S PA PB Ps ->
    (forall a, PA a = h (M_A a)) ->
    forall r : seam S, PB (fwd S r) = h (M_A (back S r)).
  Proof.
    intros HG. exact (extensional_factor_transport M_A h
                        (original_grounding_erases_to_extensional HG)).
  Qed.

  (** Target 2.  The original [seam_transport], statement exactly as in the
      legacy file, recovered from the generic calculus. *)
  Theorem original_seam_transport_from_generic {OA : Type} (M_A : A -> OA) :
    GroundingEquations S PA PB Ps ->
    forall h : OA -> bool, (forall a, PA a = h (M_A a)) ->
    forall r : seam S, PB (fwd S r) = h (M_A (back S r)).
  Proof. intros HG h. exact (grounded_factor_transport M_A h HG). Qed.

  Corollary original_seam_transport_admissible_from_generic {OA : Type}
      (M_A : A -> OA) :
    GroundingEquations S PA PB Ps ->
    Admissible M_A PA ->
    exists h : OA -> bool, forall r : seam S, PB (fwd S r) = h (M_A (back S r)).
  Proof.
    intros HG [h Hh]. exists h.
    exact (original_seam_transport_from_generic M_A HG h Hh).
  Qed.

  (** The two routes agree with the legacy theorems (same statements). *)
  Example agrees_with_legacy_seam_transport {OA : Type} (M_A : A -> OA) :
    GroundingEquations S PA PB Ps ->
    forall h : OA -> bool, (forall a, PA a = h (M_A a)) ->
    forall r : seam S, PB (fwd S r) = h (M_A (back S r)) :=
    fun HG => seam_transport S M_A PA PB Ps HG.

  (** Generic obstruction: pairwise agreement at [a],[b] with no *grounded*
      crossing from [a] to [b] leaves [inl a], [inr b] without transport. *)
  Theorem ungrounded_of_no_grounded_crossing (a : A) (b : B) :
    (forall r : seam S, back S r = a -> fwd S r = b ->
       ~ (PA (back S r) = Ps r /\ PB (fwd S r) = Ps r)) ->
    ~ erased orig_structure (inl a) (inr b).
  Proof.
    intros H [p]. destruct (opath_inv _ _ p) as [E|(r & E1 & E2 & ha & hb)].
    - discriminate E.
    - injection E1 as E1. injection E2 as E2. exact (H r (eq_sym E1) (eq_sym E2) (conj ha hb)).
  Qed.
End OriginalSeam.

(** Target 3.  The original copied-value counterexample embeds as the generic
    obstruction [UngroundedAgreement]. *)
Section Copied.
  Let G := orig_structure dual_write copied_status copied_status trace_status.

  Theorem original_copied_counterexample_embeds :
    UngroundedAgreement G (inl r_star) (inr r_star).
  Proof.
    split.
    - reflexivity.
    - apply (ungrounded_of_no_grounded_crossing dual_write copied_status
               copied_status trace_status r_star r_star).
      intros r Hb _ [Ha _]. cbn in Hb. subst r. cbn in Ha. discriminate Ha.
  Qed.

  (** Pairwise agreement holds at every crossing (legacy lemma), yet erasure
      of grounded transport does not recover it. *)
  Corollary copied_erasure_not_exact :
    ~ (forall x y, oval copied_status copied_status x
                   = oval copied_status copied_status y
                   <-> erased G x y).
  Proof.
    intro H. exact (no_exact_recovery_if_ungrounded G _ _
                      original_copied_counterexample_embeds H).
  Qed.

  (** The legacy [copied_not_grounded] is recoverable from the generic
      obstruction: a grounding would supply the crossing at [r_star]. *)
  Corollary copied_not_grounded_from_generic :
    ~ GroundingEquations dual_write copied_status copied_status trace_status.
  Proof.
    intro HG.
    exact (proj2 original_copied_counterexample_embeds
             (erase G (grounding_gives_crossing dual_write copied_status
                         copied_status trace_status HG r_star))).
  Qed.
End Copied.

(** The extensional conclusion can survive after the warrant supporting it
    has failed: on [dual_write] the endpoint equation of [seam_transport] holds
    for every seam element (with the constant factor), yet grounding fails. *)
Theorem extensional_conclusion_survives_ungrounded :
  (forall r : seam dual_write,
     copied_status (fwd dual_write r)
     = (fun _ : unit => true) ((fun _ : Req => tt) (back dual_write r))) /\
  ~ GroundingEquations dual_write copied_status copied_status trace_status.
Proof.
  split.
  - intro r. reflexivity.
  - exact copied_not_grounded.
Qed.

(** Target 5.  Pairwise coordinate agreement does not imply the original
    grounding equations, in general. *)
Theorem pairwise_agreement_not_grounding :
  ~ (forall (A B : Type) (S : Span A B) (PA : A -> bool) (PB : B -> bool)
       (Ps : seam S -> bool),
       (forall r, PA (back S r) = PB (fwd S r)) ->
       GroundingEquations S PA PB Ps).
Proof.
  intro H.
  exact (copied_not_grounded
           (H Req Req dual_write copied_status copied_status trace_status
              copied_extensionally_coherent)).
Qed.

(** The lineage-sensitive predicate here is the exhibited trace status: the
    copied value does not determine it. *)
Definition req_of (x : @ost Req Req) : Req := match x with inl r => r | inr r => r end.

Corollary trace_not_determined_by_copied_value :
  ~ Factors (oval copied_status copied_status)
            (fun x => trace_status (req_of x)).
Proof.
  apply (fibre_obstruction _ _ (inl r_ok) (inl r_star)).
  - reflexivity.
  - cbn. discriminate.
Qed.
