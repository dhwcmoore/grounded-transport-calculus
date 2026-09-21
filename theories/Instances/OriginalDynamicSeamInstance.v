(** * The original [SeamEvolution] as grounded-proper contexts.

    Against the unchanged legacy [TemporalSystem], [SeamEvolution],
    [evolution_id], [evolution_compose].  Three distinct things, kept apart:

    - STRUCTURAL naturality: the two squares [ev_back_commutes],
      [ev_fwd_commutes], with identity and composition.  This is all the
      manuscript's dynamic seam naturality requires, and all [SeamEvolution]
      records.  It says nothing about valuations.
    - VALUATION naturality ([NaturalValuations]): an OPTIONAL strengthening,
      available when the value spaces carry a transport [UV].  All three
      valuations must be natural.
    - PRESERVATION ([PreservesGroundingOnImage]): the consequence needed for
      grounded transport: grounding at [r] implies grounding at [ev_seam e r].
      It concerns only seam elements IN THE IMAGE of [ev_seam]; coverage of the
      target seam is a separate matter ([surjective_evolution_preserves_all_grounding]).

    [SeamEvolution] alone does not imply preservation
    (examples/MaintenanceFailure.v). *)

From GTC.Core Require Import GroundedTransport Erasure.
From GTC.Contexts Require Import GroundedProper ContextualPreservation.
From GTC.Instances Require Import OriginalGroundedSeamInstance.
From Exactness Require Import GroundedSeam.

(** Valuations at every stage: coordinate valuations and the independent seam
    valuation. *)
Record ValuedSystem (X : TemporalSystem) : Type := {
  vA : forall t, A X t -> bool;
  vB : forall t, B X t -> bool;
  vS : forall t, seam (sp X t) -> bool
}.
Arguments vA {X} _ _ _.
Arguments vB {X} _ _ _.
Arguments vS {X} _ _ _.

Section Dynamic.
  Context {X : TemporalSystem} (V : ValuedSystem X).

  Definition gstr (t : time X) :=
    orig_structure (sp X t) (vA V t) (vB V t) (vS V t).

  Definition GroundedAt (t : time X) (r : seam (sp X t)) : Prop :=
    vA V t (back (sp X t) r) = vS V t r /\ vB V t (fwd (sp X t) r) = vS V t r.

  Lemma grounding_iff_grounded_at (t : time X) :
    GroundingEquations (sp X t) (vA V t) (vB V t) (vS V t)
    <-> forall r, GroundedAt t r.
  Proof. split; intro H; exact H. Qed.

  Definition evo_state {t u} (e : SeamEvolution X t u)
    : @ost (A X t) (B X t) -> @ost (A X u) (B X u) :=
    fun x => match x with inl a => inl (ev_A e a) | inr b => inr (ev_B e b) end.

  (** Preservation on the image: grounding at [r] implies grounding at the
      transported seam element [ev_seam e r].  Says nothing about target seam
      elements outside the image of [ev_seam e]. *)
  Definition PreservesGroundingOnImage {t u} (e : SeamEvolution X t u) : Prop :=
    forall r, GroundedAt t r -> GroundedAt u (ev_seam e r).

  (** Valuation naturality, relative to a value transport [UV] (the manuscript's
      [U^V_{t,u}]): all three valuations must be natural. *)
  Definition NaturalValuations {t u} (e : SeamEvolution X t u)
      (UV : bool -> bool) : Prop :=
    (forall a, vA V u (ev_A e a) = UV (vA V t a)) /\
    (forall b, vB V u (ev_B e b) = UV (vB V t b)) /\
    (forall r, vS V u (ev_seam e r) = UV (vS V t r)).

  (** Structural squares + valuation naturality give preservation on the image.
      The squares are used, via [ev_back_commutes] / [ev_fwd_commutes]. *)
  Theorem natural_valuations_preserve_grounding_on_image {t u}
      (e : SeamEvolution X t u) (UV : bool -> bool) :
    NaturalValuations e UV -> PreservesGroundingOnImage e.
  Proof.
    intros (nA & nB & nS) r [ha hb]. split.
    - rewrite (ev_back_commutes e r), nA, nS, ha. reflexivity.
    - rewrite (ev_fwd_commutes e r), nB, nS, hb. reflexivity.
  Qed.

  (** The same, in the form "grounding equations at [t] give grounding at every
      transported seam element". *)
  Corollary grounding_at_transported_elements {t u}
      (e : SeamEvolution X t u) (UV : bool -> bool) :
    NaturalValuations e UV ->
    GroundingEquations (sp X t) (vA V t) (vB V t) (vS V t) ->
    forall r, GroundedAt u (ev_seam e r).
  Proof.
    intros N HG r. exact (natural_valuations_preserve_grounding_on_image e UV N r (HG r)).
  Qed.

  (** Coverage: preservation on the image lifts to the whole target seam when
      [ev_seam] is surjective.  New seam elements NOT descended from the old
      seam need new grounding evidence. *)
  Definition Surjective {P Q : Type} (f : P -> Q) : Prop := forall q, exists p, f p = q.

  Theorem surjective_evolution_preserves_all_grounding {t u}
      (e : SeamEvolution X t u) :
    PreservesGroundingOnImage e ->
    Surjective (ev_seam e) ->
    GroundingEquations (sp X t) (vA V t) (vB V t) (vS V t) ->
    GroundingEquations (sp X u) (vA V u) (vB V u) (vS V u).
  Proof.
    intros Hp Hs HG r'. destruct (Hs r') as [r <-]. exact (Hp r (HG r)).
  Qed.

  Lemma preserves_id (t : time X) : PreservesGroundingOnImage (evolution_id X t).
  Proof. intros r H. exact H. Qed.

  Lemma preserves_compose {t u v} (e1 : SeamEvolution X t u)
      (e2 : SeamEvolution X u v) :
    PreservesGroundingOnImage e1 -> PreservesGroundingOnImage e2 ->
    PreservesGroundingOnImage (evolution_compose e1 e2).
  Proof. intros M1 M2 r H. exact (M2 _ (M1 _ H)). Qed.

  Lemma natural_id (t : time X) :
    NaturalValuations (evolution_id X t) (fun v => v).
  Proof. repeat split; intro; reflexivity. Qed.

  Lemma natural_compose {t u v} (e1 : SeamEvolution X t u)
      (e2 : SeamEvolution X u v) (UV1 UV2 : bool -> bool) :
    NaturalValuations e1 UV1 -> NaturalValuations e2 UV2 ->
    NaturalValuations (evolution_compose e1 e2) (fun x => UV2 (UV1 x)).
  Proof.
    intros (a1 & b1 & s1) (a2 & b2 & s2). repeat split; intro x; cbn.
    - rewrite a2, a1. reflexivity.
    - rewrite b2, b1. reflexivity.
    - rewrite s2, s1. reflexivity.
  Qed.

  Definition path_cast {t} {x x' y y' : @ost (A X t) (B X t)}
      (ex : x = x') (ey : y = y')
      (p : OPath (sp X t) (vA V t) (vB V t) (vS V t) x y)
    : OPath (sp X t) (vA V t) (vB V t) (vS V t) x' y' :=
    eq_rect y (fun y0 => OPath (sp X t) (vA V t) (vB V t) (vS V t) x' y0)
      (eq_rect x (fun x0 => OPath (sp X t) (vA V t) (vB V t) (vS V t) x0 y) p x' ex)
      y' ey.

  Definition evo_map {t u} (e : SeamEvolution X t u) (M : PreservesGroundingOnImage e)
    : forall x y, OPath (sp X t) (vA V t) (vB V t) (vS V t) x y ->
                  OPath (sp X u) (vA V u) (vB V u) (vS V u)
                        (evo_state e x) (evo_state e y).
  Proof.
    intros x y p. induction p as [x|r ha hb|x y z p1 IH1 p2 IH2].
    - exact (op_refl _ _ _ _ _).
    - destruct (M r (conj ha hb)) as [ha' hb'].
      exact (path_cast (f_equal inl (ev_back_commutes e r))
                       (f_equal inr (ev_fwd_commutes e r))
                       (op_step _ _ _ _ (ev_seam e r) ha' hb')).
    - exact (op_trans _ _ _ _ _ _ _ IH1 IH2).
  Defined.

  (** Target 4.  A [SeamEvolution] that PRESERVES GROUNDING ON THE IMAGE is a
      grounded-proper context.  The extra hypothesis is essential: the witness
      map must send a grounded crossing at [r] to a grounded crossing at
      [ev_seam e r]. *)
  Definition original_grounding_preserving_evolution_is_grounded_proper {t u}
      (e : SeamEvolution X t u) (M : PreservesGroundingOnImage e)
    : GroundedProper (gstr t) (gstr u) (evo_state e).
  Proof.
    refine (@Build_GroundedProper _ _ _ _ (gstr t) (gstr u) (evo_state e)
              (evo_map e M) _ _);
    reflexivity.
  Defined.

  Corollary evolution_preserves_grounded_transport {t u}
      (e : SeamEvolution X t u) (M : PreservesGroundingOnImage e) x y :
    erased (gstr t) x y -> erased (gstr u) (evo_state e x) (evo_state e y).
  Proof.
    exact (grounded_proper_erased (original_grounding_preserving_evolution_is_grounded_proper e M) x y).
  Qed.

  (** Identity and composition of legacy evolutions act on states as identity
      and composite of the maps. *)
  Lemma evo_state_id (t : time X) x : evo_state (evolution_id X t) x = x.
  Proof. destruct x; reflexivity. Qed.

  Lemma evo_state_compose {t u v} (e1 : SeamEvolution X t u)
      (e2 : SeamEvolution X u v) x :
    evo_state (evolution_compose e1 e2) x = evo_state e2 (evo_state e1 x).
  Proof. destruct x; reflexivity. Qed.

  (** Compositional preservation.  The composite legacy evolution is
      grounded-proper (by construction, from [preserves_compose]) and its
      state map is pointwise the composite of the state maps, so it agrees with
      [gp_comp] of the two steps. *)
  Definition evolution_compose_grounded_proper {t u v}
      (e1 : SeamEvolution X t u) (e2 : SeamEvolution X u v)
      (M1 : PreservesGroundingOnImage e1) (M2 : PreservesGroundingOnImage e2)
    : GroundedProper (gstr t) (gstr v) (evo_state (evolution_compose e1 e2)) :=
    original_grounding_preserving_evolution_is_grounded_proper (evolution_compose e1 e2)
      (preserves_compose e1 e2 M1 M2).

  Definition evolution_compose_via_gp_comp {t u v}
      (e1 : SeamEvolution X t u) (e2 : SeamEvolution X u v)
      (M1 : PreservesGroundingOnImage e1) (M2 : PreservesGroundingOnImage e2)
    : GroundedProper (gstr t) (gstr v)
        (fun x => evo_state e2 (evo_state e1 x)) :=
    gp_comp (original_grounding_preserving_evolution_is_grounded_proper e1 M1)
            (original_grounding_preserving_evolution_is_grounded_proper e2 M2).

  Definition evolution_identity_grounded_proper (t : time X)
    : GroundedProper (gstr t) (gstr t) (evo_state (evolution_id X t)) :=
    original_grounding_preserving_evolution_is_grounded_proper (evolution_id X t) (preserves_id t).
End Dynamic.
