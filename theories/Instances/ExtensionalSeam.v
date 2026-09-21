(** * Extensional seams: the pairwise-agreement layer ONLY.

    STATUS: this file is a weaker model than the original grounded seam of
    [legacy/exactness-2026/GroundedSeam.v].  Its seam condition
    [phiB (fwd s) = phiA (back s)] is bare pairwise coordinate agreement: it has
    NO independent seam valuation [Phi_seam].  The original
    [GroundingEquations] is strictly stronger, and the gap between the two is
    exactly [copied_not_grounded] (see
    [Instances/OriginalGroundedSeamInstance.v]).

    Nothing here is the original [seam_transport].  It is kept to show what
    the calculus proves when only extensional agreement is exhibited. *)

From GTC.Core Require Import GroundedTransport Erasure.
From GTC.Contexts Require Import GroundedProper ContextualPreservation.

Record ExtSeam (V : Type) : Type := {
  sA : Type;  sB : Type;  sigma : Type;
  back : sigma -> sA;  fwd : sigma -> sB;
  phiA : sA -> V;  phiB : sB -> V;
  grounded : forall s, phiB (fwd s) = phiA (back s)
}.

Arguments sA {V} _.  Arguments sB {V} _.  Arguments sigma {V} _.
Arguments back {V} {_} _.  Arguments fwd {V} {_} _.
Arguments phiA {V} _ _.  Arguments phiB {V} _ _.
Arguments grounded {V} _ _.

Section ExtSeamCalculus.
  Context {V : Type}.

  Definition st (S : ExtSeam V) : Type := sA S + sB S.

  Definition val (S : ExtSeam V) (x : st S) : V :=
    match x with inl a => phiA S a | inr b => phiB S b end.

  Inductive ExtPath (S : ExtSeam V) : st S -> st S -> Type :=
  | ep_refl  : forall x, ExtPath S x x
  | ep_step  : forall s : sigma S, ExtPath S (inl (back s)) (inr (fwd s))
  | ep_trans : forall x y z, ExtPath S x y -> ExtPath S y z -> ExtPath S x z.

  Lemma ext_path_sound (S : ExtSeam V) x y :
    ExtPath S x y -> val S x = val S y.
  Proof.
    intro p. induction p as [x|s|x y z p1 IH1 p2 IH2].
    - reflexivity.
    - symmetry. apply (grounded S).
    - etransitivity; eassumption.
  Qed.

  Definition ext_seam_structure (S : ExtSeam V)
    : GTransport (st S) (fun x y => val S x = val S y) :=
    {| GT := ExtPath S;
       gt_refl := ep_refl S;
       gt_compose := fun x y z => ep_trans S x y z;
       gt_sound := ext_path_sound S |}.

  (** Observation factorisation on the A-side. *)
  Record ExtFactored (S : ExtSeam V) (O : Type) : Type := {
    obsM : sA S -> O;
    phihat : O -> V;
    factor : forall a, phiA S a = phihat (obsM a)
  }.

  Arguments obsM {S O} _ _.
  Arguments phihat {S O} _ _.
  Arguments factor {S O} _ _.

  (** The existing seam transport theorem, now a *corollary* of erasure
      soundness of the generic calculus. *)
  Corollary extensional_seam_transport {O} (S : ExtSeam V) (F : ExtFactored S O) :
    forall s : sigma S,
      phiB S (fwd s) = phihat F (obsM F (back s)).
  Proof.
    intro s.
    assert (H : val S (inl (back s)) = val S (inr (fwd s)))
      by exact (erasure_sound (ext_seam_structure S) _ _
                  (erase (ext_seam_structure S) (ep_step S s))).
    cbn in H. rewrite <- H. apply (factor F).
  Qed.

  (** Contexts: any map of states that sends seam crossings to transport
      paths is grounded-proper (the analogue of one evolution step). *)
  Section Evolution.
    Context {S S' : ExtSeam V} (Fm : st S -> st S').
    Hypothesis Hstep :
      forall s : sigma S, ExtPath S' (Fm (inl (back s))) (Fm (inr (fwd s))).

    Fixpoint ep_map {x y : st S} (p : ExtPath S x y)
      : ExtPath S' (Fm x) (Fm y) :=
      match p with
      | ep_refl _ x => ep_refl S' (Fm x)
      | ep_step _ s => Hstep s
      | ep_trans _ _ _ _ p q => ep_trans S' _ _ _ (ep_map p) (ep_map q)
      end.

    Definition ext_seam_context
      : GroundedProper (ext_seam_structure S) (ext_seam_structure S') Fm.
    Proof.
      refine (@Build_GroundedProper _ _ _ _ (ext_seam_structure S) (ext_seam_structure S') Fm
                (fun x y (p : ExtPath S x y) => ep_map p) _ _);
        reflexivity.
    Defined.
  End Evolution.
End ExtSeamCalculus.

Arguments obsM {V S O} _ _.
Arguments phihat {V S O} _ _.
Arguments factor {V S O} _ _.
