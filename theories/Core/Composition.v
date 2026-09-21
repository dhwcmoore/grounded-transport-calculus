(** * Derived composition, and the trivial (proof-irrelevant) instance. *)

From Coq Require Import Classes.RelationClasses.
From GTC.Core Require Import GroundedTransport Erasure.

(** n-ary composition of a chain of witnesses. *)
Inductive GChain {X R} (G : GTransport X R) : X -> X -> Type :=
| chain_nil  : forall x, GChain G x x
| chain_cons : forall x y z, GT G x y -> GChain G y z -> GChain G x z.

Fixpoint chain_collapse {X R} (G : GTransport X R) {x y : X}
  (c : GChain G x y) : GT G x y :=
  match c with
  | chain_nil _ x => gt_refl G x
  | chain_cons _ _ _ _ w c' => gt_compose G w (chain_collapse G c')
  end.

Lemma chain_sound {X R} (G : GTransport X R) {x y} (c : GChain G x y) :
  R x y.
Proof. exact (gt_sound G (chain_collapse G c)). Qed.

(** Any preorder is a grounded transport structure whose witnesses are the
    proofs themselves.  Here erasure recovers [R] exactly. *)
Definition preorder_gtransport {X} (R : X -> X -> Prop) `{PreOrder X R}
  : GTransport X R :=
  {| GT := fun x y => R x y;
     gt_refl := fun x => reflexivity x;
     gt_compose := fun x y z v w => transitivity v w;
     gt_sound := fun x y w => w |}.

Lemma preorder_complete {X} (R : X -> X -> Prop) `{PreOrder X R} :
  Complete (preorder_gtransport R).
Proof. intros x y H'. exact (inhabits H'). Qed.
