From Coq Require Import List Bool Arith.
Import ListNotations.

Definition Admissible {S O : Type} (M : S -> O) (Phi : S -> bool) : Prop :=
  exists Phi_hat : O -> bool, forall s : S, Phi s = Phi_hat (M s).

Record Span (A B : Type) : Type := mkSpan {
  seam : Type ;
  back : seam -> A ;
  fwd  : seam -> B
}.
Arguments seam {A B}.
Arguments back {A B}.
Arguments fwd  {A B}.

Definition GroundingEquations {A B : Type} (sp : Span A B)
    (Phi_A : A -> bool) (Phi_B : B -> bool)
    (Phi_seam : seam sp -> bool) : Prop :=
  forall r : seam sp,
    Phi_A (back sp r) = Phi_seam r /\ Phi_B (fwd sp r) = Phi_seam r.

Definition Transportable {A B OA OB : Type}
    (sp : Span A B)
    (M_A : A -> OA) (Phi_A : A -> bool)
    (M_B : B -> OB) (Phi_B : B -> bool)
    (Phi_seam : seam sp -> bool)
    (Exhibited LineageGrounded Functorial : Prop) : Prop :=
  inhabited (seam sp)
  /\ Exhibited
  /\ LineageGrounded
  /\ Admissible M_A Phi_A
  /\ Admissible M_B Phi_B
  /\ GroundingEquations sp Phi_A Phi_B Phi_seam
  /\ Functorial.

Record TemporalSystem := {
  time : Type ;
  A : time -> Type ;
  B : time -> Type ;
  sp : forall t, Span (A t) (B t)
}.

Record SeamEvolution (X : TemporalSystem) (t u : time X) : Type :=
  mkSeamEvolution {
    ev_seam : seam (sp X t) -> seam (sp X u) ;
    ev_A    : A X t -> A X u ;
    ev_B    : B X t -> B X u ;
    ev_back_commutes :
      forall r, back (sp X u) (ev_seam r) = ev_A (back (sp X t) r) ;
    ev_fwd_commutes :
      forall r, fwd (sp X u) (ev_seam r) = ev_B (fwd (sp X t) r)
  }.

(* Record parameters are explicit in projections unless declared implicit. *)
Arguments ev_seam {X t u} _ _.
Arguments ev_A {X t u} _ _.
Arguments ev_B {X t u} _ _.
Arguments ev_back_commutes {X t u} _ _.
Arguments ev_fwd_commutes {X t u} _ _.

Definition evolution_id (X : TemporalSystem) (t : time X)
    : SeamEvolution X t t.
Proof.
  refine {| ev_seam := fun r => r ; ev_A := fun a => a ; ev_B := fun b => b |};
    intro r; reflexivity.
Defined.

Definition evolution_compose {X : TemporalSystem} {t u v : time X}
    (e1 : SeamEvolution X t u) (e2 : SeamEvolution X u v)
    : SeamEvolution X t v.
Proof.
  refine {| ev_seam := fun r => ev_seam e2 (ev_seam e1 r) ;
            ev_A    := fun a => ev_A e2 (ev_A e1 a) ;
            ev_B    := fun b => ev_B e2 (ev_B e1 b) |}.
  - intro r. rewrite (ev_back_commutes e2), (ev_back_commutes e1). reflexivity.
  - intro r. rewrite (ev_fwd_commutes e2), (ev_fwd_commutes e1). reflexivity.
Defined.

(* Grounded form of the span criterion with the factor given:
   the stage-t factor, composed with back, computes Phi_B on the seam.
   No decision procedure for admissibility is used. *)
Lemma seam_transport {A B OA : Type} (sp : Span A B)
    (M_A : A -> OA) (Phi_A : A -> bool) (Phi_B : B -> bool)
    (Phi_seam : seam sp -> bool) :
  GroundingEquations sp Phi_A Phi_B Phi_seam ->
  forall h : OA -> bool, (forall a, Phi_A a = h (M_A a)) ->
  forall r : seam sp, Phi_B (fwd sp r) = h (M_A (back sp r)).
Proof.
  intros HG h Hh r. destruct (HG r) as [HA HB].
  rewrite HB, <- HA. apply Hh.
Qed.

(* The same conclusion from the admissibility conjunct of Transportable. *)
Corollary seam_transport_admissible {A B OA : Type} (sp : Span A B)
    (M_A : A -> OA) (Phi_A : A -> bool) (Phi_B : B -> bool)
    (Phi_seam : seam sp -> bool) :
  GroundingEquations sp Phi_A Phi_B Phi_seam ->
  Admissible M_A Phi_A ->
  exists h : OA -> bool,
    forall r : seam sp, Phi_B (fwd sp r) = h (M_A (back sp r)).
Proof.
  intros HG [h Hh]. exists h. exact (seam_transport sp M_A Phi_A Phi_B Phi_seam HG h Hh).
Qed.

(* A seam element on which the coordinate valuations differ
   refutes grounded coherence. *)
Lemma seam_witness_refutes {A B : Type} (sp : Span A B)
    (Phi_A : A -> bool) (Phi_B : B -> bool) (Phi_seam : seam sp -> bool)
    (r : seam sp) :
  Phi_A (back sp r) <> Phi_B (fwd sp r) ->
  ~ GroundingEquations sp Phi_A Phi_B Phi_seam.
Proof.
  intros Hne HG. destruct (HG r) as [HA HB]. apply Hne. congruence.
Qed.

(* A seam element on which a coordinate valuation departs from the
   exhibited seam valuation refutes grounded coherence, even when the
   two coordinate valuations agree there. *)
Lemma grounding_witness_refutes {A B : Type} (sp : Span A B)
    (Phi_A : A -> bool) (Phi_B : B -> bool) (Phi_seam : seam sp -> bool)
    (r : seam sp) :
  Phi_A (back sp r) <> Phi_seam r \/ Phi_B (fwd sp r) <> Phi_seam r ->
  ~ GroundingEquations sp Phi_A Phi_B Phi_seam.
Proof.
  intros [Hne | Hne] HG; destruct (HG r) as [HA HB]; contradiction.
Qed.

(* The copied dual-write counterexample of the ungrounded-agreement
   proposition: coordinates agree everywhere, grounding fails at r_star. *)
Inductive Req := r_ok | r_star.

Definition dual_write : Span Req Req :=
  {| seam := Req ; back := fun r => r ; fwd := fun r => r |}.

Definition copied_status (_ : Req) : bool := true.

Definition trace_status (r : Req) : bool :=
  match r with r_ok => true | r_star => false end.

Lemma copied_extensionally_coherent :
  forall r : seam dual_write,
    copied_status (back dual_write r) = copied_status (fwd dual_write r).
Proof. intro r. reflexivity. Qed.

Lemma copied_not_grounded :
  ~ GroundingEquations dual_write copied_status copied_status trace_status.
Proof.
  apply (grounding_witness_refutes dual_write copied_status copied_status
           trace_status r_star).
  left. discriminate.
Qed.

Definition SquaresOn (carrier : list nat)
    (back_t back_u fwd_t fwd_u cs ca cb : nat -> nat) : Prop :=
  forall r, In r carrier ->
    back_u (cs r) = ca (back_t r) /\
    fwd_u (cs r) = cb (fwd_t r).

Definition squares_bool (carrier : list nat)
    (back_t back_u fwd_t fwd_u cs ca cb : nat -> nat) : bool :=
  forallb (fun r =>
    Nat.eqb (back_u (cs r)) (ca (back_t r)) &&
    Nat.eqb (fwd_u (cs r)) (cb (fwd_t r))) carrier.

Theorem squares_bool_reflect (carrier : list nat)
    (back_t back_u fwd_t fwd_u cs ca cb : nat -> nat) :
  squares_bool carrier back_t back_u fwd_t fwd_u cs ca cb = true <->
  SquaresOn carrier back_t back_u fwd_t fwd_u cs ca cb.
Proof.
  unfold squares_bool, SquaresOn. rewrite forallb_forall. split.
  - intros H r Hr. specialize (H r Hr).
    apply andb_true_iff in H as [Hb Hf].
    apply Nat.eqb_eq in Hb. apply Nat.eqb_eq in Hf. split; assumption.
  - intros H r Hr. destruct (H r Hr) as [Hb Hf].
    apply andb_true_iff. split; apply Nat.eqb_eq; assumption.
Qed.


(* Finite Boolean check of the grounding equations on a declared carrier.
   This is the procedure extracted to OCaml (SeamExtraction.v). *)
Definition GroundingEquationsOn (carrier : list nat) (back fwd : nat -> nat)
    (phi_a phi_b phi_s : nat -> bool) : Prop :=
  forall r, In r carrier ->
    phi_a (back r) = phi_s r /\ phi_b (fwd r) = phi_s r.

Definition grounding_bool (carrier : list nat) (back fwd : nat -> nat)
    (phi_a phi_b phi_s : nat -> bool) : bool :=
  forallb (fun r =>
    Bool.eqb (phi_a (back r)) (phi_s r) &&
    Bool.eqb (phi_b (fwd r)) (phi_s r)) carrier.

Theorem grounding_bool_reflect (carrier : list nat) (back fwd : nat -> nat)
    (phi_a phi_b phi_s : nat -> bool) :
  grounding_bool carrier back fwd phi_a phi_b phi_s = true <->
  GroundingEquationsOn carrier back fwd phi_a phi_b phi_s.
Proof.
  unfold grounding_bool, GroundingEquationsOn. rewrite forallb_forall. split.
  - intros H r Hr. specialize (H r Hr).
    apply andb_true_iff in H as [Ha Hb].
    apply Bool.eqb_prop in Ha. apply Bool.eqb_prop in Hb. split; assumption.
  - intros H r Hr. destruct (H r Hr) as [Ha Hb].
    apply andb_true_iff. split; apply Bool.eqb_true_iff; assumption.
Qed.

Print Assumptions evolution_compose.
Print Assumptions seam_transport.
Print Assumptions seam_transport_admissible.
Print Assumptions seam_witness_refutes.
Print Assumptions grounding_witness_refutes.
Print Assumptions copied_not_grounded.
Print Assumptions squares_bool_reflect.
Print Assumptions grounding_bool_reflect.
