(** * Legacy admissibility (Admissibility.v) against the generic obstruction. *)

From Coq Require Import List.
From GTC.Obstructions Require Import FibreObstruction.
Require Exactness.Admissibility.

Section Bridge.
  Context {S O : Type} (M : S -> O) (Phi : S -> bool).

  (** The legacy [Admissible] is the generic [Factors] at [bool]. *)
  Lemma admissible_iff_factors :
    Exactness.Admissibility.Admissible M Phi <-> Factors M Phi.
  Proof. split; intro H; exact H. Qed.

  Lemma fibre_constant_iff :
    Exactness.Admissibility.FibreConstant M Phi <-> ConstantOnFibres M Phi.
  Proof. split; intro H; exact H. Qed.

  (** The legacy [witness_refutes] is an instance of [fibre_obstruction]. *)
  Lemma witness_refutes_from_generic (s1 s2 : S) :
    M s1 = M s2 -> Phi s1 <> Phi s2 ->
    ~ Exactness.Admissibility.Admissible M Phi.
  Proof. exact (fibre_obstruction M Phi s1 s2). Qed.

  (** Constructive finite converse: the legacy theorem, stated in generic
      vocabulary.  Axiom-free. *)
  Theorem finite_constant_factors (enum : list S) (complete : forall s, In s enum)
      (eq_dec : forall o1 o2 : O, {o1 = o2} + {o1 <> o2}) :
    ConstantOnFibres M Phi -> Factors M Phi.
  Proof.
    exact (Exactness.Admissibility.fibre_constant_admissible
             M Phi enum complete eq_dec).
  Qed.
End Bridge.
