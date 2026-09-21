(** * Classical functional converse of fibre factorisation.

    ISOLATED: this file depends on [ClassicalEpsilon] / [Classical_Prop] and is
    NOT part of the axiom-free kernel.  Nothing else in the development imports
    it.  Constructive alternatives: the relational form
    ([FibreObstruction.constant_relational]) and, for finite [S] with decidable
    equality on [O], the legacy [fibre_constant_admissible]
    ([Instances/OriginalAdmissibility.v]). *)

From Coq Require Import Logic.ClassicalEpsilon.
From GTC.Obstructions Require Import FibreObstruction.

Section Classical.
  Context {X O V : Type} (M : X -> O) (Phi : X -> V).

  (** Functional converse; needs an inhabitant of [V] off the image of [M]. *)
  Theorem constant_factors : V -> ConstantOnFibres M Phi -> Factors M Phi.
  Proof.
    intros v0 H.
    exists (fun o =>
      match excluded_middle_informative (exists x, M x = o) with
      | left pf => Phi (proj1_sig (constructive_indefinite_description _ pf))
      | right _ => v0
      end).
    intro x.
    destruct (excluded_middle_informative (exists x', M x' = M x)) as [pf|n].
    - destruct (constructive_indefinite_description _ pf) as [x' Hx'].
      simpl. apply H. symmetry. exact Hx'.
    - exfalso. apply n. exists x. reflexivity.
  Qed.

  Theorem factors_iff_constant : V -> (Factors M Phi <-> ConstantOnFibres M Phi).
  Proof.
    intro v0. split; [exact (factors_constant M Phi) | exact (constant_factors v0)].
  Qed.
End Classical.
