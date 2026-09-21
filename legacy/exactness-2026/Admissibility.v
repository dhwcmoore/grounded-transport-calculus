From Coq Require Import List Bool.
Import ListNotations.

Definition Admissible {S O : Type} (M : S -> O) (Phi : S -> bool) : Prop :=
  exists Phi_hat : O -> bool, forall s : S, Phi s = Phi_hat (M s).

Definition FibreConstant {S O : Type} (M : S -> O) (Phi : S -> bool) : Prop :=
  forall s1 s2 : S, M s1 = M s2 -> Phi s1 = Phi s2.

(* Soundness direction: holds with no further assumption. *)
Lemma admissible_fibre_constant {S O : Type} (M : S -> O) (Phi : S -> bool) :
  Admissible M Phi -> FibreConstant M Phi.
Proof.
  intros [h Hh] s1 s2 Heq. rewrite (Hh s1), (Hh s2), Heq. reflexivity.
Qed.

(* A witness pair refutes admissibility. *)
Lemma witness_refutes {S O : Type} (M : S -> O) (Phi : S -> bool) (s1 s2 : S) :
  M s1 = M s2 -> Phi s1 <> Phi s2 -> ~ Admissible M Phi.
Proof.
  intros Heq Hne Hadm. apply Hne.
  exact (admissible_fibre_constant M Phi Hadm s1 s2 Heq).
Qed.

(* Converse under the constructive assumptions named in the paper:
   a complete finite enumeration of S and decidable equality on O. *)
Section Finite.
  Context {S O : Type} (M : S -> O) (Phi : S -> bool).
  Context (enum : list S) (complete : forall s, In s enum).
  Context (eq_dec : forall o1 o2 : O, {o1 = o2} + {o1 <> o2}).

  Definition phi_hat (o : O) : bool :=
    existsb (fun s => if eq_dec (M s) o then Phi s else false) enum.

  Theorem fibre_constant_admissible :
    FibreConstant M Phi -> Admissible M Phi.
  Proof.
    intro Hfc. exists phi_hat. intro s. unfold phi_hat.
    destruct (Phi s) eqn:Hs.
    - symmetry. apply existsb_exists. exists s. split.
      + apply complete.
      + destruct (eq_dec (M s) (M s)) as [_|n]; [exact Hs | contradiction].
    - symmetry. apply not_true_iff_false. intro Hex.
      apply existsb_exists in Hex. destruct Hex as [s' [_ Hs']].
      destruct (eq_dec (M s') (M s)) as [e|_]; [|discriminate].
      rewrite (Hfc s' s e) in Hs'. rewrite Hs in Hs'. discriminate.
  Qed.
End Finite.


Print Assumptions fibre_constant_admissible.
Print Assumptions witness_refutes.
