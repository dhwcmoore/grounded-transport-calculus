(** * Continuation is not coverage.

    [PreservesGroundingOnImage] holds for the evolution below, and every
    stage-[false] seam element is grounded, yet the stage-[true] seam has a NEW
    element outside the image of [ev_seam] whose valuation is not grounded.
    New seam elements need new grounding evidence
    ([surjective_evolution_preserves_all_grounding] needs surjectivity). *)

From GTC.Instances Require Import OriginalDynamicSeamInstance.
From Exactness Require Import GroundedSeam.

Definition sp2 (t : bool) : Span unit unit :=
  match t with
  | false => {| seam := unit; back := fun _ => tt; fwd := fun _ => tt |}
  | true  => {| seam := bool; back := fun _ => tt; fwd := fun _ => tt |}
  end.

Definition sys2 : TemporalSystem :=
  {| time := bool; A := fun _ => unit; B := fun _ => unit; sp := sp2 |}.

(** The seam valuation at stage [true] is true only on the image element. *)
Definition V2 : ValuedSystem sys2 :=
  @Build_ValuedSystem sys2 (fun _ _ => true) (fun _ _ => true)
    (fun t : bool => match t return seam (sp2 t) -> bool with
                     | false => fun _ => true
                     | true => fun b : bool => b
                     end).

Definition e2 : SeamEvolution sys2 false true :=
  @mkSeamEvolution sys2 false true (fun _ => true) (fun _ => tt) (fun _ => tt)
    (fun _ => eq_refl) (fun _ => eq_refl).

Lemma grounded_before :
  GroundingEquations (sp sys2 false) (vA V2 false) (vB V2 false) (vS V2 false).
Proof. intro r. split; reflexivity. Qed.

Lemma preserved_on_image : PreservesGroundingOnImage V2 e2.
Proof. intros r [ha hb]. split; reflexivity. Qed.

Lemma image_not_covering : ~ Surjective (ev_seam e2).
Proof.
  intro H. destruct (H false) as [r E]. discriminate E.
Qed.

Lemma new_element_ungrounded : ~ GroundedAt V2 true false.
Proof. intros [Ha _]. discriminate Ha. Qed.

Theorem preservation_without_coverage :
  PreservesGroundingOnImage V2 e2 /\
  GroundingEquations (sp sys2 false) (vA V2 false) (vB V2 false) (vS V2 false) /\
  ~ GroundingEquations (sp sys2 true) (vA V2 true) (vB V2 true) (vS V2 true).
Proof.
  refine (conj preserved_on_image (conj grounded_before _)).
  intro H. exact (new_element_ungrounded (H false)).
Qed.
