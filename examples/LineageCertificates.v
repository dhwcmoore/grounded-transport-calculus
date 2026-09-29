(** * Lineage certificates on small declared graphs (manuscript Definition 13).

    Lineage records are FINITE DATA (lists), so they survive extraction.

    - [indep_lineage d]: coordinates derive from raw inputs 0 and 1, the ground
      from a separate claim-relevant raw input 2.  It passes for every choice
      [d] of declared dispositions; the certificate carries graph, coverage and
      verdict as data.
    - [copy_lineage]: the ground is derived from the coordinate [d_A] (the copy
      pattern of [dual_write]).  It fails (L1): no certificate can exist, and the
      failure is located by an ancestor path.

    These are declared records checked in the kernel.  They are NOT outputs of
    the OCaml audit, and [LineagePasses] is a specification mirroring that audit
    by inspection, not a proved-equivalent implementation. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From GTC.Debt Require Import Certificates.

(** ** An independent ground *)

Definition indep_lineage (d : list (nat * Disposition)) : Lineage :=
  {| lin_derived := [(3, [0]); (4, [1]); (5, [2])];
     lin_raw := [0; 1; 2];
     lin_relevant := [2];
     lin_dA := 3; lin_dB := 4; lin_ground := 5;
     lin_dispositions := d |}.

Section Indep.
  Variable d : list (nat * Disposition).
  Let g := indep_lineage d.

  Lemma indep_anc3 m : Ancestor g 3 m -> m = 0.
  Proof.
    intro H. apply anc_inv in H. cbn in H.
    destruct H as [[E|[]] | (p & [E|[]] & H)].
    - symmetry. exact E.
    - subst p. exfalso. exact (anc_leaf g 0 m eq_refl H).
  Qed.

  Lemma indep_anc4 m : Ancestor g 4 m -> m = 1.
  Proof.
    intro H. apply anc_inv in H. cbn in H.
    destruct H as [[E|[]] | (p & [E|[]] & H)].
    - symmetry. exact E.
    - subst p. exfalso. exact (anc_leaf g 1 m eq_refl H).
  Qed.

  Lemma indep_anc5 m : Ancestor g 5 m -> m = 2.
  Proof.
    intro H. apply anc_inv in H. cbn in H.
    destruct H as [[E|[]] | (p & [E|[]] & H)].
    - symmetry. exact E.
    - subst p. exfalso. exact (anc_leaf g 2 m eq_refl H).
  Qed.

  Lemma indep_parents_lt : forall k p, In p (lin_parents g k) -> p < k.
  Proof.
    intros k p Hp.
    destruct k as [|[|[|[|[|[|k]]]]]]; cbn in Hp;
      try (destruct Hp as [<-|[]]; lia); destruct Hp.
  Qed.

  Lemma indep_wf : LineageWellFormed g.
  Proof.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    - unfold lin_nodes. cbn.
      repeat constructor; cbn; intro H;
        repeat (destruct H as [H|H]; [discriminate H|]); exact H.
    - intros n ps H p Hp. cbn in H.
      destruct H as [E|[E|[E|[]]]]; inversion E; subst; cbn in Hp;
        destruct Hp as [<-|[]]; unfold lin_nodes; cbn; firstorder.
    - cbn. firstorder.
    - cbn. firstorder.
    - unfold lin_nodes. cbn. firstorder.
    - intros n Hn. unfold lin_is_relevant, lin_is_raw in *. cbn in *.
      destruct Hn as [<-|[]]. firstorder.
    - intros n H.
      pose proof (ancestor_rank g (fun n => n)
                    (fun n p Hp => indep_parents_lt n p Hp) n n H) as Hr.
      lia.
  Qed.

  Lemma indep_L1 : L1 g.
  Proof.
    repeat split.
    - cbn. lia.
    - cbn. lia.
    - intro H.
      apply indep_anc5 in H.
      cbn in H.
      lia.
    - intro H.
      apply indep_anc5 in H.
      cbn in H.
      lia.
  Qed.

  Lemma indep_L2 : L2 g.
  Proof.
    intros n H3 H4 Hnr. apply indep_anc3 in H3. apply indep_anc4 in H4. lia.
  Qed.

  Lemma indep_L3 : L3 g.
  Proof.
    exists 2. unfold lin_is_raw, lin_is_relevant. cbn. repeat split.
    - firstorder.
    - left. reflexivity.
    - right. apply anc_parent. cbn. left. reflexivity.
    - intro H. apply indep_anc3 in H. lia.
    - intro H. apply indep_anc4 in H. lia.
    - lia.
    - lia.
  Qed.
End Indep.

Definition indep_certificate (d : list (nat * Disposition)) : LineageCertificate :=
  {| lc_graph := indep_lineage d;
     lc_coverage := {| cov_from := 0; cov_to := 1; cov_gaps := [] |};
     lc_audit := LineagePass; lc_audit_passed := eq_refl; lc_no_gaps := eq_refl;
     lc_wf := indep_wf d; lc_L1 := indep_L1 d; lc_L2 := indep_L2 d;
     lc_L3 := indep_L3 d |}.

(** ** A copied ground *)

(** node 0: raw status; 1: [d_A]; 2: [d_B] (copies [d_A]); 3: ground, derived
    from [d_A]. *)
Definition copy_lineage : Lineage :=
  {| lin_derived := [(1, [0]); (2, [1]); (3, [1])];
     lin_raw := [0]; lin_relevant := [0];
     lin_dA := 1; lin_dB := 2; lin_ground := 3;
     lin_dispositions := [] |}.

(** The ground descends from a coordinate: the located failure. *)
Lemma copy_descends :
  Ancestor copy_lineage (lin_ground copy_lineage) (lin_dA copy_lineage).
Proof. apply anc_parent. cbn. left. reflexivity. Qed.

Lemma copy_fails_L1 : ~ L1 copy_lineage.
Proof.
  intros (_ & _ & H & _).
  exact (H copy_descends).
Qed.

Corollary copy_not_lineage_grounded : ~ LineagePasses copy_lineage.
Proof. intros (_ & H & _). exact (copy_fails_L1 H). Qed.

Corollary copy_has_no_certificate :
  forall c : LineageCertificate, lc_graph c = copy_lineage -> False.
Proof.
  intros c E. pose proof (lc_L1 c) as H. rewrite E in H. exact (copy_fails_L1 H).
Qed.
