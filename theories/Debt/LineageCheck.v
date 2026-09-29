(** * A checked lineage audit, with a reflection theorem.

    [lineage_check] decides the manuscript's Definition 13 (L1-L3, plus
    well-formedness and coverage) on the finite-data [Lineage] of
    [Certificates.v].  It is proved to REFLECT the Prop-level specification:

        lineage_check g c = LineageAccepted  <->  LineagePasses g /\ cov_gaps c = []

    UNCONDITIONALLY (well-formedness is part of what is checked).  A rejection
    is LOCATED ([LineageDefect]) and its evidence is proved ([defect_sound]).
    [issue_certificate] builds a kernel-checked [LineageCertificate] from an
    accepted check, so the extracted checker constructs certificates whose types
    are certified.

    What this does and does not establish.  It connects the Coq specification to
    a Coq algorithm.  It does NOT connect either to the handwritten OCaml audit in
    legacy/exactness-2026/jurisdiction.ml; that comparison is the regression
    in extraction/lineage_regression.ml (a test, not a theorem).  Nor does it
    show the declared graph contains every real production path.

    Ancestors are computed by saturation: [ancestors] iterates a de-duplicating
    closure step [length nodes] times.  Completeness needs only that every
    parent is a declared node; it uses a pigeonhole argument. *)

From Coq Require Import List Arith Bool Lia.
Import ListNotations.
From GTC.Debt Require Import Certificates.

Section Ancestors.
  Variable g : Lineage.

  Definition mem (x : nat) (l : list nat) : bool := existsb (Nat.eqb x) l.

  Lemma mem_iff x l : mem x l = true <-> In x l.
  Proof.
    unfold mem. rewrite existsb_exists. split.
    - intros (y & Hy & E). apply Nat.eqb_eq in E. subst. exact Hy.
    - intro H. exists x. split; [exact H | apply Nat.eqb_refl].
  Qed.

  Fixpoint nodupb (l : list nat) : bool :=
    match l with [] => true | x :: t => negb (mem x t) && nodupb t end.

  Lemma nodupb_iff l : nodupb l = true <-> NoDup l.
  Proof.
    induction l as [|x t IH]; cbn.
    - split; [intros _; constructor | reflexivity].
    - rewrite Bool.andb_true_iff, Bool.negb_true_iff, IH, NoDup_cons_iff. split.
      + intros [Hm Hn]. split; [|exact Hn].
        intro H. apply mem_iff in H. rewrite H in Hm. discriminate.
      + intros [Hi Hn]. split; [|exact Hn].
        destruct (mem x t) eqn:E; [exfalso; apply Hi, mem_iff; exact E | reflexivity].
  Qed.

  Definition step (l : list nat) : list nat :=
    nodup Nat.eq_dec (l ++ flat_map (lin_parents g) l).

  Fixpoint iter (k : nat) (l : list nat) : list nat :=
    match k with 0 => l | S k' => step (iter k' l) end.

  Definition seed (n : nat) : list nat := nodup Nat.eq_dec (lin_parents g n).

  Definition ancestors (n : nat) : list nat :=
    iter (length (lin_nodes g)) (seed n).

  (** ** Soundness (no hypothesis) *)

  Lemma anc_snoc n p m : Ancestor g n p -> In m (lin_parents g p) -> Ancestor g n m.
  Proof.
    intro H. induction H as [n p Hp | n q p Hq H IH]; intro Hm.
    - exact (anc_step g n p m Hp (anc_parent g p m Hm)).
    - exact (anc_step g n q m Hq (IH Hm)).
  Qed.

  Lemma iter_sound n k : forall m, In m (iter k (seed n)) -> Ancestor g n m.
  Proof.
    induction k as [|k IH]; cbn; intros m H.
    - apply nodup_In in H. exact (anc_parent g n m H).
    - unfold step in H. apply nodup_In in H. apply in_app_iff in H.
      destruct H as [H|H].
      + exact (IH m H).
      + apply in_flat_map in H as (p & Hp & Hm). exact (anc_snoc n p m (IH p Hp) Hm).
  Qed.

  Theorem ancestors_sound n m : In m (ancestors n) -> Ancestor g n m.
  Proof. exact (iter_sound n _ m). Qed.

  (** ** Completeness, given that every parent is declared *)

  Definition DeclParents : Prop :=
    forall p q, In q (lin_parents g p) -> In q (lin_nodes g).

  Variable HD : DeclParents.
  Variable n : nat.

  Let S (k : nat) : list nat := iter k (seed n).

  Lemma S_nodup k : NoDup (S k).
  Proof. destruct k; [apply NoDup_nodup | apply NoDup_nodup]. Qed.

  Lemma S_declared k : incl (S k) (lin_nodes g).
  Proof.
    induction k as [|k IH]; intros x Hx.
    - apply nodup_In in Hx. exact (HD n x Hx).
    - unfold S in Hx. cbn in Hx. unfold step in Hx. apply nodup_In in Hx.
      apply in_app_iff in Hx. destruct Hx as [Hx|Hx].
      + exact (IH x Hx).
      + apply in_flat_map in Hx as (p & _ & Hq). exact (HD p x Hq).
  Qed.

  Lemma S_mono k : incl (S k) (S (Datatypes.S k)).
  Proof.
    intros x Hx. unfold S. cbn. unfold step. apply nodup_In. apply in_or_app. left. exact Hx.
  Qed.

  Lemma S_parents k : forall p q, In p (S k) -> In q (lin_parents g p) -> In q (S (Datatypes.S k)).
  Proof.
    intros p q Hp Hq. unfold S. cbn. unfold step. apply nodup_In. apply in_or_app. right.
    apply in_flat_map. exists p. split; assumption.
  Qed.

  Definition stable (k : nat) : Prop := incl (S (Datatypes.S k)) (S k).

  (** Constructive: a failed inclusion returns its witness. *)
  Lemma incl_dec (l l' : list nat) :
    {incl l l'} + {exists x, In x l /\ ~ In x l'}.
  Proof.
    induction l as [|a l IH].
    - left. intros x [].
    - destruct (in_dec Nat.eq_dec a l') as [Ha|Ha].
      + destruct IH as [IH|IH].
        * left. intros x [<-|Hx]; [exact Ha | exact (IH x Hx)].
        * right. destruct IH as (x & Hx & Hn).
          exists x. split; [exact (or_intror Hx) | exact Hn].
      + right. exists a. split; [exact (or_introl eq_refl) | exact Ha].
  Qed.

  Lemma stable_from k : stable k -> forall j, incl (S (k + j)) (S k).
  Proof.
    intro Hs. induction j as [|j IH].
    - rewrite Nat.add_0_r. intros x Hx. exact Hx.
    - intros x Hx. rewrite Nat.add_succ_r in Hx. unfold S in Hx. cbn in Hx.
      unfold step in Hx. apply nodup_In in Hx. apply in_app_iff in Hx.
      destruct Hx as [Hx|Hx].
      + exact (IH x Hx).
      + apply in_flat_map in Hx as (p & Hp & Hq).
        apply Hs. exact (S_parents (k) p x (IH p Hp) Hq).
  Qed.

  Lemma mono_le i j : i <= j -> incl (S i) (S j).
  Proof.
    induction 1 as [|j Hij IH].
    - intros x Hx. exact Hx.
    - intros x Hx. exact (S_mono j x (IH x Hx)).
  Qed.

  (** Counting: if nothing stabilises before [j], the sets have grown by one at
      every step. *)
  Lemma growth j : (forall i, i < j -> ~ stable i) -> j <= length (S j).
  Proof.
    induction j as [|j IH]; intro H.
    - lia.
    - assert (IHj : j <= length (S j)) by (apply IH; intros i Hi; apply H; lia).
      assert (Hns : ~ stable j) by (apply H; lia).
      unfold stable in Hns.
      destruct (incl_dec (S (Datatypes.S j)) (S j)) as [Hi|(x & Hx1 & Hx2)];
        [contradiction|].
      assert (Hlen : length (x :: S j) <= length (S (Datatypes.S j))).
      { apply NoDup_incl_length.
        - constructor; [exact Hx2 | apply S_nodup].
        - intros y [<-|Hy]; [exact Hx1 | exact (S_mono j y Hy)]. }
      change (length (x :: S j)) with (Datatypes.S (length (S j))) in Hlen.
      lia.
  Qed.

  Lemma exists_stable : forall j, (forall i, i < j -> ~ stable i) \/ (exists i, i < j /\ stable i).
  Proof.
    induction j as [|j IH].
    - left. intros i Hi. lia.
    - destruct IH as [IH|(i & Hi & Hs)].
      + destruct (incl_dec (S (Datatypes.S j)) (S j)) as [Hs|(x & Hx1 & Hx2)].
        * right. exists j. split; [lia | exact Hs].
        * left. intros i Hi. destruct (Nat.eq_dec i j) as [->|Hne].
          -- intro Hs. exact (Hx2 (Hs x Hx1)).
          -- apply IH. lia.
      + right. exists i. split; [lia | exact Hs].
  Qed.

  Let N := length (lin_nodes g).

  Lemma stable_by_N : exists i, i <= N /\ stable i.
  Proof.
    destruct (exists_stable (Datatypes.S N)) as [H|(i & Hi & Hs)].
    - exfalso. pose proof (growth (Datatypes.S N) H) as Hg.
      assert (Hle : length (S (Datatypes.S N)) <= N).
      { apply NoDup_incl_length; [apply S_nodup | apply S_declared]. }
      lia.
    - exists i. split; [lia | exact Hs].
  Qed.

  (** The final set is closed under taking parents. *)
  Lemma final_closed : forall p q, In p (S N) -> In q (lin_parents g p) -> In q (S N).
  Proof.
    intros p q Hp Hq.
    destruct stable_by_N as (i & Hi & Hs).
    pose proof (S_parents N p q Hp Hq) as Hq'.
    assert (Hin : incl (S (Datatypes.S N)) (S i)).
    { replace (Datatypes.S N) with (i + (Datatypes.S N - i)) by lia.
      exact (stable_from i Hs (Datatypes.S N - i)). }
    exact (mono_le i N Hi q (Hin q Hq')).
  Qed.

  Lemma seed_in_final : incl (seed n) (S N).
  Proof. intros x Hx. exact (mono_le 0 N (Nat.le_0_l N) x Hx). Qed.

  Lemma anc_in_final : forall a m, Ancestor g a m -> (a = n \/ In a (S N)) -> In m (S N).
  Proof.
    intros a m H. induction H as [a m Hm | a p m Hp H IH]; intro Ha.
    - destruct Ha as [->|Ha].
      + apply seed_in_final. unfold seed. apply nodup_In. exact Hm.
      + exact (final_closed a m Ha Hm).
    - assert (Hp' : In p (S N)).
      { destruct Ha as [->|Ha].
        - apply seed_in_final. unfold seed. apply nodup_In. exact Hp.
        - exact (final_closed a p Ha Hp). }
      exact (IH (or_intror Hp')).
  Qed.

  Theorem ancestors_complete_aux : forall m, Ancestor g n m -> In m (S N).
  Proof. intros m H. exact (anc_in_final n m H (or_introl eq_refl)). Qed.
End Ancestors.

Theorem ancestors_complete (g : Lineage) : DeclParents g ->
  forall n m, Ancestor g n m -> In m (ancestors g n).
Proof. intros HD n m H. exact (ancestors_complete_aux g HD n m H). Qed.

Corollary ancestors_iff (g : Lineage) : DeclParents g ->
  forall n m, In m (ancestors g n) <-> Ancestor g n m.
Proof.
  intros HD n m. split; [apply ancestors_sound | apply ancestors_complete; exact HD].
Qed.

(** * The checks and their reflection *)

Inductive WfDefect : Type :=
| DuplicateNode | UndeclaredParent | DistinguishedNotDerived | RelevantNotRaw
| Cycle (n : nat).

Inductive LineageDefect : Type :=
| Malformed (d : WfDefect)
| GroundEqualsA
| GroundEqualsB
| DescentFromA
| DescentFromB
| UndisclosedShared (n : nat)
| NoIndependentSource.

Inductive LineageDecision : Type :=
| LineageAccepted
| LineageRejected (d : LineageDefect)
| LineageOpen (gaps : list nat).

Section Checks.
  Variable g : Lineage.

  (** ** Parents are declared *)

  Definition DeclEntries : Prop :=
    forall n ps, In (n, ps) (lin_derived g) -> forall p, In p ps -> In p (lin_nodes g).

  Lemma parents_entry n : forall m, In m (lin_parents g n) ->
    exists e, In e (lin_derived g) /\ fst e = n /\ In m (snd e).
  Proof.
    intros m Hm. unfold lin_parents in Hm.
    destruct (find (fun e => Nat.eqb (fst e) n) (lin_derived g)) as [e|] eqn:E.
    - apply find_some in E as [Hin Heq]. apply Nat.eqb_eq in Heq.
      exists e. repeat split; assumption.
    - destruct Hm.
  Qed.

  Lemma anc_key n m : Ancestor g n m -> In n (map fst (lin_derived g)).
  Proof.
    intro H. assert (Hk : exists m', In m' (lin_parents g n)).
    { destruct H as [n m Hm | n p m Hp _]; [exists m; exact Hm | exists p; exact Hp]. }
    destruct Hk as [m' Hm'].
    destruct (parents_entry n m' Hm') as (e & Hin & Hfst & _).
    apply in_map_iff. exists e. split; assumption.
  Qed.

  Lemma decl_parents_of_entries : DeclEntries -> DeclParents g.
  Proof.
    intros HE p q Hq. destruct (parents_entry p q Hq) as ([k ps] & Hin & Hk & Hqs).
    cbn in Hk, Hqs. subst k. exact (HE p ps Hin q Hqs).
  Qed.

  Definition declared_parents_b : bool :=
    forallb (fun e => forallb (fun p => mem p (lin_nodes g)) (snd e)) (lin_derived g).

  Lemma declared_parents_iff : declared_parents_b = true <-> DeclEntries.
  Proof.
    unfold declared_parents_b, DeclEntries. rewrite forallb_forall. split.
    - intros H n ps Hin p Hp. specialize (H _ Hin). cbn in H.
      rewrite forallb_forall in H. apply mem_iff. exact (H p Hp).
    - intros H e Hin. rewrite forallb_forall. intros p Hp.
      apply mem_iff. destruct e as [n ps]. exact (H n ps Hin p Hp).
  Qed.

  (** ** Well-formedness *)

  Definition distinguished_b : bool :=
    mem (lin_dA g) (map fst (lin_derived g)) &&
    mem (lin_dB g) (map fst (lin_derived g)) &&
    mem (lin_ground g) (lin_nodes g).
  Definition relevant_b : bool := forallb (fun n => mem n (lin_raw g)) (lin_relevant g).
  Definition cycle_at : option nat :=
    find (fun n => mem n (ancestors g n)) (lin_nodes g).

  Definition wf_defect : option WfDefect :=
    if nodupb (lin_nodes g) then
      if declared_parents_b then
        if distinguished_b then
          if relevant_b then
            match cycle_at with Some n => Some (Cycle n) | None => None end
          else Some RelevantNotRaw
        else Some DistinguishedNotDerived
      else Some UndeclaredParent
    else Some DuplicateNode.

  Lemma distinguished_iff : distinguished_b = true <->
    In (lin_dA g) (map fst (lin_derived g)) /\
    In (lin_dB g) (map fst (lin_derived g)) /\
    In (lin_ground g) (lin_nodes g).
  Proof.
    unfold distinguished_b. rewrite !Bool.andb_true_iff, !mem_iff.
    tauto.
  Qed.

  Lemma relevant_iff : relevant_b = true <->
    (forall n, lin_is_relevant g n -> lin_is_raw g n).
  Proof.
    unfold relevant_b, lin_is_relevant, lin_is_raw. rewrite forallb_forall. split;
      intros H n Hn; apply mem_iff; apply H; exact Hn.
  Qed.

  Theorem wf_defect_none_iff : wf_defect = None <-> LineageWellFormed g.
  Proof.
    unfold wf_defect. split.
    - intro H.
      destruct (nodupb (lin_nodes g)) eqn:Hnd0; [|discriminate].
      pose proof (proj1 (nodupb_iff _) Hnd0) as Hnd.
      destruct declared_parents_b eqn:Hdp; [|discriminate].
      destruct distinguished_b eqn:Hd; [|discriminate].
      destruct relevant_b eqn:Hr; [|discriminate].
      destruct cycle_at as [c|] eqn:Hc; [discriminate|].
      pose proof (proj1 declared_parents_iff Hdp) as Hdp2.
      destruct (proj1 distinguished_iff Hd) as (HdA & HdB & Hg).
      pose proof (proj1 relevant_iff Hr) as Hr2.
      unfold LineageWellFormed.
      split; [exact Hnd |].
      split; [exact Hdp2 |].
      split; [exact HdA |].
      split; [exact HdB |].
      split; [exact Hg |].
      split; [exact Hr2 |].
      intros x Hx.
      assert (Hin : In x (lin_nodes g))
        by (unfold lin_nodes; apply in_or_app; left; exact (anc_key x x Hx)).
      pose proof (ancestors_complete g (decl_parents_of_entries Hdp2) x x Hx) as Hm0.
      pose proof (proj2 (mem_iff x (ancestors g x)) Hm0) as Hm.
      unfold cycle_at in Hc. pose proof (find_none _ _ Hc x Hin) as Hf.
      cbn in Hf. rewrite Hm in Hf. discriminate Hf.
    - intros (Hnd & Hdp & HdA & HdB & Hg & Hr & Hac).
      assert (E0 : nodupb (lin_nodes g) = true) by (apply nodupb_iff; exact Hnd).
      rewrite E0.
      assert (E1 : declared_parents_b = true) by (apply declared_parents_iff; exact Hdp).
      rewrite E1.
      assert (E2 : distinguished_b = true) by (apply distinguished_iff; exact (conj HdA (conj HdB Hg))).
      rewrite E2.
      assert (E3 : relevant_b = true) by (apply relevant_iff; exact Hr).
      rewrite E3.
      destruct cycle_at as [c|] eqn:Hc; [|reflexivity].
      exfalso. unfold cycle_at in Hc. apply find_some in Hc as [_ Hm].
      apply mem_iff in Hm. exact (Hac c (ancestors_sound g c c Hm)).
  Qed.

  (** ** L1, L2, L3, under declared parents *)

  Hypothesis HD : DeclParents g.

  Lemma anc_mem a m : mem m (ancestors g a) = true <-> Ancestor g a m.
  Proof. rewrite mem_iff. apply ancestors_iff. exact HD. Qed.

  Definition descends_a : bool := mem (lin_dA g) (ancestors g (lin_ground g)).
  Definition descends_b : bool := mem (lin_dB g) (ancestors g (lin_ground g)).

  Definition ground_eq_a : bool :=
    Nat.eqb (lin_ground g) (lin_dA g).

  Definition ground_eq_b : bool :=
    Nat.eqb (lin_ground g) (lin_dB g).

  Definition check_L1 : bool :=
    negb ground_eq_a &&
    negb ground_eq_b &&
    negb descends_a &&
    negb descends_b.

  Theorem check_L1_reflect : check_L1 = true <-> L1 g.
  Proof.
    unfold check_L1, ground_eq_a, ground_eq_b,
      descends_a, descends_b, L1.
    rewrite !Bool.andb_true_iff, !Bool.negb_true_iff.
    split.
    - intros [[[Hga Hgb] Ha] Hb].
      repeat split.
      + intro E.
        rewrite E, Nat.eqb_refl in Hga.
        discriminate.
      + intro E.
        rewrite E, Nat.eqb_refl in Hgb.
        discriminate.
      + intro H.
        apply anc_mem in H.
        rewrite H in Ha.
        discriminate.
      + intro H.
        apply anc_mem in H.
        rewrite H in Hb.
        discriminate.
    - intros (Hga & Hgb & Ha & Hb).
      repeat split.
      + destruct (Nat.eqb (lin_ground g) (lin_dA g)) eqn:E.
        * exfalso.
          apply Hga.
          apply Nat.eqb_eq.
          exact E.
        * reflexivity.
      + destruct (Nat.eqb (lin_ground g) (lin_dB g)) eqn:E.
        * exfalso.
          apply Hgb.
          apply Nat.eqb_eq.
          exact E.
        * reflexivity.
      + destruct (mem (lin_dA g) (ancestors g (lin_ground g))) eqn:E.
        * exfalso.
          apply Ha, anc_mem.
          exact E.
        * reflexivity.
      + destruct (mem (lin_dB g) (ancestors g (lin_ground g))) eqn:E.
        * exfalso.
          apply Hb, anc_mem.
          exact E.
        * reflexivity.
  Qed.

  Definition disposed_b (n : nat) : bool :=
    existsb (fun e => Nat.eqb (fst e) n) (lin_dispositions g).

  Lemma disposed_iff n : disposed_b n = true <-> lin_disposed g n.
  Proof.
    unfold disposed_b, lin_disposed. rewrite existsb_exists. split.
    - intros ([k d] & Hin & E). cbn in E. apply Nat.eqb_eq in E. subst k.
      exists d. exact Hin.
    - intros [d Hd]. exists (n, d). split; [exact Hd | cbn; apply Nat.eqb_refl].
  Qed.

  Definition undisclosed_pred (n : nat) : bool :=
    mem n (ancestors g (lin_dB g)) && negb (mem n (lin_raw g)) && negb (disposed_b n).

  Definition undisclosed : option nat :=
    find undisclosed_pred (ancestors g (lin_dA g)).

  Lemma undisclosed_pred_iff n :
    undisclosed_pred n = true <->
    Ancestor g (lin_dB g) n /\ ~ lin_is_raw g n /\ ~ lin_disposed g n.
  Proof.
    unfold undisclosed_pred. rewrite !Bool.andb_true_iff, !Bool.negb_true_iff.
    rewrite anc_mem. unfold lin_is_raw. split.
    - intros [[Hb Hr] Hd]. refine (conj Hb (conj _ _)).
      + intro H. apply mem_iff in H. rewrite H in Hr. discriminate.
      + intro H. apply disposed_iff in H. rewrite H in Hd. discriminate.
    - intros (Hb & Hr & Hd). refine (conj (conj Hb _) _).
      + destruct (mem n (lin_raw g)) eqn:E; [exfalso; apply Hr, mem_iff; exact E | reflexivity].
      + destruct (disposed_b n) eqn:E; [exfalso; apply Hd, disposed_iff; exact E | reflexivity].
  Qed.

  Theorem undisclosed_none_iff : undisclosed = None <-> L2 g.
  Proof.
    unfold undisclosed, L2. split.
    - intros H n Ha Hb Hr.
      assert (Hin : In n (ancestors g (lin_dA g))) by (apply mem_iff, anc_mem; exact Ha).
      pose proof (find_none _ _ H n Hin) as Hf.
      destruct (disposed_b n) eqn:E.
      + apply disposed_iff. exact E.
      + exfalso. assert (Hp : undisclosed_pred n = true).
        { apply undisclosed_pred_iff. refine (conj Hb (conj Hr _)).
          intro Hd. apply disposed_iff in Hd. rewrite E in Hd. discriminate. }
        rewrite Hp in Hf. discriminate Hf.
    - intro H. destruct (find undisclosed_pred (ancestors g (lin_dA g))) as [n|] eqn:E;
        [|reflexivity].
      exfalso. apply find_some in E as [Hin Hp].
      apply undisclosed_pred_iff in Hp as (Hb & Hr & Hd).
      apply Hd. apply (H n).
      + exact (ancestors_sound g _ _ Hin).
      + exact Hb.
      + exact Hr.
  Qed.

  Theorem undisclosed_some_evidence n : undisclosed = Some n ->
    Ancestor g (lin_dA g) n /\ Ancestor g (lin_dB g) n /\
    ~ lin_is_raw g n /\ ~ lin_disposed g n.
  Proof.
    unfold undisclosed. intro E. apply find_some in E as [Hin Hp].
    apply undisclosed_pred_iff in Hp as (Hb & Hr & Hd).
    exact (conj (ancestors_sound g _ _ Hin) (conj Hb (conj Hr Hd))).
  Qed.

  Definition source_pred (n : nat) : bool :=
    mem n (lin_raw g) && mem n (lin_relevant g) &&
    negb (mem n (ancestors g (lin_dA g))) && negb (mem n (ancestors g (lin_dB g))) &&
    negb (Nat.eqb n (lin_dA g)) && negb (Nat.eqb n (lin_dB g)).

  Definition check_L3 : bool :=
    existsb source_pred (lin_ground g :: ancestors g (lin_ground g)).

  Theorem check_L3_reflect : check_L3 = true <-> L3 g.
  Proof.
    unfold check_L3, L3. rewrite existsb_exists. split.
    - intros (n & Hin & Hp).
      unfold source_pred in Hp.
      rewrite !Bool.andb_true_iff, !Bool.negb_true_iff, !Nat.eqb_neq in Hp.
      destruct Hp as [[[[[Hr Hv] Ha] Hb] Hna] Hnb].
      exists n. unfold lin_is_raw, lin_is_relevant.
      refine
        (conj (proj1 (mem_iff _ _) Hr)
          (conj (proj1 (mem_iff _ _) Hv)
            (conj _ (conj _ (conj _ (conj _ _)))))).
      + destruct Hin as [Hg | Hin].
        * left. symmetry. exact Hg.
        * right. exact (ancestors_sound g _ _ Hin).
      + intro H. apply anc_mem in H. rewrite H in Ha. discriminate.
      + intro H. apply anc_mem in H. rewrite H in Hb. discriminate.
      + exact Hna.
      + exact Hnb.
    - intros (n & Hr & Hv & Hg & Ha & Hb & Hna & Hnb).
      exists n. split.
      + destruct Hg as [Hg | Hg].
        * left. symmetry. exact Hg.
        * right. apply mem_iff, anc_mem. exact Hg.
      + unfold source_pred.
        rewrite !Bool.andb_true_iff, !Bool.negb_true_iff, !Nat.eqb_neq.
        unfold lin_is_raw, lin_is_relevant in *.
        refine (conj (conj (conj (conj (conj _ _) _) _) Hna) Hnb).
        * apply mem_iff. exact Hr.
        * apply mem_iff. exact Hv.
        * destruct (mem n (ancestors g (lin_dA g))) eqn:E.
          -- exfalso. apply Ha, anc_mem. exact E.
          -- reflexivity.
        * destruct (mem n (ancestors g (lin_dB g))) eqn:E.
          -- exfalso. apply Hb, anc_mem. exact E.
          -- reflexivity.
  Qed.
End Checks.

(** ** The defect, its evidence, and the decision *)

Definition lineage_defect (g : Lineage) : option LineageDefect :=
  match wf_defect g with
  | Some d => Some (Malformed d)
  | None =>
      if ground_eq_a g then Some GroundEqualsA
      else if ground_eq_b g then Some GroundEqualsB
      else if descends_a g then Some DescentFromA
      else if descends_b g then Some DescentFromB
      else match undisclosed g with
           | Some n => Some (UndisclosedShared n)
           | None => if check_L3 g then None else Some NoIndependentSource
           end
  end.

Definition WfEvidence (g : Lineage) (d : WfDefect) : Prop :=
  match d with
  | DuplicateNode => ~ NoDup (lin_nodes g)
  | UndeclaredParent => ~ DeclEntries g
  | DistinguishedNotDerived =>
      ~ (In (lin_dA g) (map fst (lin_derived g)) /\
         In (lin_dB g) (map fst (lin_derived g)) /\
         In (lin_ground g) (lin_nodes g))
  | RelevantNotRaw => ~ (forall n, lin_is_relevant g n -> lin_is_raw g n)
  | Cycle n => Ancestor g n n
  end.

Definition DefectEvidence (g : Lineage) (d : LineageDefect) : Prop :=
  match d with
  | Malformed w => WfEvidence g w
  | GroundEqualsA => lin_ground g = lin_dA g
  | GroundEqualsB => lin_ground g = lin_dB g
  | DescentFromA => Ancestor g (lin_ground g) (lin_dA g)
  | DescentFromB => Ancestor g (lin_ground g) (lin_dB g)
  | UndisclosedShared n =>
      Ancestor g (lin_dA g) n /\ Ancestor g (lin_dB g) n /\
      ~ lin_is_raw g n /\ ~ lin_disposed g n
  | NoIndependentSource => ~ L3 g
  end.

Lemma wf_defect_evidence g w : wf_defect g = Some w -> WfEvidence g w.
Proof.
  unfold wf_defect.
  destruct (nodupb (lin_nodes g)) eqn:Hnd.
  - destruct (declared_parents_b g) eqn:Hdp.
    + destruct (distinguished_b g) eqn:Hd.
      * destruct (relevant_b g) eqn:Hr.
        -- destruct (cycle_at g) as [c|] eqn:Hc; intro H; [|discriminate].
           injection H as <-. unfold WfEvidence.
           unfold cycle_at in Hc. apply find_some in Hc as [_ Hm].
           apply mem_iff in Hm. exact (ancestors_sound g _ _ Hm).
        -- intro H. injection H as <-. cbn. intro H'. apply (proj2 (relevant_iff g)) in H'.
           rewrite Hr in H'. discriminate.
      * intro H. injection H as <-. cbn. intro H'. apply (proj2 (distinguished_iff g)) in H'.
        rewrite Hd in H'. discriminate.
    + intro H. injection H as <-. cbn. intro H'. apply (proj2 (declared_parents_iff g)) in H'.
      rewrite Hdp in H'. discriminate.
  - intro H. injection H as <-. cbn. intro H'. apply (proj2 (nodupb_iff _)) in H'.
    rewrite Hnd in H'. discriminate.
Qed.

Theorem defect_sound g d : lineage_defect g = Some d -> DefectEvidence g d.
Proof.
  unfold lineage_defect.
  destruct (wf_defect g) as [w|] eqn:Hw.
  - intro H. injection H as <-. exact (wf_defect_evidence g w Hw).
  - pose proof (proj1 (wf_defect_none_iff g) Hw) as (_ & Hdp & _).
    pose proof (decl_parents_of_entries g Hdp) as HD.
    destruct (ground_eq_a g) eqn:Hga.
    + intro H. injection H as <-. cbn.
      unfold ground_eq_a in Hga.
      apply Nat.eqb_eq in Hga.
      exact Hga.
    + destruct (ground_eq_b g) eqn:Hgb.
      * intro H. injection H as <-. cbn.
        unfold ground_eq_b in Hgb.
        apply Nat.eqb_eq in Hgb.
        exact Hgb.
      * destruct (descends_a g) eqn:Ha.
        -- intro H. injection H as <-. cbn.
           apply (anc_mem g HD). exact Ha.
        -- destruct (descends_b g) eqn:Hb.
           ++ intro H. injection H as <-. cbn.
              apply (anc_mem g HD). exact Hb.
           ++ destruct (undisclosed g) as [n|] eqn:Hu.
              ** intro H. injection H as <-.
                 exact (undisclosed_some_evidence g HD n Hu).
              ** destruct (check_L3 g) eqn:H3; intro H; [discriminate|].
                 injection H as <-. cbn. intro H'.
                 apply (check_L3_reflect g HD) in H'.
                 rewrite H3 in H'. discriminate.
Qed.

Theorem lineage_defect_none_iff g : lineage_defect g = None <-> LineagePasses g.
Proof.
  unfold lineage_defect, LineagePasses. split.
  - intro H.
    destruct (wf_defect g) as [w|] eqn:Hw; [discriminate|].
    pose proof (proj1 (wf_defect_none_iff g) Hw) as Hwf.
    pose proof (decl_parents_of_entries g (proj1 (proj2 Hwf))) as HD.
    destruct (ground_eq_a g) eqn:Hga; [discriminate|].
    destruct (ground_eq_b g) eqn:Hgb; [discriminate|].
    destruct (descends_a g) eqn:Ha; [discriminate|].
    destruct (descends_b g) eqn:Hb; [discriminate|].
    destruct (undisclosed g) as [n|] eqn:Hu; [discriminate|].
    destruct (check_L3 g) eqn:H3; [|discriminate].
    refine (conj Hwf (conj _ (conj _ _))).
    + apply (check_L1_reflect g HD).
      unfold check_L1.
      rewrite Hga, Hgb, Ha, Hb.
      reflexivity.
    + apply (undisclosed_none_iff g HD). exact Hu.
    + apply (check_L3_reflect g HD). exact H3.
  - intros (Hwf & L1h & L2h & L3h).
    assert (Hw : wf_defect g = None) by
      (apply wf_defect_none_iff; exact Hwf).
    pose proof (decl_parents_of_entries g (proj1 (proj2 Hwf))) as HD.
    rewrite Hw.

    apply (check_L1_reflect g HD) in L1h.
    unfold check_L1 in L1h.

    apply Bool.andb_true_iff in L1h as [H123 Hb].
    apply Bool.andb_true_iff in H123 as [H12 Ha].
    apply Bool.andb_true_iff in H12 as [Hga Hgb].

    apply Bool.negb_true_iff in Hga.
    apply Bool.negb_true_iff in Hgb.
    apply Bool.negb_true_iff in Ha.
    apply Bool.negb_true_iff in Hb.

    rewrite Hga, Hgb, Ha, Hb.

    assert (Hu : undisclosed g = None) by
      (apply (undisclosed_none_iff g HD); exact L2h).
    rewrite Hu.

    assert (H3 : check_L3 g = true) by
      (apply (check_L3_reflect g HD); exact L3h).
    rewrite H3.
    reflexivity.
Qed.

Definition lineage_check (g : Lineage) (c : CoverageRecord) : LineageDecision :=
  match lineage_defect g with
  | Some d => LineageRejected d
  | None => match cov_gaps c with [] => LineageAccepted | gs => LineageOpen gs end
  end.

(** Reflection, unconditional. *)
Theorem lineage_check_reflect g c :
  lineage_check g c = LineageAccepted <-> LineagePasses g /\ cov_gaps c = [].
Proof.
  unfold lineage_check. split.
  - destruct (lineage_defect g) as [d|] eqn:Hd; [discriminate|].
    destruct (cov_gaps c) as [|x gs] eqn:Hg; [|discriminate].
    intros _. split; [apply lineage_defect_none_iff; exact Hd | reflexivity].
  - intros [Hp Hg]. apply lineage_defect_none_iff in Hp. rewrite Hp, Hg. reflexivity.
Qed.

Theorem lineage_check_rejected g c d :
  lineage_check g c = LineageRejected d -> DefectEvidence g d /\ ~ LineagePasses g.
Proof.
  unfold lineage_check. destruct (lineage_defect g) as [d'|] eqn:Hd.
  - intro H. injection H as <-. split; [exact (defect_sound g _ Hd) |].
    intro Hp. apply lineage_defect_none_iff in Hp. rewrite Hp in Hd. discriminate.
  - destruct (cov_gaps c); discriminate.
Qed.

(** Open is coverage-qualified only: the graph passes, but gaps remain. *)
Theorem lineage_check_open g c gs :
  lineage_check g c = LineageOpen gs <-> LineagePasses g /\ cov_gaps c = gs /\ gs <> [].
Proof.
  unfold lineage_check. split.
  - destruct (lineage_defect g) as [d|] eqn:Hd; [discriminate|].
    destruct (cov_gaps c) as [|x l] eqn:Hg; [discriminate|].
    intro H. injection H as <-. split; [apply lineage_defect_none_iff; exact Hd |].
    split; [reflexivity | discriminate].
  - intros (Hp & Hg & Hne). apply lineage_defect_none_iff in Hp. rewrite Hp, Hg.
    destruct gs; [contradiction | reflexivity].
Qed.

(** The certified certificate issuer.  An accepted check yields a kernel-checked
    [LineageCertificate]; the graph and coverage are carried as data. *)
Definition build_certificate (g : Lineage) (c : CoverageRecord)
    (Hp : LineagePasses g) (Hg : cov_gaps c = []) : LineageCertificate :=
  {| lc_graph := g; lc_coverage := c; lc_audit := LineagePass;
     lc_audit_passed := eq_refl; lc_no_gaps := Hg;
     lc_wf := proj1 Hp; lc_L1 := proj1 (proj2 Hp);
     lc_L2 := proj1 (proj2 (proj2 Hp)); lc_L3 := proj2 (proj2 (proj2 Hp)) |}.

Definition defect_dec (g : Lineage)
  : {lineage_defect g = None} + {exists d, lineage_defect g = Some d}.
Proof.
  destruct (lineage_defect g) as [d|].
  - right. exists d. reflexivity.
  - left. reflexivity.
Defined.

Definition issue_gaps (g : Lineage) (c : CoverageRecord) (Hp : LineagePasses g)
  : forall gs : list nat, cov_gaps c = gs -> option LineageCertificate :=
  fun gs =>
    match gs as gs' return cov_gaps c = gs' -> option LineageCertificate with
    | [] => fun Hg => Some (build_certificate g c Hp Hg)
    | _ :: _ => fun _ => None
    end.

Lemma issue_gaps_some g c Hp gs (E : cov_gaps c = gs) :
  (exists cert, issue_gaps g c Hp gs E = Some cert) <-> gs = [].
Proof.
  destruct gs as [|x l]; cbn; split; intro H.
  - reflexivity.
  - eexists. reflexivity.
  - destruct H as [cert H]. discriminate H.
  - discriminate H.
Qed.

Lemma issue_gaps_data g c Hp gs (E : cov_gaps c = gs) cert :
  issue_gaps g c Hp gs E = Some cert -> lc_graph cert = g /\ lc_coverage cert = c.
Proof.
  destruct gs as [|x l]; cbn; intro H; [|discriminate H].
  injection H as <-. split; reflexivity.
Qed.

Definition issue_certificate (g : Lineage) (c : CoverageRecord)
  : option LineageCertificate :=
  match defect_dec g with
  | left Hd => issue_gaps g c (proj1 (lineage_defect_none_iff g) Hd) (cov_gaps c) eq_refl
  | right _ => None
  end.

Theorem issue_certificate_iff g c :
  (exists cert, issue_certificate g c = Some cert) <-> lineage_check g c = LineageAccepted.
Proof.
  unfold issue_certificate. rewrite lineage_check_reflect. split.
  - intros [cert H]. destruct (defect_dec g) as [Hd|[d Hd]]; [|discriminate].
    split; [apply lineage_defect_none_iff; exact Hd|].
    apply (issue_gaps_some g c (proj1 (lineage_defect_none_iff g) Hd) (cov_gaps c) eq_refl).
    exists cert. exact H.
  - intros [Hp Hg]. destruct (defect_dec g) as [Hd|[d Hd]].
    + apply (issue_gaps_some g c (proj1 (lineage_defect_none_iff g) Hd) (cov_gaps c) eq_refl). exact Hg.
    + exfalso. apply lineage_defect_none_iff in Hp. rewrite Hp in Hd. discriminate.
Qed.

Theorem issue_certificate_data g c cert :
  issue_certificate g c = Some cert -> lc_graph cert = g /\ lc_coverage cert = c.
Proof.
  unfold issue_certificate. destruct (defect_dec g) as [Hd|[d Hd]]; [|discriminate].
  exact (issue_gaps_data g c (proj1 (lineage_defect_none_iff g) Hd) (cov_gaps c) eq_refl cert).
Qed.
