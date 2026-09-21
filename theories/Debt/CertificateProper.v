(** * Two levels of contextual preservation.

    [CrossingProper]: a context that maps CROSSING witnesses (the first-erased
    structure, no certificates) and acts on the list of seam elements crossed.
    [CertificateProper]: a context that maps full CERTIFIED witnesses ([RPath]) and
    whose witness map COMMUTES WITH THE FIRST ERASURE up to that action.

        CertificateProper F  =>  CrossingProper F  =>  ordinary Proper (erased)

    A crossing-level map cannot in general be lifted to certificates: certificates
    (exhibition, lineage, coverage, maintenance, authority) must be transported
    too.  [ProblemMorphism] packages exactly the extra structure required, an
    EVIDENCE LIFT, and yields a [CertificateProper] instance.

    Why the action on seam lists?  Coq has no definitional proof irrelevance, so
    equating two crossing witnesses that differ only in proofs of the grounding
    equations is not available.  Comparing the seam elements crossed ([ocross]) is
    the proof-independent content of a crossing witness. *)

From Coq Require Import List.
Import ListNotations.
From GTC.Core Require Import GroundedTransport Erasure.
From GTC.Contexts Require Import GroundedProper ContextualPreservation.
From GTC.Instances Require Import OriginalGroundedSeamInstance OriginalDynamicSeamInstance.
From GTC.Debt Require Import Certificates EvidenceObligations GroundedWitness.
From Exactness Require Import GroundedSeam.

(** ** Seam elements crossed by a crossing witness *)

Fixpoint ocross {A B} {S : Span A B} {PA PB Ps} {x y}
    (p : OPath S PA PB Ps x y) : list (seam S) :=
  match p with
  | op_refl _ _ _ _ _ => []
  | op_step _ _ _ _ r _ _ => [r]
  | op_trans _ _ _ _ _ _ _ p q => ocross p ++ ocross q
  end.

Lemma ocross_forget (c : EvCandidate) {x y} (w : RPath c x y) :
  ocross (rpath_forget c w) = map (fun e => projT1 e) (crossings c w).
Proof.
  induction w as [x|r ct|x y z w1 IH1 w2 IH2]; cbn; [reflexivity | reflexivity |].
  rewrite map_app, IH1, IH2. reflexivity.
Qed.

(** ** Level 1: crossing-proper contexts *)

Record CrossingProper {A B A' B'} (S : Span A B) PA PB Ps
    (S' : Span A' B') PA' PB' Ps' (F : @ost A B -> @ost A' B') : Type := {
  cr_gp : GroundedProper (orig_structure S PA PB Ps) (orig_structure S' PA' PB' Ps') F;
  cr_act : list (seam S) -> list (seam S');
  cr_act_spec : forall x y (p : OPath S PA PB Ps x y),
    ocross (gp_map cr_gp p) = cr_act (ocross p)
}.

Arguments cr_gp {A B A' B' S PA PB Ps S' PA' PB' Ps' F} _.
Arguments cr_act {A B A' B' S PA PB Ps S' PA' PB' Ps' F} _ _.
Arguments cr_act_spec {A B A' B' S PA PB Ps S' PA' PB' Ps' F} _ {x y} _.

Definition crossing_proper_id {A B} (S : Span A B) PA PB Ps
  : CrossingProper S PA PB Ps S PA PB Ps (fun x => x).
Proof.
  refine {| cr_gp := gp_id _; cr_act := fun l => l |}.
  intros x y p. reflexivity.
Defined.

Definition crossing_proper_comp {A B A' B' A'' B''}
    {S : Span A B} {PA PB Ps} {S' : Span A' B'} {PA' PB' Ps'}
    {S'' : Span A'' B''} {PA'' PB'' Ps''} {F G}
    (P : CrossingProper S PA PB Ps S' PA' PB' Ps' F)
    (Q : CrossingProper S' PA' PB' Ps' S'' PA'' PB'' Ps'' G)
  : CrossingProper S PA PB Ps S'' PA'' PB'' Ps'' (fun x => G (F x)).
Proof.
  refine {| cr_gp := gp_comp (cr_gp P) (cr_gp Q);
            cr_act := fun l => cr_act Q (cr_act P l) |}.
  intros x y p. cbn. rewrite (cr_act_spec Q). rewrite (cr_act_spec P). reflexivity.
Defined.

(** Crossing-proper contexts are ordinary proper contexts after erasure. *)
Theorem crossing_proper_erased {A B A' B'} {S : Span A B} {PA PB Ps}
    {S' : Span A' B'} {PA' PB' Ps'} {F}
    (P : CrossingProper S PA PB Ps S' PA' PB' Ps' F) x y :
  erased (orig_structure S PA PB Ps) x y ->
  erased (orig_structure S' PA' PB' Ps') (F x) (F y).
Proof. exact (grounded_proper_erased (cr_gp P) x y). Qed.

(** ** Seam evolutions are crossing-proper (given preservation on the image) *)

Section EvolutionCrossing.
  Context {X : TemporalSystem} (V : ValuedSystem X).

  Lemma path_cast_ocross {t} {x x' y y' : @ost (A X t) (B X t)}
      (ex : x = x') (ey : y = y')
      (p : OPath (sp X t) (vA V t) (vB V t) (vS V t) x y) :
    ocross (path_cast V ex ey p) = ocross p.
  Proof. destruct ex, ey. reflexivity. Qed.

  Definition evolution_crossing_proper {t u} (e : SeamEvolution X t u)
      (M : PreservesGroundingOnImage V e)
    : CrossingProper (sp X t) (vA V t) (vB V t) (vS V t)
                     (sp X u) (vA V u) (vB V u) (vS V u) (evo_state e).
  Proof.
    refine {| cr_gp := original_grounding_preserving_evolution_is_grounded_proper V e M;
              cr_act := map (ev_seam e) |}.
    intros x y p. cbn. induction p as [x|r ha hb|x y z p1 IH1 p2 IH2]; cbn.
    - reflexivity.
    - destruct (M r (conj ha hb)) as [ha' hb'].
      unfold evo_map. cbn. rewrite path_cast_ocross. reflexivity.
    - rewrite map_app, <- IH1, <- IH2. reflexivity.
  Defined.
End EvolutionCrossing.

(** ** Level 2: certificate-proper contexts *)

Record CertificateProper {c c' : EvCandidate} (F : rstate c -> rstate c') : Type := {
  cp_cross : CrossingProper (ecSpan c) (ecPA c) (ecPB c) (ecPs c)
                            (ecSpan c') (ecPA c') (ecPB c') (ecPs c') F;
  cp_map : forall x y, RPath c x y -> RPath c' (F x) (F y);
  cp_refl : forall x, cp_map x x (rp_refl x) = rp_refl (F x);
  cp_comp : forall x y z (v : RPath c x y) (w : RPath c y z),
    cp_map x z (rp_trans v w) = rp_trans (cp_map x y v) (cp_map y z w);
  cp_commute : forall x y (w : RPath c x y),
    ocross (rpath_forget c' (cp_map x y w))
    = cr_act cp_cross (ocross (rpath_forget c w))
}.

Arguments cp_cross {c c' F} _.
Arguments cp_map {c c' F} _ {x y} _.
Arguments cp_refl {c c' F} _ x.
Arguments cp_comp {c c' F} _ {x y z} _ _.
Arguments cp_commute {c c' F} _ {x y} _.

(** CertificateProper => CrossingProper. *)
Definition certificate_proper_crossing {c c'} {F : rstate c -> rstate c'}
    (P : CertificateProper F) := cp_cross P.

Definition certificate_proper_id (c : EvCandidate) : CertificateProper (fun x : rstate c => x).
Proof.
  refine {| cp_cross := crossing_proper_id _ _ _ _; cp_map := fun x y w => w |};
    reflexivity.
Defined.

Definition certificate_proper_comp {c c' c'' : EvCandidate}
    {F : rstate c -> rstate c'} {G : rstate c' -> rstate c''}
    (P : CertificateProper F) (Q : CertificateProper G)
  : CertificateProper (fun x => G (F x)).
Proof.
  refine {| cp_cross := crossing_proper_comp (cp_cross P) (cp_cross Q);
            cp_map := fun x y w => cp_map Q (cp_map P w) |}.
  - intro x. cbn. rewrite (cp_refl P x). apply (cp_refl Q).
  - intros x y z v w. cbn. rewrite (cp_comp P v w). apply (cp_comp Q).
  - intros x y w. cbn. rewrite (cp_commute Q). rewrite (cp_commute P). reflexivity.
Defined.

(** Both levels give ordinary proper contexts after erasure. *)
Theorem certificate_proper_erased {c c'} {F : rstate c -> rstate c'}
    (P : CertificateProper F) x y :
  erased (rich_structure c) x y -> erased (rich_structure c') (F x) (F y).
Proof. intros [w]. exact (erase (rich_structure c') (cp_map P w)). Qed.

Corollary certificate_proper_sound {c c'} {F : rstate c -> rstate c'}
    (P : CertificateProper F) x y :
  RPath c x y -> rval c' (F x) = rval c' (F y).
Proof. intro w. exact (rpath_sound c' _ _ (cp_map P w)). Qed.

(** The chain of implications, packaged. *)
Corollary contextual_chain {c c'} {F : rstate c -> rstate c'} (P : CertificateProper F) x y :
  (erased (rich_structure c) x y -> erased (rich_structure c') (F x) (F y)) /\
  (erased (orig_structure (ecSpan c) (ecPA c) (ecPB c) (ecPs c)) x y ->
   erased (orig_structure (ecSpan c') (ecPA c') (ecPB c') (ecPs c')) (F x) (F y)).
Proof.
  split; [exact (certificate_proper_erased P x y) | exact (crossing_proper_erased (cp_cross P) x y)].
Qed.

(** ** Evidence lifting: problem morphisms *)

Definition rcast {c} {x x' y y' : rstate c} (ex : x = x') (ey : y = y')
    (w : RPath c x y) : RPath c x' y' :=
  eq_rect y (fun y0 => RPath c x' y0) (eq_rect x (fun x0 => RPath c x0 y) w x' ex) y' ey.

Definition ocast {A B} {S : Span A B} {PA PB Ps} {x x' y y' : @ost A B}
    (ex : x = x') (ey : y = y') (p : OPath S PA PB Ps x y) : OPath S PA PB Ps x' y' :=
  eq_rect y (fun y0 => OPath S PA PB Ps x' y0) (eq_rect x (fun x0 => OPath S PA PB Ps x0 y) p x' ex) y' ey.

Lemma ocross_ocast {A B} {S : Span A B} {PA PB Ps} {x x' y y' : @ost A B}
    (ex : x = x') (ey : y = y') (p : OPath S PA PB Ps x y) :
  ocross (ocast ex ey p) = ocross p.
Proof. destruct ex, ey. reflexivity. Qed.

Lemma ocross_rcast {c} {x x' y y' : rstate c} (ex : x = x') (ey : y = y') (w : RPath c x y) :
  ocross (rpath_forget c (rcast ex ey w)) = ocross (rpath_forget c w).
Proof. destruct ex, ey. reflexivity. Qed.

(** A problem morphism: maps of seam and coordinates commuting with the
    projections, preservation of the grounding equations on the image, and an
    EVIDENCE LIFT of certified transports. *)
Record ProblemMorphism (c c' : EvCandidate) : Type := {
  pm_seam : seam (ecSpan c) -> seam (ecSpan c');
  pm_A : ecA c -> ecA c';
  pm_B : ecB c -> ecB c';
  pm_back : forall r, back (ecSpan c') (pm_seam r) = pm_A (back (ecSpan c) r);
  pm_fwd : forall r, fwd (ecSpan c') (pm_seam r) = pm_B (fwd (ecSpan c) r);
  pm_grounding : forall r,
    ecPA c (back (ecSpan c) r) = ecPs c r -> ecPB c (fwd (ecSpan c) r) = ecPs c r ->
    ecPA c' (back (ecSpan c') (pm_seam r)) = ecPs c' (pm_seam r) /\
    ecPB c' (fwd (ecSpan c') (pm_seam r)) = ecPs c' (pm_seam r);
  pm_lift : CertifiedTransport c -> CertifiedTransport c'
}.

Arguments pm_seam {c c'} _ _.
Arguments pm_A {c c'} _ _.
Arguments pm_B {c c'} _ _.
Arguments pm_back {c c'} _ _.
Arguments pm_fwd {c c'} _ _.
Arguments pm_grounding {c c'} _ _ _ _.
Arguments pm_lift {c c'} _ _.

Section Morphism.
  Context {c c' : EvCandidate} (pm : ProblemMorphism c c').

  Definition pm_state : rstate c -> rstate c' :=
    fun x => match x with inl a => inl (pm_A pm a) | inr b => inr (pm_B pm b) end.

  Definition pm_cross_map
    : forall x y, OPath (ecSpan c) (ecPA c) (ecPB c) (ecPs c) x y ->
                  OPath (ecSpan c') (ecPA c') (ecPB c') (ecPs c') (pm_state x) (pm_state y).
  Proof.
    intros x y p. induction p as [x|r ha hb|x y z p1 IH1 p2 IH2].
    - exact (op_refl _ _ _ _ _).
    - destruct (pm_grounding pm r ha hb) as [ha' hb'].
      exact (ocast (f_equal inl (pm_back pm r)) (f_equal inr (pm_fwd pm r))
                   (op_step _ _ _ _ (pm_seam pm r) ha' hb')).
    - exact (op_trans _ _ _ _ _ _ _ IH1 IH2).
  Defined.

  Definition pm_cert_map
    : forall x y, RPath c x y -> RPath c' (pm_state x) (pm_state y).
  Proof.
    intros x y w. induction w as [x|r ct|x y z w1 IH1 w2 IH2].
    - exact (rp_refl _).
    - exact (rcast (f_equal inl (pm_back pm r)) (f_equal inr (pm_fwd pm r))
                   (rp_step (pm_seam pm r) (pm_lift pm ct))).
    - exact (rp_trans IH1 IH2).
  Defined.

  Definition pm_crossing_proper
    : CrossingProper (ecSpan c) (ecPA c) (ecPB c) (ecPs c)
                     (ecSpan c') (ecPA c') (ecPB c') (ecPs c') pm_state.
  Proof.
    refine {| cr_gp := @Build_GroundedProper _ _ _ _
                (orig_structure (ecSpan c) (ecPA c) (ecPB c) (ecPs c))
                (orig_structure (ecSpan c') (ecPA c') (ecPB c') (ecPs c')) pm_state
                pm_cross_map _ _;
              cr_act := map (pm_seam pm); cr_act_spec := _ |}.
    intros x y p. cbn. induction p as [x|r ha hb|x y z p1 IH1 p2 IH2]; cbn.
      + reflexivity.
      + destruct (pm_grounding pm r ha hb) as [ha' hb'].
        unfold pm_cross_map. cbn. rewrite ocross_ocast. reflexivity.
      + rewrite map_app, <- IH1, <- IH2. reflexivity.
    Unshelve.
    all: intros; reflexivity.
  Defined.

  (** The certificate map commutes with the first erasure, up to the action. *)
  Lemma pm_commute : forall x y (w : RPath c x y),
    ocross (rpath_forget c' (pm_cert_map x y w))
    = map (pm_seam pm) (ocross (rpath_forget c w)).
  Proof.
    intros x y w. induction w as [x|r ct|x y z w1 IH1 w2 IH2].
    - reflexivity.
    - unfold pm_cert_map. cbn. rewrite ocross_rcast. reflexivity.
    - cbn. rewrite map_app, <- IH1, <- IH2. reflexivity.
  Qed.

  (** With an evidence lift, a seam morphism is certificate-proper. *)
  Definition pm_certificate_proper : CertificateProper pm_state :=
    {| cp_cross := pm_crossing_proper; cp_map := pm_cert_map;
       cp_refl := fun x => eq_refl;
       cp_comp := fun x y z v w => eq_refl;
       cp_commute := fun x y w => pm_commute x y w |}.

  (** The lift carries certified grounding: whatever holds of every certified
      transport of [c'] holds of the image of any certified transport of [c]. *)
  Lemma lift_gives_grounding (ct : CertifiedTransport c) :
    GroundingEquations (ecSpan c') (ecPA c') (ecPB c') (ecPs c').
  Proof. exact (cc_grounding (ct_construction (pm_lift pm ct))). Qed.
End Morphism.
