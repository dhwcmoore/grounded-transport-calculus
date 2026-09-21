(** * The debt classifier.

    Given decidability of the four obligations (institutional decidability
    is a hypothesis about the supplied policy), build a report with

    - soundness: every reported debt is a refuted obligation, hence a failed
      transport;
    - relative completeness: if transport fails, some debt is reported. *)

From GTC.Debt Require Import WarrantDebt.

Definition debt_of {P : Prop} (d : {P} + {~ P}) : option (~ P) :=
  match d with left _ => None | right n => Some n end.

Lemma debt_of_none_iff {P : Prop} (d : {P} + {~ P}) : debt_of d = None <-> P.
Proof.
  destruct d as [h|n]; cbn; split.
  - intros _. exact h.
  - intros _. reflexivity.
  - intro H. discriminate H.
  - intro p. exfalso. exact (n p).
Qed.

Section Classifier.
  Context {P} (O : Obligations P).
  Hypothesis dec_obs   : forall p, {Obs O p} + {~ Obs O p}.
  Hypothesis dec_cons  : forall p, {Cons O p} + {~ Cons O p}.
  Hypothesis dec_maint : forall p, {Maint O p} + {~ Maint O p}.
  Hypothesis dec_inst  : forall p, {Inst O p} + {~ Inst O p}.

  Definition classify (p : P) : DebtReport O p :=
    {| observational_debt := debt_of (dec_obs p);
       construction_debt  := debt_of (dec_cons p);
       maintenance_debt   := debt_of (dec_maint p);
       institutional_debt := debt_of (dec_inst p) |}.

  (** Each debt is absent exactly when its obligation holds. *)
  Lemma obs_debt_none   p : observational_debt (classify p) = None <-> Obs O p.
  Proof. apply debt_of_none_iff. Qed.
  Lemma cons_debt_none  p : construction_debt (classify p) = None <-> Cons O p.
  Proof. apply debt_of_none_iff. Qed.
  Lemma maint_debt_none p : maintenance_debt (classify p) = None <-> Maint O p.
  Proof. apply debt_of_none_iff. Qed.
  Lemma inst_debt_none  p : institutional_debt (classify p) = None <-> Inst O p.
  Proof. apply debt_of_none_iff. Qed.

  (** Soundness, per debt: a reported debt carries a refutation of the
      obligation it names, hence refutes transport. *)
  Theorem debt_sound_obs : forall p n,
    observational_debt (classify p) = Some n -> ~ Transport O p.
  Proof. intros p n _ (H & _). exact (n H). Qed.
  Theorem debt_sound_cons : forall p n,
    construction_debt (classify p) = Some n -> ~ Transport O p.
  Proof. intros p n _ (_ & H & _). exact (n H). Qed.
  Theorem debt_sound_maint : forall p n,
    maintenance_debt (classify p) = Some n -> ~ Transport O p.
  Proof. intros p n _ (_ & _ & H & _). exact (n H). Qed.
  Theorem debt_sound_inst : forall p n,
    institutional_debt (classify p) = Some n -> ~ Transport O p.
  Proof. intros p n _ (_ & _ & _ & H). exact (n H). Qed.

  (** Soundness and relative completeness, packaged: the report is clean
      exactly when transport is warranted. *)
  Theorem clean_iff_transport : forall p,
    Clean (classify p) <-> Transport O p.
  Proof.
    intros p. unfold Clean, Transport. split.
    - intros (a & b & c & d). split; [|split; [|split]].
      + apply obs_debt_none, a.
      + apply cons_debt_none, b.
      + apply maint_debt_none, c.
      + apply inst_debt_none, d.
    - intros (a & b & c & d). split; [|split; [|split]].
      + apply obs_debt_none, a.
      + apply cons_debt_none, b.
      + apply maint_debt_none, c.
      + apply inst_debt_none, d.
  Qed.

  Theorem debt_sound : forall p,
    ~ Clean (classify p) -> ~ Transport O p.
  Proof. intros p H T. apply H. apply clean_iff_transport, T. Qed.

  (** Relative completeness: failed transport always yields a report. *)
  Theorem debt_complete : forall p,
    ~ Transport O p -> ~ Clean (classify p).
  Proof. intros p H C. apply H. apply clean_iff_transport, C. Qed.
End Classifier.
