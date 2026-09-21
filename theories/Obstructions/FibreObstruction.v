(** * Fibre factorisation (the admissibility engine).

    [Phi] factors through the observation [M] iff [Phi] is constant on the
    fibres of [M].  The direction that produces obstruction certificates
    needs no axioms, and so does the relational converse.  The unrestricted
    functional converse needs classical choice and lives in
    [ClassicalFactorisation.v], outside the axiom-free kernel.  A finite
    constructive converse is the legacy [fibre_constant_admissible]; see
    [Instances/OriginalAdmissibility.v]. *)

Section Fibres.
  Context {X O V : Type} (M : X -> O) (Phi : X -> V).

  Definition Factors : Prop := exists Phihat : O -> V, forall x, Phi x = Phihat (M x).
  Definition ConstantOnFibres : Prop := forall x y, M x = M y -> Phi x = Phi y.

  (** Axiom-free. *)
  Theorem factors_constant : Factors -> ConstantOnFibres.
  Proof.
    intros [Ph H] x y Hxy. rewrite (H x), (H y), Hxy. reflexivity.
  Qed.

  (** A certificate: two states with equal observation and different value. *)
  Theorem fibre_obstruction :
    forall x y, M x = M y -> Phi x <> Phi y -> ~ Factors.
  Proof.
    intros x y Hm Hn Hf. exact (Hn (factors_constant Hf x y Hm)).
  Qed.

  (** Axiom-free relational factorisation: [Phi] is determined by [M] iff the
      relation "some [x] has observation [o] and value [v]" is functional. *)
  Definition graph (o : O) (v : V) : Prop := exists x, M x = o /\ Phi x = v.

  Theorem constant_relational :
    ConstantOnFibres ->
    (forall x, graph (M x) (Phi x)) /\
    (forall o v v', graph o v -> graph o v' -> v = v').
  Proof.
    intro H. split.
    - intro x. exists x. split; reflexivity.
    - intros o v v' [x [Hx Hv]] [y [Hy Hv']].
      rewrite <- Hv, <- Hv'. apply H. rewrite Hx, Hy. reflexivity.
  Qed.
End Fibres.
