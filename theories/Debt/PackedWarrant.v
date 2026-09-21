(** * Packed warrants: one endpoint-indexed collection, many problems.

    Witnesses for different transport problems inhabit different indexed types
    ([RPath c s t] depends on the candidate [c]).  [PackedWarrant] packages the
    problem with the witness and an interpretation of its states into a common
    endpoint type [X], so warrants for the same endpoints can be compared in ONE
    type without pretending their lineage records (or authorities) coincide.

    Erasure ([erase_packed]) lands in a single proposition [ErasedAt x y] that
    does not record which problem or witness was used. *)

From Coq Require Import List.
Import ListNotations.
From GTC.Core Require Import GroundedTransport Erasure.
From GTC.Debt Require Import Certificates EvidenceObligations GroundedWitness.

Section Packed.
  Context {X : Type} (emb : forall c : EvCandidate, rstate c -> X).

  (** The ordinary judgement: some problem and some erased transport. *)
  Definition ErasedAt (x y : X) : Prop :=
    exists (c : EvCandidate) (s t : rstate c),
      emb c s = x /\ emb c t = y /\ erased (rich_structure c) s t.

  Record PackedWarrant (x y : X) : Type := {
    pw_problem : EvCandidate;
    pw_src : rstate pw_problem;
    pw_tgt : rstate pw_problem;
    pw_src_is : emb pw_problem pw_src = x;
    pw_tgt_is : emb pw_problem pw_tgt = y;
    pw_witness : RPath pw_problem pw_src pw_tgt
  }.

  Definition erase_packed {x y} (w : PackedWarrant x y) : ErasedAt x y :=
    ex_intro _ (pw_problem x y w)
      (ex_intro _ (pw_src x y w)
        (ex_intro _ (pw_tgt x y w)
          (conj (pw_src_is x y w)
            (conj (pw_tgt_is x y w)
              (erase (rich_structure (pw_problem x y w)) (pw_witness x y w)))))).

  (** What survives: the extractable summary of the witness. *)
  Definition warrant_summary {x y} (w : PackedWarrant x y) : list (WitnessSummary) :=
    witness_summary (pw_problem x y w) (pw_witness x y w).

  (** Warrants with different summaries are different warrants, though they
      erase into the same judgement. *)
  Theorem packed_distinguishable {x y} (w1 w2 : PackedWarrant x y) :
    warrant_summary w1 <> warrant_summary w2 -> w1 <> w2.
  Proof. intros H E. apply H. rewrite E. reflexivity. Qed.
End Packed.

Arguments pw_problem {X emb x y} _.
Arguments pw_src {X emb x y} _.
Arguments pw_tgt {X emb x y} _.
Arguments pw_src_is {X emb x y} _.
Arguments pw_tgt_is {X emb x y} _.
Arguments pw_witness {X emb x y} _.
Arguments erase_packed {X emb x y} _.
Arguments warrant_summary {X emb x y} _.
