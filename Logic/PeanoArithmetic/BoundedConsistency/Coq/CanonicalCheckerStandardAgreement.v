(** Standard-natural correctness of the concrete Minsky checker.

    This module is intentionally separate from [CanonicalCheckerTrace].
    The latter defines the transparent arithmetical trace predicate used in
    arbitrary PA models; the theorem here only connects the compiled machine
    to the executable Boolean checker on ordinary Coq naturals. *)

From Stdlib Require Import Arith Lia Vector.
From Undecidability Require Import
  MinskyMachines.MMA
  MinskyMachines.Reductions.L_computable_closed_to_MMA_computable.
From BoundedPAConsistency Require Import
  CodedProof CodedCheckerDecisionComputability CanonicalCheckerTrace.

Module PABoundedCanonicalCheckerStandardAgreement.

Import PABoundedCodedProof.
Import PABoundedCodedCheckerDecisionComputability.
Import PABoundedCanonicalCheckerTrace.

Definition canonicalCheckerInitialState (n p : nat) :
    nat * Vector.t nat canonicalCheckerCounterCount :=
  (1, Vector.append
    (Vector.cons nat 0 2 (canonicalCheckerInputVector n p))
    vec.vec_zero).

Definition canonicalCheckerOutputState (output : nat) :
    nat * Vector.t nat canonicalCheckerCounterCount :=
  (canonicalCheckerMMAEnd,
    Vector.cons nat output (2 + 6) vec.vec_zero).

(** The compiler exits immediately after the last instruction. *)
Lemma canonicalCheckerMMAEnd_out_code :
  subcode.out_code canonicalCheckerMMAEnd
    (1, canonicalCheckerMMAProgram).
Proof.
  unfold subcode.out_code, subcode.code_start, subcode.code_end.
  right.
  change (1 + length canonicalCheckerMMAProgram <=
    canonicalCheckerMMAEnd).
  rewrite canonicalCheckerMMAEnd_eq_length.
  lia.
Qed.

Definition canonicalCheckerAccepts (n p : nat) : Prop :=
  sss.sss_output (@mma_sss canonicalCheckerCounterCount)
    (1, canonicalCheckerMMAProgram)
    (canonicalCheckerInitialState n p)
    (canonicalCheckerOutputState 1).

Lemma canonicalCheckerMMAProgram_computes_named : forall n p,
  sss.sss_compute (@mma_sss canonicalCheckerCounterCount)
    (1, canonicalCheckerMMAProgram)
    (canonicalCheckerInitialState n p)
    (canonicalCheckerOutputState (canonicalRestrictedProofFlag n p)).
Proof.
  intros n p.
  exact (canonicalCheckerMMAProgram_computes n p).
Qed.

(** On ordinary naturals the concrete accepting computation agrees exactly
    with the verified executable checker.  No claim about a nonstandard PA
    model is hidden in this statement. *)
Theorem canonicalCheckerAccepts_iff : forall n p,
  canonicalCheckerAccepts n p <->
  checkRestrictedPAProofCode n p = true.
Proof.
  intros n p. split.
  - intros [haccept haccept_out].
    pose proof (canonicalCheckerMMAProgram_computes_named n p) as hcanonical.
    assert (hfinal : canonicalCheckerOutputState 1 =
        canonicalCheckerOutputState (canonicalRestrictedProofFlag n p)).
    {
      eapply sss.sss_compute_fun.
      - exact (@mma_defs.mma_sss_fun canonicalCheckerCounterCount).
      - exact haccept_out.
      - exact canonicalCheckerMMAEnd_out_code.
      - exact haccept.
      - exact hcanonical.
    }
    pose proof (f_equal
      (fun st : nat * Vector.t nat canonicalCheckerCounterCount =>
        vec.vec_pos (snd st) (Fin.F1 : Fin.t canonicalCheckerCounterCount))
      hfinal) as hhead.
    cbn [canonicalCheckerOutputState canonicalCheckerCounterCount] in hhead.
    unfold canonicalRestrictedProofFlag in hhead.
    destruct (checkRestrictedPAProofCode n p) eqn:hcheck.
    + reflexivity.
    + discriminate.
  - intro hcheck.
    split.
    + pose proof (canonicalCheckerMMAProgram_computes_named n p) as hrun.
      unfold canonicalRestrictedProofFlag in hrun.
      rewrite hcheck in hrun.
      exact hrun.
    + exact canonicalCheckerMMAEnd_out_code.
Qed.

End PABoundedCanonicalCheckerStandardAgreement.
