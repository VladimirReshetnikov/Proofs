(**
  Raw-model reflection for the transparent canonical Minsky trace.

  This module proves the first machine-specific soundness layer needed by
  bounded consistency.  Satisfaction of the concrete finite transition
  formula is exactly one step of an explicit Minsky relation over the carrier
  of an arbitrary [RawPAModel].  No standardness assumption and no rejection
  of accepting traces is used.

  The relation is deliberately phrased over raw model operations.  In the
  decrement branch, for example, the positive case is the equation
  [old = succ new] appearing in the formula, rather than an external test on
  a Coq natural.  This distinction is essential for nonstandard models.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedCheckerRawReduction CanonicalCheckerTrace
  CanonicalCheckerRawReduction.

Import ListNotations.

Module PABoundedCanonicalCheckerRawTraceReflection.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PAFiniteBetaCoding.
Import PABoundedCodedCheckerRawReduction.
Import PABoundedCanonicalCheckerTrace.
Import PABoundedCanonicalCheckerRawReduction.

(** A state of the nine-counter machine, interpreted in a raw arithmetic
    carrier.  Registers outside the finite machine range are harmless; all
    relations below quantify only over [seq 0 canonicalCheckerCounterCount]. *)
Record RawCanonicalMachineState (M : RawPAModel) : Type := {
  rawCanonicalPC : M;
  rawCanonicalRegister : nat -> M
}.

Arguments rawCanonicalPC {M} _.
Arguments rawCanonicalRegister {M} _ _.

Definition rawLocalCurrentState (M : RawPAModel) (e : nat -> M) :
    RawCanonicalMachineState M :=
  {| rawCanonicalPC := raw_term_eval M e localPC;
     rawCanonicalRegister := fun r =>
       raw_term_eval M e (localRegister r) |}.

Arguments rawLocalCurrentState M e : clear implicits.

Definition rawLocalNextState (M : RawPAModel) (e : nat -> M) :
    RawCanonicalMachineState M :=
  {| rawCanonicalPC := raw_term_eval M e localNextPC;
     rawCanonicalRegister := fun r =>
       raw_term_eval M e (localNextRegister r) |}.

Arguments rawLocalNextState M e : clear implicits.

(** Pointwise preservation of every machine register except the one changed
    by an instruction. *)
Definition RawRegistersEqualExcept (M : RawPAModel) (except : option nat)
    (current next : RawCanonicalMachineState M) : Prop :=
  forall r, In r (seq 0 canonicalCheckerCounterCount) ->
    match except with
    | Some x =>
        if Nat.eq_dec r x then True
        else rawCanonicalRegister next r = rawCanonicalRegister current r
    | None =>
        rawCanonicalRegister next r = rawCanonicalRegister current r
    end.

Arguments RawRegistersEqualExcept M except current next : clear implicits.

Definition RawCanonicalIncStep (M : RawPAModel) (x : nat)
    (current next : RawCanonicalMachineState M) : Prop :=
  rawCanonicalPC next = raw_succ M (rawCanonicalPC current) /\
  rawCanonicalRegister next x =
    raw_succ M (rawCanonicalRegister current x) /\
  RawRegistersEqualExcept M (Some x) current next.

Arguments RawCanonicalIncStep M x current next : clear implicits.

Definition RawCanonicalDecStep (M : RawPAModel) (x jump : nat)
    (current next : RawCanonicalMachineState M) : Prop :=
  (rawCanonicalRegister current x = raw_zero M /\
   rawCanonicalPC next = raw_succ M (rawCanonicalPC current) /\
   RawRegistersEqualExcept M None current next) \/
  (rawCanonicalRegister current x =
      raw_succ M (rawCanonicalRegister next x) /\
   rawCanonicalPC next = rawStandardNumeral M jump /\
   RawRegistersEqualExcept M (Some x) current next).

Arguments RawCanonicalDecStep M x jump current next : clear implicits.

Definition RawCanonicalInstructionStep (M : RawPAModel)
    (current next : RawCanonicalMachineState M)
    (entry : nat * MM.mm_instr (Fin.t canonicalCheckerCounterCount)) : Prop :=
  let '(offset, instruction) := entry in
  rawCanonicalPC current = rawStandardNumeral M (S offset) /\
  match instruction with
  | MM.mm_inc x =>
      RawCanonicalIncStep M (finIndexNat x) current next
  | MM.mm_dec x jump =>
      RawCanonicalDecStep M (finIndexNat x) jump current next
  end.

Arguments RawCanonicalInstructionStep M current next entry : clear implicits.

Definition RawCanonicalProgramStep (M : RawPAModel)
    (current next : RawCanonicalMachineState M) : Prop :=
  exists entry,
    In entry
      (combine (seq 0 (length canonicalCheckerMMAProgram))
        canonicalCheckerMMAProgram) /\
    RawCanonicalInstructionStep M current next entry.

Arguments RawCanonicalProgramStep M current next : clear implicits.

Lemma raw_registersEqualExcept_iff : forall (M : RawPAModel)
    (e : nat -> M) except,
  raw_formula_sat M e (traceConjunction (registersEqualExcept except)) <->
  RawRegistersEqualExcept M except
    (rawLocalCurrentState M e) (rawLocalNextState M e).
Proof.
  intros M e except.
  rewrite raw_traceConjunction.
  unfold RawRegistersEqualExcept, registersEqualExcept.
  split.
  - intros hall r hr.
    destruct except as [x|].
    + destruct (Nat.eq_dec r x) as [heq|hne].
      * exact I.
      * specialize (hall
          (pEq (localNextRegister r) (localRegister r))).
        assert (hin : In
            (pEq (localNextRegister r) (localRegister r))
            (map (fun r0 =>
              if Nat.eq_dec r0 x then pEq tZero tZero
              else pEq (localNextRegister r0) (localRegister r0))
              (seq 0 canonicalCheckerCounterCount))).
        {
          apply in_map_iff. exists r. split.
          - destruct (Nat.eq_dec r x); [contradiction | reflexivity].
          - exact hr.
        }
        specialize (hall hin).
        exact hall.
    + specialize (hall
        (pEq (localNextRegister r) (localRegister r))).
      apply hall.
      apply in_map_iff. exists r. split; [reflexivity | exact hr].
  - intros hequal f hf.
    apply in_map_iff in hf.
    destruct hf as [r [<- hr]].
    destruct except as [x|].
    + destruct (Nat.eq_dec r x) as [heq|hne].
      * reflexivity.
      * specialize (hequal r hr).
        destruct (Nat.eq_dec r x) as [heq'|hne']; [contradiction |].
        change (raw_term_eval M e (localNextRegister r) =
          raw_term_eval M e (localRegister r)).
        exact hequal.
    + specialize (hequal r hr).
      change (raw_term_eval M e (localNextRegister r) =
        raw_term_eval M e (localRegister r)).
      exact hequal.
Qed.

Lemma raw_incTransition_iff : forall (M : RawPAModel)
    (e : nat -> M) x,
  raw_formula_sat M e (incTransition x) <->
  RawCanonicalIncStep M x
    (rawLocalCurrentState M e) (rawLocalNextState M e).
Proof.
  intros M e x.
  unfold incTransition, RawCanonicalIncStep.
  change
    ((raw_term_eval M e localNextPC =
        raw_succ M (raw_term_eval M e localPC)) /\
     (raw_term_eval M e (localNextRegister x) =
        raw_succ M (raw_term_eval M e (localRegister x))) /\
     raw_formula_sat M e
       (traceConjunction (registersEqualExcept (Some x))) <->
     (raw_term_eval M e localNextPC =
        raw_succ M (raw_term_eval M e localPC)) /\
     (raw_term_eval M e (localNextRegister x) =
        raw_succ M (raw_term_eval M e (localRegister x))) /\
     RawRegistersEqualExcept M (Some x)
       (rawLocalCurrentState M e) (rawLocalNextState M e)).
  rewrite raw_registersEqualExcept_iff.
  reflexivity.
Qed.

Lemma raw_decTransition_iff : forall (M : RawPAModel)
    (e : nat -> M) x jump,
  raw_formula_sat M e (decTransition x jump) <->
  RawCanonicalDecStep M x jump
    (rawLocalCurrentState M e) (rawLocalNextState M e).
Proof.
  intros M e x jump.
  unfold decTransition, RawCanonicalDecStep.
  change
    (((raw_term_eval M e (localRegister x) = raw_zero M) /\
      (raw_term_eval M e localNextPC =
        raw_succ M (raw_term_eval M e localPC)) /\
      raw_formula_sat M e
        (traceConjunction (registersEqualExcept None))) \/
     ((raw_term_eval M e (localRegister x) =
        raw_succ M (raw_term_eval M e (localNextRegister x))) /\
      (raw_term_eval M e localNextPC =
        raw_term_eval M e (Term.numeral jump)) /\
      raw_formula_sat M e
        (traceConjunction (registersEqualExcept (Some x)))) <->
     ((raw_term_eval M e (localRegister x) = raw_zero M) /\
      (raw_term_eval M e localNextPC =
        raw_succ M (raw_term_eval M e localPC)) /\
      RawRegistersEqualExcept M None
        (rawLocalCurrentState M e) (rawLocalNextState M e)) \/
     ((raw_term_eval M e (localRegister x) =
        raw_succ M (raw_term_eval M e (localNextRegister x))) /\
      (raw_term_eval M e localNextPC = rawStandardNumeral M jump) /\
      RawRegistersEqualExcept M (Some x)
        (rawLocalCurrentState M e) (rawLocalNextState M e))).
  rewrite raw_term_eval_standard_numeral.
  rewrite raw_registersEqualExcept_iff.
  rewrite raw_registersEqualExcept_iff.
  reflexivity.
Qed.

Lemma raw_instructionTransition_iff : forall (M : RawPAModel)
    (e : nat -> M) entry,
  raw_formula_sat M e (instructionTransition entry) <->
  RawCanonicalInstructionStep M
    (rawLocalCurrentState M e) (rawLocalNextState M e) entry.
Proof.
  intros M e [offset instruction].
  destruct instruction as [x | x jump]; cbn [instructionTransition
    RawCanonicalInstructionStep raw_formula_sat].
  - rewrite raw_term_eval_standard_numeral.
    rewrite raw_incTransition_iff.
    reflexivity.
  - rewrite raw_term_eval_standard_numeral.
    rewrite raw_decTransition_iff.
    reflexivity.
Qed.

(** Main local reflection theorem.  It applies to every environment over
    every raw arithmetic structure; [RawPASatisfies] is not needed because
    this is purely the semantics of the displayed transition formula. *)
Theorem raw_canonicalMachineTransition_iff : forall (M : RawPAModel)
    (e : nat -> M),
  raw_formula_sat M e canonicalMachineTransition <->
  RawCanonicalProgramStep M
    (rawLocalCurrentState M e) (rawLocalNextState M e).
Proof.
  intros M e.
  unfold canonicalMachineTransition, RawCanonicalProgramStep.
  rewrite raw_traceDisjunction.
  split.
  - intros [f [hf hsat]].
    apply in_map_iff in hf.
    destruct hf as [entry [<- hentry]].
    exists entry. split; [exact hentry |].
    apply (proj1 (@raw_instructionTransition_iff M e entry)).
    exact hsat.
  - intros [entry [hentry hstep]].
    exists (instructionTransition entry). split.
    + apply in_map_iff. exists entry. split; [reflexivity | exact hentry].
    + apply (proj2 (@raw_instructionTransition_iff M e entry)).
      exact hstep.
Qed.

(** ------------------------------------------------------------------
    Reflection of one beta-coded position of the outer accepting trace. *)

Definition rawCanonicalStateComponent (M : RawPAModel)
    (state : RawCanonicalMachineState M) (sequence : nat) : M :=
  match sequence with
  | 0 => rawCanonicalPC state
  | S r => rawCanonicalRegister state r
  end.

Arguments rawCanonicalStateComponent M state sequence : clear implicits.

Definition rawOuterSequenceCode (M : RawPAModel)
    (outerSlots : nat -> M) (sequence : nat) : M :=
  outerSlots (1 + 2 * sequence).

Definition rawOuterSequenceStep (M : RawPAModel)
    (outerSlots : nat -> M) (sequence : nat) : M :=
  outerSlots (2 + 2 * sequence).

Arguments rawOuterSequenceCode M outerSlots sequence : clear implicits.
Arguments rawOuterSequenceStep M outerSlots sequence : clear implicits.

(** A state is present at an internal trace index when every one of its ten
    components (program counter followed by nine registers) is a beta entry
    at that index. *)
Definition RawCanonicalTraceStateAt (M : RawPAModel)
    (outerSlots : nat -> M) (index : M)
    (state : RawCanonicalMachineState M) : Prop :=
  forall sequence,
    In sequence (seq 0 machineSequenceCount) ->
    @RawBetaEntry M
      (rawCanonicalStateComponent M state sequence)
      (rawOuterSequenceCode M outerSlots sequence)
      (rawOuterSequenceStep M outerSlots sequence)
      index.

Arguments RawCanonicalTraceStateAt M outerSlots index state : clear implicits.

Definition rawStepLocalEnv (M : RawPAModel)
    (outerSlots localSlots : nat -> M) (index : M)
    (tail : nat -> M) : nat -> M :=
  traceSlotEnv M localStateSlotCount localSlots
    (scons M index
      (traceSlotEnv M outerTraceSlotCount outerSlots tail)).

Arguments rawStepLocalEnv M outerSlots localSlots index tail : clear implicits.

Lemma raw_stepLocalEnv_time : forall (M : RawPAModel)
    outerSlots localSlots index tail,
  raw_term_eval M
    (rawStepLocalEnv M outerSlots localSlots index tail) localTime = index.
Proof.
  intros M outerSlots localSlots index tail.
  unfold rawStepLocalEnv, localTime.
  cbn [raw_term_eval].
  rewrite traceSlotEnv_of_ge by lia.
  replace (localStateSlotCount - localStateSlotCount) with 0 by lia.
  reflexivity.
Qed.

Lemma raw_stepLocalEnv_sequenceCode : forall (M : RawPAModel)
    outerSlots localSlots index tail sequence,
  sequence < machineSequenceCount ->
  raw_term_eval M
    (rawStepLocalEnv M outerSlots localSlots index tail)
    (localSequenceCode sequence) =
  rawOuterSequenceCode M outerSlots sequence.
Proof.
  intros M outerSlots localSlots index tail sequence hsequence.
  unfold rawStepLocalEnv, localSequenceCode, localOuterSlot,
    rawOuterSequenceCode.
  cbn [raw_term_eval].
  rewrite traceSlotEnv_of_ge by lia.
  replace
    (S localStateSlotCount + (1 + 2 * sequence) - localStateSlotCount)
    with (S (1 + 2 * sequence)) by lia.
  cbn [scons].
  rewrite traceSlotEnv_of_lt by
    (unfold outerTraceSlotCount; lia).
  reflexivity.
Qed.

Lemma raw_stepLocalEnv_sequenceStep : forall (M : RawPAModel)
    outerSlots localSlots index tail sequence,
  sequence < machineSequenceCount ->
  raw_term_eval M
    (rawStepLocalEnv M outerSlots localSlots index tail)
    (localSequenceStep sequence) =
  rawOuterSequenceStep M outerSlots sequence.
Proof.
  intros M outerSlots localSlots index tail sequence hsequence.
  unfold rawStepLocalEnv, localSequenceStep, localOuterSlot,
    rawOuterSequenceStep.
  cbn [raw_term_eval].
  rewrite traceSlotEnv_of_ge by lia.
  replace
    (S localStateSlotCount + (2 + 2 * sequence) - localStateSlotCount)
    with (S (2 + 2 * sequence)) by lia.
  cbn [scons].
  rewrite traceSlotEnv_of_lt by
    (unfold outerTraceSlotCount; lia).
  reflexivity.
Qed.

Lemma raw_localCurrent_component : forall (M : RawPAModel)
    (e : nat -> M) sequence,
  raw_term_eval M e (localCurrent sequence) =
  rawCanonicalStateComponent M (rawLocalCurrentState M e) sequence.
Proof.
  intros M e [|r]; reflexivity.
Qed.

Lemma raw_localNext_component : forall (M : RawPAModel)
    (e : nat -> M) sequence,
  raw_term_eval M e (localNext sequence) =
  rawCanonicalStateComponent M (rawLocalNextState M e) sequence.
Proof.
  intros M e [|r]; reflexivity.
Qed.

Lemma local_current_trace_condition_in : forall sequence,
  In sequence (seq 0 machineSequenceCount) ->
  In
    (Formula.betaTermTermAt (localCurrent sequence)
      (localSequenceCode sequence) (localSequenceStep sequence) localTime)
    localTraceConditions.
Proof.
  intros sequence hsequence.
  unfold localTraceConditions.
  apply in_flat_map.
  exists sequence. split; [exact hsequence |].
  simpl. auto.
Qed.

Lemma local_next_trace_condition_in : forall sequence,
  In sequence (seq 0 machineSequenceCount) ->
  In
    (Formula.betaTermTermAt (localNext sequence)
      (localSequenceCode sequence) (localSequenceStep sequence)
      (tSucc localTime))
    localTraceConditions.
Proof.
  intros sequence hsequence.
  unfold localTraceConditions.
  apply in_flat_map.
  exists sequence. split; [exact hsequence |].
  simpl. auto.
Qed.

(** Every internally indexed adjacent pair in a satisfying trace is a beta-
    decoded pair of states related by the concrete raw program semantics.
    This theorem is valid even when [index] and the trace length are
    nonstandard elements of [M]. *)
Theorem raw_everyTraceStepCondition_reflects : forall
    (M : RawPAModel) (outerSlots : nat -> M) (tail : nat -> M),
  raw_formula_sat M
    (traceSlotEnv M outerTraceSlotCount outerSlots tail)
    everyTraceStepCondition ->
  forall index,
    rawLt M index (outerSlots 0) ->
    exists current next : RawCanonicalMachineState M,
      RawCanonicalTraceStateAt M outerSlots index current /\
      RawCanonicalTraceStateAt M outerSlots (raw_succ M index) next /\
      RawCanonicalProgramStep M current next.
Proof.
  intros M outerSlots tail hsteps index hindex.
  set (outerEnv :=
    traceSlotEnv M outerTraceSlotCount outerSlots tail).
  unfold everyTraceStepCondition in hsteps.
  change
    (forall d : M,
      raw_formula_sat M (scons M d outerEnv)
        (Formula.ltTermAt (tVar 0) (traceLiftTerm 1 outerSteps)) ->
      raw_formula_sat M (scons M d outerEnv)
        (traceExistsN localStateSlotCount
          (traceConjunction
            (localTraceConditions ++ [canonicalMachineTransition]))))
    in hsteps.
  assert (hltSat : raw_formula_sat M (scons M index outerEnv)
      (Formula.ltTermAt (tVar 0) (traceLiftTerm 1 outerSteps))).
  {
    apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
    unfold outerEnv, traceLiftTerm, outerSteps.
    cbn [raw_term_eval scons].
    exact hindex.
  }
  specialize (hsteps index hltSat).
  destruct (proj1 (@raw_traceExistsN_iff_slots M
    localStateSlotCount
    (traceConjunction
      (localTraceConditions ++ [canonicalMachineTransition]))
    (scons M index outerEnv)) hsteps) as [localSlots hlocal].
  set (localEnv :=
    rawStepLocalEnv M outerSlots localSlots index tail).
  assert (henv :
      traceSlotEnv M localStateSlotCount localSlots
        (scons M index outerEnv) = localEnv).
  {
    unfold localEnv, rawStepLocalEnv, outerEnv. reflexivity.
  }
  rewrite henv in hlocal.
  pose proof (proj1 (@raw_traceConjunction M localEnv
    (localTraceConditions ++ [canonicalMachineTransition])) hlocal)
    as hall.
  exists (rawLocalCurrentState M localEnv),
    (rawLocalNextState M localEnv).
  repeat split.
  - intros sequence hsequence.
    assert (hseqLt : sequence < machineSequenceCount).
    { apply in_seq in hsequence. lia. }
    assert (hin : In
        (Formula.betaTermTermAt (localCurrent sequence)
          (localSequenceCode sequence) (localSequenceStep sequence) localTime)
        (localTraceConditions ++ [canonicalMachineTransition])).
    {
      apply in_app_iff. left.
      exact (@local_current_trace_condition_in sequence hsequence).
    }
    pose proof (hall
      (Formula.betaTermTermAt (localCurrent sequence)
        (localSequenceCode sequence) (localSequenceStep sequence) localTime)
      hin) as hbeta.
    apply (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)) in hbeta.
    unfold localEnv in hbeta.
    rewrite raw_localCurrent_component in hbeta.
    rewrite raw_stepLocalEnv_sequenceCode in hbeta by exact hseqLt.
    rewrite raw_stepLocalEnv_sequenceStep in hbeta by exact hseqLt.
    rewrite raw_stepLocalEnv_time in hbeta.
    exact hbeta.
  - intros sequence hsequence.
    assert (hseqLt : sequence < machineSequenceCount).
    { apply in_seq in hsequence. lia. }
    assert (hin : In
        (Formula.betaTermTermAt (localNext sequence)
          (localSequenceCode sequence) (localSequenceStep sequence)
          (tSucc localTime))
        (localTraceConditions ++ [canonicalMachineTransition])).
    {
      apply in_app_iff. left.
      exact (@local_next_trace_condition_in sequence hsequence).
    }
    pose proof (hall
      (Formula.betaTermTermAt (localNext sequence)
        (localSequenceCode sequence) (localSequenceStep sequence)
        (tSucc localTime))
      hin) as hbeta.
    apply (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)) in hbeta.
    unfold localEnv in hbeta.
    rewrite raw_localNext_component in hbeta.
    rewrite raw_stepLocalEnv_sequenceCode in hbeta by exact hseqLt.
    rewrite raw_stepLocalEnv_sequenceStep in hbeta by exact hseqLt.
    exact hbeta.
  - apply (proj1 (@raw_canonicalMachineTransition_iff M localEnv)).
    apply hall.
    apply in_app_iff. right. simpl. auto.
Qed.

Definition RawCanonicalStepwiseTrace (M : RawPAModel)
    (outerSlots : nat -> M) : Prop :=
  forall index,
    rawLt M index (outerSlots 0) ->
    exists current next : RawCanonicalMachineState M,
      RawCanonicalTraceStateAt M outerSlots index current /\
      RawCanonicalTraceStateAt M outerSlots (raw_succ M index) next /\
      RawCanonicalProgramStep M current next.

Arguments RawCanonicalStepwiseTrace M outerSlots : clear implicits.

(** A witness for the complete canonical graph therefore contains an
    internally stepwise raw-Minsky trace.  The remaining bounded-consistency
    work is now sharply isolated: prove, by an object-definable invariant and
    PA induction, that the compiled checker's initial state cannot reach its
    accepting output on a restricted contradiction certificate.  One cannot
    iterate this theorem by Coq induction up to [outerSlots 0], since that
    element may be nonstandard and is not a Coq [nat]. *)
Theorem raw_CanonicalRestrictedPAProofFormula_stepwise : forall
    (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e CanonicalRestrictedPAProofFormula ->
  exists outerSlots : nat -> M,
    RawCanonicalStepwiseTrace M outerSlots.
Proof.
  intros M e hcanonical.
  destruct (proj1
    (@raw_CanonicalRestrictedPAProofFormula_certificate M e) hcanonical)
    as [outerSlots hall].
  exists outerSlots.
  unfold RawCanonicalStepwiseTrace.
  intros index hindex.
  apply (@raw_everyTraceStepCondition_reflects M outerSlots e).
  - apply hall.
    apply in_app_iff. right. simpl. auto.
  - exact hindex.
Qed.

End PABoundedCanonicalCheckerRawTraceReflection.
