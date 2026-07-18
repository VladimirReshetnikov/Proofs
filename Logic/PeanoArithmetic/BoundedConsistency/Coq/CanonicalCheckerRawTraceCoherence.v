(**
  Coherence and boundary reflection for the canonical raw checker trace.

  The preceding transition-reflection module produces an independently
  existential pair of states at each internal time.  Here beta functionality,
  which genuinely requires [RawPASatisfies], shows that all descriptions of
  one trace position agree on the finite machine state.  We also decode the
  fixed initial checker input and the accepting output/final-PC boundary of a
  complete canonical witness.

  No induction over a model element and no rejection hypothesis occurs in
  this file.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedCheckerRawReduction CanonicalCheckerTrace
  CanonicalCheckerRawReduction CanonicalCheckerRawTraceReflection.

Import ListNotations.

Module PABoundedCanonicalCheckerRawTraceCoherence.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedCheckerRawReduction.
Import PABoundedCanonicalCheckerTrace.
Import PABoundedCanonicalCheckerRawReduction.
Import PABoundedCanonicalCheckerRawTraceReflection.

(** Equality on precisely the program counter and the nine live registers.
    The older state record intentionally permits arbitrary values outside the
    finite register range, so ordinary record equality would be too strong. *)
Definition RawCanonicalStateAgreement (M : RawPAModel)
    (left right : RawCanonicalMachineState M) : Prop :=
  rawCanonicalPC left = rawCanonicalPC right /\
  forall r, In r (seq 0 canonicalCheckerCounterCount) ->
    rawCanonicalRegister left r = rawCanonicalRegister right r.

Arguments RawCanonicalStateAgreement M left right : clear implicits.

Lemma raw_trace_state_functional : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall outerSlots index left right,
  RawCanonicalTraceStateAt M outerSlots index left ->
  RawCanonicalTraceStateAt M outerSlots index right ->
  RawCanonicalStateAgreement M left right.
Proof.
  intros M hPA outerSlots index left right hleft hright.
  split.
  - assert (hzero : In 0 (seq 0 machineSequenceCount)).
    { apply in_seq. unfold machineSequenceCount. lia. }
    specialize (hleft 0 hzero).
    specialize (hright 0 hzero).
    cbn [rawCanonicalStateComponent] in hleft, hright.
    eapply (@rawBetaEntry_functional M hPA); eassumption.
  - intros r hr.
    assert (hsucc : In (S r) (seq 0 machineSequenceCount)).
    {
      apply in_seq in hr. apply in_seq.
      unfold machineSequenceCount. lia.
    }
    specialize (hleft (S r) hsucc).
    specialize (hright (S r) hsucc).
    cbn [rawCanonicalStateComponent] in hleft, hright.
    eapply (@rawBetaEntry_functional M hPA); eassumption.
Qed.

Definition RawCanonicalTraceStepAt (M : RawPAModel)
    (outerSlots : nat -> M) (index : M)
    (current next : RawCanonicalMachineState M) : Prop :=
  RawCanonicalTraceStateAt M outerSlots index current /\
  RawCanonicalTraceStateAt M outerSlots (raw_succ M index) next /\
  RawCanonicalProgramStep M current next.

Arguments RawCanonicalTraceStepAt M outerSlots index current next
  : clear implicits.

(** The endpoint of one reflected step and the start point of a reflected
    successor step agree on the entire live machine state. *)
Theorem raw_trace_steps_chain : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall outerSlots index first middle middle' last,
  RawCanonicalTraceStepAt M outerSlots index first middle ->
  RawCanonicalTraceStepAt M outerSlots (raw_succ M index) middle' last ->
  RawCanonicalStateAgreement M middle middle'.
Proof.
  intros M hPA outerSlots index first middle middle' last
    [_ [hmiddle _]] [hmiddle' _].
  eapply raw_trace_state_functional; eassumption.
Qed.

Definition RawCanonicalCoherentTrace (M : RawPAModel)
    (outerSlots : nat -> M) : Prop :=
  RawCanonicalStepwiseTrace M outerSlots /\
  forall index left right,
    RawCanonicalTraceStateAt M outerSlots index left ->
    RawCanonicalTraceStateAt M outerSlots index right ->
    RawCanonicalStateAgreement M left right.

Arguments RawCanonicalCoherentTrace M outerSlots : clear implicits.

Lemma raw_stepwise_trace_coherent : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall outerSlots,
  RawCanonicalStepwiseTrace M outerSlots ->
  RawCanonicalCoherentTrace M outerSlots.
Proof.
  intros M hPA outerSlots hstepwise. split; [exact hstepwise |].
  intros index left right hleft hright.
  eapply raw_trace_state_functional; eassumption.
Qed.

(** ------------------------------------------------------------------
    Evaluation of the outer beta slots and boundary formulas. *)

Lemma raw_term_eval_traceLiftTerm : forall (M : RawPAModel)
    n slots (e : nat -> M) t,
  raw_term_eval M (traceSlotEnv M n slots e) (traceLiftTerm n t) =
  raw_term_eval M e t.
Proof.
  intros M n slots e t.
  unfold traceLiftTerm.
  rewrite raw_term_eval_rename.
  apply raw_term_eval_ext.
  intro i.
  rewrite traceSlotEnv_of_ge by lia.
  f_equal. lia.
Qed.

Lemma raw_outerEnv_sequenceCode : forall (M : RawPAModel)
    outerSlots tail sequence,
  sequence < machineSequenceCount ->
  raw_term_eval M
    (traceSlotEnv M outerTraceSlotCount outerSlots tail)
    (outerSequenceCode sequence) =
  rawOuterSequenceCode M outerSlots sequence.
Proof.
  intros M outerSlots tail sequence hsequence.
  unfold outerSequenceCode, rawOuterSequenceCode.
  cbn [raw_term_eval].
  rewrite traceSlotEnv_of_lt by
    (unfold outerTraceSlotCount; lia).
  reflexivity.
Qed.

Lemma raw_outerEnv_sequenceStep : forall (M : RawPAModel)
    outerSlots tail sequence,
  sequence < machineSequenceCount ->
  raw_term_eval M
    (traceSlotEnv M outerTraceSlotCount outerSlots tail)
    (outerSequenceStep sequence) =
  rawOuterSequenceStep M outerSlots sequence.
Proof.
  intros M outerSlots tail sequence hsequence.
  unfold outerSequenceStep, rawOuterSequenceStep.
  cbn [raw_term_eval].
  rewrite traceSlotEnv_of_lt by
    (unfold outerTraceSlotCount; lia).
  reflexivity.
Qed.

Lemma raw_outerEnv_steps : forall (M : RawPAModel) outerSlots tail,
  raw_term_eval M
    (traceSlotEnv M outerTraceSlotCount outerSlots tail) outerSteps =
  outerSlots 0.
Proof.
  intros M outerSlots tail.
  unfold outerSteps. cbn [raw_term_eval].
  rewrite traceSlotEnv_of_lt by
    (unfold outerTraceSlotCount; lia).
  reflexivity.
Qed.

Lemma raw_outerEntry_iff : forall (M : RawPAModel)
    outerSlots tail sequence index value,
  sequence < machineSequenceCount ->
  raw_formula_sat M
    (traceSlotEnv M outerTraceSlotCount outerSlots tail)
    (outerEntry sequence index value) <->
  @RawBetaEntry M
    (raw_term_eval M
      (traceSlotEnv M outerTraceSlotCount outerSlots tail) value)
    (rawOuterSequenceCode M outerSlots sequence)
    (rawOuterSequenceStep M outerSlots sequence)
    (raw_term_eval M
      (traceSlotEnv M outerTraceSlotCount outerSlots tail) index).
Proof.
  intros M outerSlots tail sequence index value hsequence.
  unfold outerEntry.
  rewrite raw_sat_betaTermTermAt_iff.
  rewrite raw_outerEnv_sequenceCode by exact hsequence.
  rewrite raw_outerEnv_sequenceStep by exact hsequence.
  reflexivity.
Qed.

Definition rawCanonicalInitialRegister (M : RawPAModel)
    (bound certificate : M) (r : nat) : M :=
  match r with
  | 0 => raw_zero M
  | 1 => bound
  | 2 => certificate
  | _ => raw_zero M
  end.

Definition rawCanonicalInitialState (M : RawPAModel)
    (bound certificate : M) : RawCanonicalMachineState M :=
  {| rawCanonicalPC := rawStandardNumeral M 1;
     rawCanonicalRegister :=
       @rawCanonicalInitialRegister M bound certificate |}.

Arguments rawCanonicalInitialRegister M bound certificate r : clear implicits.
Arguments rawCanonicalInitialState M bound certificate : clear implicits.

Lemma raw_initialRegisterValue : forall (M : RawPAModel)
    outerSlots tail bound certificate r,
  raw_term_eval M
    (traceSlotEnv M outerTraceSlotCount outerSlots tail)
    (initialRegisterValue bound certificate r) =
  rawCanonicalInitialRegister M
    (raw_term_eval M tail bound) (raw_term_eval M tail certificate) r.
Proof.
  intros M outerSlots tail bound certificate [|[|[|r]]];
    cbn [initialRegisterValue rawCanonicalInitialRegister raw_term_eval].
  - reflexivity.
  - apply raw_term_eval_traceLiftTerm.
  - apply raw_term_eval_traceLiftTerm.
  - reflexivity.
Qed.

Lemma raw_initialTraceConditions_reflect : forall (M : RawPAModel)
    outerSlots tail bound certificate,
  (forall f, In f (initialTraceConditions bound certificate) ->
    raw_formula_sat M
      (traceSlotEnv M outerTraceSlotCount outerSlots tail) f) ->
  RawCanonicalTraceStateAt M outerSlots (raw_zero M)
    (rawCanonicalInitialState M
      (raw_term_eval M tail bound) (raw_term_eval M tail certificate)).
Proof.
  intros M outerSlots tail bound certificate hall [|r] hsequence.
  - assert (hpc : raw_formula_sat M
        (traceSlotEnv M outerTraceSlotCount outerSlots tail)
        (outerEntry 0 tZero (Term.numeral 1))).
    {
      apply hall. unfold initialTraceConditions. simpl. auto.
    }
    assert (hseq0 : 0 < machineSequenceCount).
    { unfold machineSequenceCount. lia. }
    apply (proj1 (@raw_outerEntry_iff M outerSlots tail 0
      tZero (Term.numeral 1) hseq0)) in hpc.
    rewrite raw_term_eval_standard_numeral in hpc.
    exact hpc.
  - assert (hr : In r (seq 0 canonicalCheckerCounterCount)).
    {
      apply in_seq in hsequence. apply in_seq.
      unfold machineSequenceCount in hsequence. lia.
    }
    assert (hreg : raw_formula_sat M
        (traceSlotEnv M outerTraceSlotCount outerSlots tail)
        (outerEntry (S r) tZero
          (initialRegisterValue bound certificate r))).
    {
      apply hall. unfold initialTraceConditions. right.
      apply in_map_iff. exists r. split; [reflexivity | exact hr].
    }
    assert (hseqS : S r < machineSequenceCount).
    { unfold machineSequenceCount. apply in_seq in hr. lia. }
    apply (proj1 (@raw_outerEntry_iff M outerSlots tail (S r)
      tZero (initialRegisterValue bound certificate r) hseqS)) in hreg.
    rewrite raw_initialRegisterValue in hreg.
    exact hreg.
Qed.

Definition RawCanonicalAcceptingOutput (M : RawPAModel)
    (outerSlots : nat -> M) : Prop :=
  @RawBetaEntry M (rawStandardNumeral M 1)
    (rawOuterSequenceCode M outerSlots 1)
    (rawOuterSequenceStep M outerSlots 1)
    (outerSlots 0).

Arguments RawCanonicalAcceptingOutput M outerSlots : clear implicits.

Lemma raw_finalOutputOneCondition_iff : forall (M : RawPAModel)
    outerSlots tail,
  raw_formula_sat M
    (traceSlotEnv M outerTraceSlotCount outerSlots tail)
    finalOutputOneCondition <->
  RawCanonicalAcceptingOutput M outerSlots.
Proof.
  intros M outerSlots tail.
  unfold finalOutputOneCondition, RawCanonicalAcceptingOutput.
  rewrite (@raw_outerEntry_iff M outerSlots tail 1
    outerSteps (Term.numeral 1)) by
    (unfold machineSequenceCount, canonicalCheckerCounterCount; lia).
  rewrite raw_outerEnv_steps.
  rewrite raw_term_eval_standard_numeral.
  reflexivity.
Qed.

(** Local raw semantics for the library's non-strict order formula. *)
Lemma raw_sat_leTermAt_iff_coherence : forall (M : RawPAModel)
    (a b : term) (e : nat -> M),
  raw_formula_sat M e (Formula.leTermAt a b) <->
  rawLe M (raw_term_eval M e a) (raw_term_eval M e b).
Proof.
  intros M a b e.
  unfold Formula.leTermAt, rawLe.
  cbn [raw_formula_sat raw_term_eval].
  split.
  - intros [d h]. exists d.
    repeat rewrite raw_term_eval_rename_succ in h.
    cbn [raw_term_eval scons] in h. exact h.
  - intros [d h]. exists d.
    repeat rewrite raw_term_eval_rename_succ.
    cbn [raw_term_eval scons]. exact h.
Qed.

Definition RawCanonicalOutsideProgram (M : RawPAModel) (pc : M) : Prop :=
  rawLt M pc (rawStandardNumeral M 1) \/
  rawLe M (rawStandardNumeral M canonicalCheckerMMAEnd) pc.

Arguments RawCanonicalOutsideProgram M pc : clear implicits.

Lemma raw_outsideCanonicalProgram_iff : forall (M : RawPAModel)
    (e : nat -> M) pc,
  raw_formula_sat M e (outsideCanonicalProgram pc) <->
  RawCanonicalOutsideProgram M (raw_term_eval M e pc).
Proof.
  intros M e pc.
  unfold outsideCanonicalProgram, RawCanonicalOutsideProgram.
  cbn [raw_formula_sat].
  rewrite raw_sat_ltTermAt_iff.
  rewrite raw_sat_leTermAt_iff_coherence.
  rewrite !raw_term_eval_standard_numeral.
  reflexivity.
Qed.

Definition RawCanonicalFinalPCBoundary (M : RawPAModel)
    (outerSlots : nat -> M) : Prop :=
  exists pc : M,
    @RawBetaEntry M pc
      (rawOuterSequenceCode M outerSlots 0)
      (rawOuterSequenceStep M outerSlots 0)
      (outerSlots 0) /\
    RawCanonicalOutsideProgram M pc.

Arguments RawCanonicalFinalPCBoundary M outerSlots : clear implicits.

Lemma raw_term_eval_traceLiftOne : forall (M : RawPAModel)
    x (e : nat -> M) t,
  raw_term_eval M (scons M x e) (traceLiftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M x e t.
  unfold traceLiftTerm.
  rewrite raw_term_eval_rename.
  apply raw_term_eval_ext.
  intro i. replace (i + 1) with (S i) by lia. reflexivity.
Qed.

Lemma raw_finalPCCondition_iff : forall (M : RawPAModel)
    outerSlots tail,
  raw_formula_sat M
    (traceSlotEnv M outerTraceSlotCount outerSlots tail)
    finalPCCondition <->
  RawCanonicalFinalPCBoundary M outerSlots.
Proof.
  intros M outerSlots tail.
  unfold finalPCCondition, RawCanonicalFinalPCBoundary.
  cbn [raw_formula_sat].
  split.
  - intros [pc [hbeta hout]]. exists pc. split.
    + apply (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)) in hbeta.
      repeat rewrite raw_term_eval_traceLiftOne in hbeta.
      rewrite raw_outerEnv_sequenceCode in hbeta by
        (unfold machineSequenceCount; lia).
      rewrite raw_outerEnv_sequenceStep in hbeta by
        (unfold machineSequenceCount; lia).
      rewrite raw_outerEnv_steps in hbeta.
      exact hbeta.
    + apply (proj1 (@raw_outsideCanonicalProgram_iff M _ _)) in hout.
      exact hout.
  - intros [pc [hbeta hout]]. exists pc. split.
    + apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
      repeat rewrite raw_term_eval_traceLiftOne.
      rewrite raw_outerEnv_sequenceCode by
        (unfold machineSequenceCount; lia).
      rewrite raw_outerEnv_sequenceStep by
        (unfold machineSequenceCount; lia).
      rewrite raw_outerEnv_steps.
      exact hbeta.
    + apply (proj2 (@raw_outsideCanonicalProgram_iff M _ _)).
      exact hout.
Qed.

(** ------------------------------------------------------------------
    A genuine state at the final trace index.

    This does not iterate externally up to the (possibly nonstandard) trace
    length.  PA's internal zero-or-successor theorem gives either the zero
    boundary directly or one immediate predecessor, to which the already
    universal step condition may be applied once. *)

Lemma raw_zero_or_successor_coherence : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M,
  x = raw_zero M \/ exists predecessor : M,
    x = raw_succ M predecessor.
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (PA.Formula.BProv_Ax_s_zeroOrSuccPredAt [] 0) e) as hcases.
  change (x = raw_zero M \/ exists predecessor : M,
    x = raw_succ M predecessor) in hcases.
  exact hcases.
Qed.

Lemma raw_lt_self_succ_coherence : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M,
  rawLt M x (raw_succ M x).
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (PA.Formula.BProv_Ax_s_leTermAt_refl [] (PA.tVar 0)) e) as hle.
  change (rawLe M x x) in hle.
  exact (raw_lt_succ_of_le M hPA x x hle).
Qed.

Lemma raw_stepwise_trace_has_final_state : forall (M : RawPAModel),
  RawPASatisfies M -> forall outerSlots initial,
  RawCanonicalStepwiseTrace M outerSlots ->
  RawCanonicalTraceStateAt M outerSlots (raw_zero M) initial ->
  exists final : RawCanonicalMachineState M,
    RawCanonicalTraceStateAt M outerSlots (outerSlots 0) final.
Proof.
  intros M hPA outerSlots initial hsteps hinitial.
  destruct (@raw_zero_or_successor_coherence M hPA (outerSlots 0))
    as [hzero | [predecessor hsuccessor]].
  - exists initial. rewrite hzero. exact hinitial.
  - assert (hlt : rawLt M predecessor (outerSlots 0)).
    {
      rewrite hsuccessor.
      exact (@raw_lt_self_succ_coherence M hPA predecessor).
    }
    destruct (hsteps predecessor hlt) as
      [current [final [_ [hfinal _]]]].
    exists final. rewrite hsuccessor. exact hfinal.
Qed.

(** A full final machine state, not merely two isolated beta entries. *)
Definition RawCanonicalAcceptingFinalState (M : RawPAModel)
    (outerSlots : nat -> M) (final : RawCanonicalMachineState M) : Prop :=
  RawCanonicalTraceStateAt M outerSlots (outerSlots 0) final /\
  RawCanonicalOutsideProgram M (rawCanonicalPC final) /\
  rawCanonicalRegister final 0 = rawStandardNumeral M 1.

Arguments RawCanonicalAcceptingFinalState M outerSlots final
  : clear implicits.

Lemma raw_final_state_accepting : forall (M : RawPAModel),
  RawPASatisfies M -> forall outerSlots final,
  RawCanonicalTraceStateAt M outerSlots (outerSlots 0) final ->
  RawCanonicalAcceptingOutput M outerSlots ->
  RawCanonicalFinalPCBoundary M outerSlots ->
  RawCanonicalAcceptingFinalState M outerSlots final.
Proof.
  intros M hPA outerSlots final hfinal houtput
    [pc [hpc houtside]].
  unfold RawCanonicalAcceptingFinalState.
  repeat split.
  - exact hfinal.
  - assert (hsequence : In 0 (seq 0 machineSequenceCount)).
    { apply in_seq. unfold machineSequenceCount. lia. }
    specialize (hfinal 0 hsequence).
    cbn [rawCanonicalStateComponent] in hfinal.
    assert (heq : rawCanonicalPC final = pc).
    { eapply (@rawBetaEntry_functional M hPA); eassumption. }
    rewrite heq. exact houtside.
  - assert (hsequence : In 1 (seq 0 machineSequenceCount)).
    {
      apply in_seq.
      unfold machineSequenceCount, canonicalCheckerCounterCount. lia.
    }
    specialize (hfinal 1 hsequence).
    cbn [rawCanonicalStateComponent] in hfinal.
    unfold RawCanonicalAcceptingOutput in houtput.
    eapply (@rawBetaEntry_functional M hPA); eassumption.
Qed.

(** Complete boundary/coherence package extracted from one canonical graph
    witness.  [tail 0] and [tail 1] are exactly the fixed bound and candidate
    certificate supplied to the graph formula. *)
Theorem raw_CanonicalRestrictedPAProofFormula_boundary_coherent : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  raw_formula_sat M tail CanonicalRestrictedPAProofFormula ->
  exists outerSlots : nat -> M,
    RawCanonicalCoherentTrace M outerSlots /\
    RawCanonicalTraceStateAt M outerSlots (raw_zero M)
      (rawCanonicalInitialState M (tail 0) (tail 1)) /\
    RawCanonicalAcceptingOutput M outerSlots /\
    RawCanonicalFinalPCBoundary M outerSlots.
Proof.
  intros M hPA tail hcanonical.
  destruct (proj1
    (@raw_CanonicalRestrictedPAProofFormula_certificate M tail) hcanonical)
    as [outerSlots hall].
  exists outerSlots.
  assert (hsteps : RawCanonicalStepwiseTrace M outerSlots).
  {
    intros index hindex.
    apply (@raw_everyTraceStepCondition_reflects M outerSlots tail).
    - apply hall. apply in_app_iff. right. simpl. auto.
    - exact hindex.
  }
  split.
  - apply raw_stepwise_trace_coherent; assumption.
  - split.
    + apply (@raw_initialTraceConditions_reflect M outerSlots tail
        (tVar 0) (tVar 1)).
      intros f hf. apply hall.
      apply in_app_iff. left. exact hf.
    + split.
      * apply (proj1 (@raw_finalOutputOneCondition_iff M outerSlots tail)).
        apply hall. apply in_app_iff. right. simpl. auto.
      * apply (proj1 (@raw_finalPCCondition_iff M outerSlots tail)).
        apply hall. apply in_app_iff. right. simpl. auto.
Qed.

(** The same package with the boundary entries identified as components of
    one genuine final state. *)
Theorem raw_CanonicalRestrictedPAProofFormula_accepting_final_state : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  raw_formula_sat M tail CanonicalRestrictedPAProofFormula ->
  exists (outerSlots : nat -> M) (final : RawCanonicalMachineState M),
    RawCanonicalCoherentTrace M outerSlots /\
    RawCanonicalTraceStateAt M outerSlots (raw_zero M)
      (rawCanonicalInitialState M (tail 0) (tail 1)) /\
    RawCanonicalAcceptingFinalState M outerSlots final.
Proof.
  intros M hPA tail hcanonical.
  destruct (@raw_CanonicalRestrictedPAProofFormula_boundary_coherent
    M hPA tail hcanonical) as
    [outerSlots [hcoherent [hinitial [houtput hfinalPC]]]].
  destruct (@raw_stepwise_trace_has_final_state M hPA outerSlots
    (rawCanonicalInitialState M (tail 0) (tail 1))
    (proj1 hcoherent) hinitial) as [final hfinal].
  exists outerSlots, final.
  split; [exact hcoherent |].
  split; [exact hinitial |].
  exact (@raw_final_state_accepting M hPA outerSlots final
    hfinal houtput hfinalPC).
Qed.

End PABoundedCanonicalCheckerRawTraceCoherence.
