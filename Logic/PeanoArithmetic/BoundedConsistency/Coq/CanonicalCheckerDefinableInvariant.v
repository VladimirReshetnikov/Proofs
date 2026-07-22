(**
  PA-definable invariants for the canonical checker trace.

  A canonical trace may have nonstandard length in a nonstandard model of
  PA.  Consequently it is unsound to iterate its reflected steps by Rocq
  induction.  This file builds a first-order formula saying that a supplied
  invariant holds of the beta-coded state at a given time, and applies PA's
  own induction axiom through [raw_definable_induction].

  The final theorem factors the remaining checker-specific work into three
  ordinary obligations on one formula: it holds initially, is preserved by
  every concrete Minsky step, and excludes an accepting final state.  No
  assumption about standardness of the trace code or its length occurs.
*)

From Stdlib Require Import List Arith Lia Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedCheckerRawReduction CanonicalCheckerTrace
  CanonicalCheckerRawReduction CanonicalCheckerRawTraceReflection
  CanonicalCheckerRawTraceCoherence.

Import ListNotations.

Module PABoundedCanonicalCheckerDefinableInvariant.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedCheckerRawReduction.
Import PABoundedCanonicalCheckerTrace.
Import PABoundedCanonicalCheckerRawReduction.
Import PABoundedCanonicalCheckerRawTraceReflection.
Import PABoundedCanonicalCheckerRawTraceCoherence.

(** ------------------------------------------------------------------
    The invariant formula and its beta-coded point predicate.

    Inside [canonicalTraceInvariantAt invariant], the first ten variables
    are the program counter and nine registers.  They are followed by the
    current time, then by the outer trace slots, then by the public checker
    input environment.  Thus an invariant may mention not only the current
    state, but also the time, trace parameters, fixed hierarchy bound, and
    candidate certificate when those are useful for a concrete proof. *)

Definition invariantStateComponent (sequence : nat) : PA.term :=
  tVar sequence.

Definition invariantTime : PA.term := tVar machineSequenceCount.

Definition invariantOuterSlot (slot : nat) : PA.term :=
  tVar (S machineSequenceCount + slot).

Definition invariantSequenceCode (sequence : nat) : PA.term :=
  invariantOuterSlot (1 + 2 * sequence).

Definition invariantSequenceStep (sequence : nat) : PA.term :=
  invariantOuterSlot (2 + 2 * sequence).

Definition invariantTraceEntry (sequence : nat) : PA.formula :=
  Formula.betaTermTermAt (invariantStateComponent sequence)
    (invariantSequenceCode sequence) (invariantSequenceStep sequence)
    invariantTime.

Definition canonicalTraceInvariantAt (invariant : PA.formula) : PA.formula :=
  traceExistsN machineSequenceCount
    (traceConjunction
      (map invariantTraceEntry (seq 0 machineSequenceCount) ++ [invariant])).

(** The guarded predicate is true automatically after the end of the trace.
    This shape makes its successor closure provable at *every* model element,
    as required by PA induction, while still yielding the invariant at the
    final trace index. *)
Definition canonicalTraceInvariantThrough
    (invariant : PA.formula) : PA.formula :=
  pImp
    (Formula.leTermAt (tVar 0) (traceLiftTerm 1 outerSteps))
    (canonicalTraceInvariantAt invariant).

Definition rawCanonicalInvariantEnv (M : RawPAModel)
    (outerSlots : nat -> M) (tail : nat -> M) (index : M)
    (state : RawCanonicalMachineState M) : nat -> M :=
  traceSlotEnv M machineSequenceCount
    (fun sequence => rawCanonicalStateComponent M state sequence)
    (scons M index
      (traceSlotEnv M outerTraceSlotCount outerSlots tail)).

Arguments rawCanonicalInvariantEnv M outerSlots tail index state
  : clear implicits.

Definition RawCanonicalInvariantHolds (M : RawPAModel)
    (invariant : PA.formula) (outerSlots : nat -> M) (tail : nat -> M)
    (index : M) (state : RawCanonicalMachineState M) : Prop :=
  raw_formula_sat M
    (rawCanonicalInvariantEnv M outerSlots tail index state) invariant.

Arguments RawCanonicalInvariantHolds M invariant outerSlots tail index state
  : clear implicits.

(** Evaluation of the manually laid-out variables in the invariant body. *)
Lemma raw_invariant_inner_state : forall (M : RawPAModel)
    stateSlots outerSlots tail index sequence,
  sequence < machineSequenceCount ->
  raw_term_eval M
    (traceSlotEnv M machineSequenceCount stateSlots
      (scons M index
        (traceSlotEnv M outerTraceSlotCount outerSlots tail)))
    (invariantStateComponent sequence) = stateSlots sequence.
Proof.
  intros M stateSlots outerSlots tail index sequence hsequence.
  unfold invariantStateComponent. cbn [raw_term_eval].
  apply traceSlotEnv_of_lt. exact hsequence.
Qed.

Lemma raw_invariant_inner_time : forall (M : RawPAModel)
    stateSlots outerSlots tail index,
  raw_term_eval M
    (traceSlotEnv M machineSequenceCount stateSlots
      (scons M index
        (traceSlotEnv M outerTraceSlotCount outerSlots tail)))
    invariantTime = index.
Proof.
  intros M stateSlots outerSlots tail index.
  unfold invariantTime. cbn [raw_term_eval].
  rewrite traceSlotEnv_of_ge by lia.
  replace (machineSequenceCount - machineSequenceCount) with 0 by lia.
  reflexivity.
Qed.

Lemma raw_invariant_inner_sequenceCode : forall (M : RawPAModel)
    stateSlots outerSlots tail index sequence,
  sequence < machineSequenceCount ->
  raw_term_eval M
    (traceSlotEnv M machineSequenceCount stateSlots
      (scons M index
        (traceSlotEnv M outerTraceSlotCount outerSlots tail)))
    (invariantSequenceCode sequence) =
  rawOuterSequenceCode M outerSlots sequence.
Proof.
  intros M stateSlots outerSlots tail index sequence hsequence.
  unfold invariantSequenceCode, invariantOuterSlot, rawOuterSequenceCode.
  cbn [raw_term_eval].
  rewrite traceSlotEnv_of_ge by lia.
  replace (S machineSequenceCount + (1 + 2 * sequence) -
      machineSequenceCount) with (S (1 + 2 * sequence)) by lia.
  cbn [scons].
  rewrite traceSlotEnv_of_lt by
    (unfold outerTraceSlotCount; lia).
  reflexivity.
Qed.

Lemma raw_invariant_inner_sequenceStep : forall (M : RawPAModel)
    stateSlots outerSlots tail index sequence,
  sequence < machineSequenceCount ->
  raw_term_eval M
    (traceSlotEnv M machineSequenceCount stateSlots
      (scons M index
        (traceSlotEnv M outerTraceSlotCount outerSlots tail)))
    (invariantSequenceStep sequence) =
  rawOuterSequenceStep M outerSlots sequence.
Proof.
  intros M stateSlots outerSlots tail index sequence hsequence.
  unfold invariantSequenceStep, invariantOuterSlot, rawOuterSequenceStep.
  cbn [raw_term_eval].
  rewrite traceSlotEnv_of_ge by lia.
  replace (S machineSequenceCount + (2 + 2 * sequence) -
      machineSequenceCount) with (S (2 + 2 * sequence)) by lia.
  cbn [scons].
  rewrite traceSlotEnv_of_lt by
    (unfold outerTraceSlotCount; lia).
  reflexivity.
Qed.

Definition rawInvariantStateOfSlots (M : RawPAModel)
    (stateSlots : nat -> M) : RawCanonicalMachineState M :=
  {| rawCanonicalPC := stateSlots 0;
     rawCanonicalRegister := fun r => stateSlots (S r) |}.

Arguments rawInvariantStateOfSlots M stateSlots : clear implicits.

Lemma rawInvariantStateOfSlots_component : forall (M : RawPAModel)
    stateSlots sequence,
  rawCanonicalStateComponent M
    (rawInvariantStateOfSlots M stateSlots) sequence = stateSlots sequence.
Proof.
  intros M stateSlots [|r]; reflexivity.
Qed.

(** Exact raw semantics of the point predicate.  This lemma is law-free:
    PA is needed only later, to iterate the predicate through nonstandard
    time. *)
Theorem raw_canonicalTraceInvariantAt_iff : forall (M : RawPAModel)
    invariant outerSlots tail index,
  raw_formula_sat M
    (scons M index
      (traceSlotEnv M outerTraceSlotCount outerSlots tail))
    (canonicalTraceInvariantAt invariant) <->
  exists state : RawCanonicalMachineState M,
    RawCanonicalTraceStateAt M outerSlots index state /\
    RawCanonicalInvariantHolds M invariant outerSlots tail index state.
Proof.
  intros M invariant outerSlots tail index.
  unfold canonicalTraceInvariantAt.
  rewrite raw_traceExistsN_iff_slots.
  split.
  - intros [stateSlots hbody].
    pose proof (proj1 (@raw_traceConjunction M
      (traceSlotEnv M machineSequenceCount stateSlots
        (scons M index
          (traceSlotEnv M outerTraceSlotCount outerSlots tail)))
      (map invariantTraceEntry (seq 0 machineSequenceCount) ++ [invariant]))
      hbody) as hall.
    exists (rawInvariantStateOfSlots M stateSlots).
    split.
    + intros sequence hsequence.
      assert (hsequenceLt : sequence < machineSequenceCount).
      { apply in_seq in hsequence. lia. }
      assert (hentry : raw_formula_sat M
          (traceSlotEnv M machineSequenceCount stateSlots
            (scons M index
              (traceSlotEnv M outerTraceSlotCount outerSlots tail)))
          (invariantTraceEntry sequence)).
      {
        apply hall. apply in_app_iff. left.
        apply in_map. exact hsequence.
      }
      unfold invariantTraceEntry in hentry.
      apply (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)) in hentry.
      rewrite raw_invariant_inner_state in hentry by exact hsequenceLt.
      rewrite raw_invariant_inner_sequenceCode in hentry
        by exact hsequenceLt.
      rewrite raw_invariant_inner_sequenceStep in hentry
        by exact hsequenceLt.
      rewrite raw_invariant_inner_time in hentry.
      rewrite rawInvariantStateOfSlots_component.
      exact hentry.
    + unfold RawCanonicalInvariantHolds, rawCanonicalInvariantEnv.
      assert (hinvariant : raw_formula_sat M
          (traceSlotEnv M machineSequenceCount stateSlots
            (scons M index
              (traceSlotEnv M outerTraceSlotCount outerSlots tail)))
          invariant).
      {
        apply hall. apply in_app_iff. right. simpl. now left.
      }
      assert (henv : forall i,
        traceSlotEnv M machineSequenceCount stateSlots
          (scons M index
            (traceSlotEnv M outerTraceSlotCount outerSlots tail)) i =
        traceSlotEnv M machineSequenceCount
          (fun sequence => rawCanonicalStateComponent M
            (rawInvariantStateOfSlots M stateSlots) sequence)
          (scons M index
            (traceSlotEnv M outerTraceSlotCount outerSlots tail)) i).
      {
        intro i. unfold traceSlotEnv.
        destruct (i <? machineSequenceCount); [|reflexivity].
        symmetry. apply rawInvariantStateOfSlots_component.
      }
      apply (proj1 (raw_formula_sat_ext M invariant
        (traceSlotEnv M machineSequenceCount stateSlots
          (scons M index
            (traceSlotEnv M outerTraceSlotCount outerSlots tail)))
        (traceSlotEnv M machineSequenceCount
          (fun sequence => rawCanonicalStateComponent M
            (rawInvariantStateOfSlots M stateSlots) sequence)
          (scons M index
            (traceSlotEnv M outerTraceSlotCount outerSlots tail))) henv)).
      exact hinvariant.
  - intros [state [hstate hinvariant]].
    exists (fun sequence => rawCanonicalStateComponent M state sequence).
    apply (proj2 (@raw_traceConjunction M
      (traceSlotEnv M machineSequenceCount
        (fun sequence => rawCanonicalStateComponent M state sequence)
        (scons M index
          (traceSlotEnv M outerTraceSlotCount outerSlots tail)))
      (map invariantTraceEntry (seq 0 machineSequenceCount) ++ [invariant]))).
    intros f hf.
    apply in_app_iff in hf. destruct hf as [hf | hf].
    + apply in_map_iff in hf.
      destruct hf as [sequence [<- hsequence]].
      assert (hsequenceLt : sequence < machineSequenceCount).
      { apply in_seq in hsequence. lia. }
      unfold invariantTraceEntry.
      apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
      rewrite raw_invariant_inner_state by exact hsequenceLt.
      rewrite raw_invariant_inner_sequenceCode by exact hsequenceLt.
      rewrite raw_invariant_inner_sequenceStep by exact hsequenceLt.
      rewrite raw_invariant_inner_time.
      apply hstate. exact hsequence.
    + simpl in hf. destruct hf as [<- | []].
      exact hinvariant.
Qed.

(** ------------------------------------------------------------------
    PA induction along the (possibly nonstandard) trace. *)

Lemma raw_canonicalTraceInvariantThrough_iff : forall
    (M : RawPAModel) invariant outerSlots tail index,
  raw_formula_sat M
    (scons M index
      (traceSlotEnv M outerTraceSlotCount outerSlots tail))
    (canonicalTraceInvariantThrough invariant) <->
  (rawLe M index (outerSlots 0) ->
   exists state : RawCanonicalMachineState M,
     RawCanonicalTraceStateAt M outerSlots index state /\
     RawCanonicalInvariantHolds M invariant outerSlots tail index state).
Proof.
  intros M invariant outerSlots tail index.
  unfold canonicalTraceInvariantThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_coherence.
  cbn [raw_term_eval scons].
  rewrite raw_term_eval_traceLiftOne.
  rewrite raw_outerEnv_steps.
  rewrite raw_canonicalTraceInvariantAt_iff.
  tauto.
Qed.

Lemma raw_le_zero_left_invariant : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M, rawLe M (raw_zero M) x.
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (PA.Formula.BProv_Ax_s_leTermAt_zero_left [] (tVar 0)) e) as hle.
  change (rawLe M (raw_zero M) x) in hle.
  exact hle.
Qed.

Lemma raw_le_refl_invariant : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M, rawLe M x x.
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (PA.Formula.BProv_Ax_s_leTermAt_refl [] (tVar 0)) e) as hle.
  change (rawLe M x x) in hle.
  exact hle.
Qed.

Lemma raw_lt_of_succ_le_invariant : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y : M,
  rawLe M (raw_succ M x) y -> rawLt M x y.
Proof.
  intros M hPA x y hsuccLe.
  set (G := [Formula.leTermAt (tSucc (tVar 0)) (tVar 1)]).
  assert (hass : Formula.BProv Formula.Ax_s G
      (Formula.leTermAt (tSucc (tVar 0)) (tVar 1))).
  {
    apply Formula.BProv_ass. unfold G. simpl. now left.
  }
  pose proof (Formula.BProv_Ax_s_ltTermAt_of_succ_leTermAt
    G (tVar 0) (tVar 1) hass) as hstrict.
  set (e := scons M x
    (scons M y (fun _ : nat => raw_zero M))).
  apply (raw_sat_of_BProv_axs_context M G _ hPA hstrict e).
  intros g hg. unfold G in hg. simpl in hg.
  destruct hg as [<- | []].
  change (rawLe M (raw_succ M x) y).
  exact hsuccLe.
Qed.

Lemma raw_state_component_of_agreement : forall (M : RawPAModel)
    left right sequence,
  RawCanonicalStateAgreement M left right ->
  In sequence (seq 0 machineSequenceCount) ->
  rawCanonicalStateComponent M left sequence =
  rawCanonicalStateComponent M right sequence.
Proof.
  intros M left right [|r] [hpc hregisters] hsequence.
  - exact hpc.
  - cbn [rawCanonicalStateComponent]. apply hregisters.
    apply in_seq in hsequence. apply in_seq.
    unfold machineSequenceCount in hsequence. lia.
Qed.

Lemma raw_invariant_holds_of_agreement : forall (M : RawPAModel)
    invariant outerSlots tail index left right,
  RawCanonicalStateAgreement M left right ->
  RawCanonicalInvariantHolds M invariant outerSlots tail index left ->
  RawCanonicalInvariantHolds M invariant outerSlots tail index right.
Proof.
  intros M invariant outerSlots tail index left right hagree hleft.
  unfold RawCanonicalInvariantHolds, rawCanonicalInvariantEnv in *.
  assert (henv : forall i,
    traceSlotEnv M machineSequenceCount
      (fun sequence => rawCanonicalStateComponent M left sequence)
      (scons M index
        (traceSlotEnv M outerTraceSlotCount outerSlots tail)) i =
    traceSlotEnv M machineSequenceCount
      (fun sequence => rawCanonicalStateComponent M right sequence)
      (scons M index
        (traceSlotEnv M outerTraceSlotCount outerSlots tail)) i).
  {
    intro i. unfold traceSlotEnv.
    destruct (i <? machineSequenceCount) eqn:hi; [|reflexivity].
    apply raw_state_component_of_agreement; [exact hagree |].
    apply in_seq. apply Nat.ltb_lt in hi. lia.
  }
  apply (proj1 (raw_formula_sat_ext M invariant
    (traceSlotEnv M machineSequenceCount
      (fun sequence => rawCanonicalStateComponent M left sequence)
      (scons M index
        (traceSlotEnv M outerTraceSlotCount outerSlots tail)))
    (traceSlotEnv M machineSequenceCount
      (fun sequence => rawCanonicalStateComponent M right sequence)
      (scons M index
        (traceSlotEnv M outerTraceSlotCount outerSlots tail))) henv)).
  exact hleft.
Qed.

Definition RawCanonicalInvariantPreserved (M : RawPAModel)
    (invariant : PA.formula) (outerSlots : nat -> M) (tail : nat -> M) : Prop :=
  forall index current next,
    rawLt M index (outerSlots 0) ->
    RawCanonicalTraceStateAt M outerSlots index current ->
    RawCanonicalTraceStateAt M outerSlots (raw_succ M index) next ->
    RawCanonicalProgramStep M current next ->
    RawCanonicalInvariantHolds M invariant outerSlots tail index current ->
    RawCanonicalInvariantHolds M invariant outerSlots tail
      (raw_succ M index) next.

Arguments RawCanonicalInvariantPreserved M invariant outerSlots tail
  : clear implicits.

(** This is the central nonstandard-time theorem.  Its induction variable is
    an element of [M], so the proof necessarily invokes a first-order PA
    induction instance rather than Rocq's [nat] induction. *)
Theorem raw_coherent_trace_preserves_definable_invariant : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall invariant outerSlots tail initial,
  RawCanonicalCoherentTrace M outerSlots ->
  RawCanonicalTraceStateAt M outerSlots (raw_zero M) initial ->
  RawCanonicalInvariantHolds M invariant outerSlots tail
    (raw_zero M) initial ->
  RawCanonicalInvariantPreserved M invariant outerSlots tail ->
  forall final,
    RawCanonicalTraceStateAt M outerSlots (outerSlots 0) final ->
    RawCanonicalInvariantHolds M invariant outerSlots tail
      (outerSlots 0) final.
Proof.
  intros M hPA invariant outerSlots tail initial
    [hstepwise hfunctional] hinitial hinvariant hpreserved final hfinal.
  set (outerEnv :=
    traceSlotEnv M outerTraceSlotCount outerSlots tail).
  assert (hall : forall index,
      raw_formula_sat M (scons M index outerEnv)
        (canonicalTraceInvariantThrough invariant)).
  {
    apply (raw_definable_induction M hPA
      (canonicalTraceInvariantThrough invariant) outerEnv).
    - pose proof (@raw_canonicalTraceInvariantThrough_iff M
        invariant outerSlots tail (raw_zero M)) as hiff.
      unfold iff in hiff.
      apply (proj2 hiff).
      intros _. exists initial. split; assumption.
    - intros index hindex.
      pose proof (@raw_canonicalTraceInvariantThrough_iff M
        invariant outerSlots tail (raw_succ M index)) as hiff.
      unfold iff in hiff.
      apply (proj2 hiff).
      intro hsuccLe.
      assert (hindexLt : rawLt M index (outerSlots 0)).
      { exact (@raw_lt_of_succ_le_invariant M hPA index
          (outerSlots 0) hsuccLe). }
      assert (hindexLe : rawLe M index (outerSlots 0)).
      { exact (@raw_lt_to_le M index (outerSlots 0) hindexLt). }
      pose proof (@raw_canonicalTraceInvariantThrough_iff M
        invariant outerSlots tail index) as hiffIndex.
      unfold iff in hiffIndex.
      pose proof (proj1 hiffIndex hindex hindexLe) as hatIndex.
      destruct hatIndex as [witness [hwitnessState hwitnessInvariant]].
      destruct (hstepwise index hindexLt) as
        [current [next [hcurrent [hnext hmachine]]]].
      assert (hcurrentInvariant :
          RawCanonicalInvariantHolds M invariant outerSlots tail
            index current).
      {
        apply (@raw_invariant_holds_of_agreement M invariant outerSlots tail
          index witness current).
        - apply (hfunctional index witness current);
            assumption.
        - exact hwitnessInvariant.
      }
      exists next. split; [exact hnext |].
      exact (hpreserved index current next hindexLt hcurrent hnext
        hmachine hcurrentInvariant).
  }
  pose proof (@raw_canonicalTraceInvariantThrough_iff M
    invariant outerSlots tail (outerSlots 0)) as hiffFinal.
  unfold iff in hiffFinal.
  pose proof (proj1 hiffFinal (hall (outerSlots 0))
    (@raw_le_refl_invariant M hPA (outerSlots 0))) as hatFinal.
  destruct hatFinal as [witness [hwitnessState hwitnessInvariant]].
  apply (@raw_invariant_holds_of_agreement M invariant outerSlots tail
    (outerSlots 0) witness final).
  - apply (hfunctional (outerSlots 0) witness final);
      assumption.
  - exact hwitnessInvariant.
Qed.

(** ------------------------------------------------------------------
    A checker-specific safety-certificate boundary. *)

Definition RawCanonicalInvariantExcludesAcceptance (M : RawPAModel)
    (invariant : PA.formula) (outerSlots : nat -> M) (tail : nat -> M) : Prop :=
  forall final,
    RawCanonicalAcceptingFinalState M outerSlots final ->
    RawCanonicalInvariantHolds M invariant outerSlots tail
      (outerSlots 0) final -> False.

Arguments RawCanonicalInvariantExcludesAcceptance
  M invariant outerSlots tail : clear implicits.

(** A certificate is uniform over all raw PA models, all (possibly
    nonstandard) candidate proof codes, and all beta trace parameters.  The
    external bound [n] is inserted as the standard numeral by the same public
    environment used by [NoCanonicalRestrictedPAProofFormula]. *)
Definition RawCanonicalDefinableSafetyCertificate
    (n : nat) (invariant : PA.formula) : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
  forall (p : M) (outerSlots : nat -> M),
    RawCanonicalInvariantHolds M invariant outerSlots
      (@rawCanonicalRestrictedCheckerEnv M n p) (raw_zero M)
      (rawCanonicalInitialState M (rawStandardNumeral M n) p) /\
    RawCanonicalInvariantPreserved M invariant outerSlots
      (@rawCanonicalRestrictedCheckerEnv M n p) /\
    RawCanonicalInvariantExcludesAcceptance M invariant outerSlots
      (@rawCanonicalRestrictedCheckerEnv M n p).

(** Any such definable safety certificate rules out a canonical accepting
    graph even in nonstandard models. *)
Theorem raw_rejection_of_definable_safety_certificate : forall n invariant,
  RawCanonicalDefinableSafetyCertificate n invariant ->
  RawCanonicalRestrictedCheckerRejection n.
Proof.
  intros n invariant hcertificate M hPA p hcanonical.
  destruct (@raw_CanonicalRestrictedPAProofFormula_accepting_final_state
    M hPA (@rawCanonicalRestrictedCheckerEnv M n p) hcanonical) as
    [outerSlots [final [hcoherent [hinitial haccepting]]]].
  specialize (hcertificate M hPA p outerSlots).
  destruct hcertificate as [hinvariant [hpreserved hexcludes]].
  apply (hexcludes final haccepting).
  exact (@raw_coherent_trace_preserves_definable_invariant M hPA
    invariant outerSlots (@rawCanonicalRestrictedCheckerEnv M n p)
    (rawCanonicalInitialState M (rawStandardNumeral M n) p)
    hcoherent hinitial hinvariant hpreserved final (proj1 haccepting)).
Qed.

(** Combining the preceding semantic reduction with raw-model completeness
    yields the desired object-language theorem as soon as the three concrete
    invariant obligations are discharged. *)
Corollary PA_BProv_NoCanonicalRestrictedPAProofFormula_of_definable_invariant :
  forall n invariant,
  RawCanonicalDefinableSafetyCertificate n invariant ->
  Formula.BProv Formula.Ax_s []
    (NoCanonicalRestrictedPAProofFormula n).
Proof.
  intros n invariant hcertificate.
  apply PA_BProv_NoCanonicalRestrictedPAProofFormula_of_raw_rejection.
  exact (@raw_rejection_of_definable_safety_certificate
    n invariant hcertificate).
Qed.

End PABoundedCanonicalCheckerDefinableInvariant.
