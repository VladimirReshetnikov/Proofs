(**
  A concrete safety invariant for the compiled canonical checker.

  The invariant says exactly that the current state is not an accepting exit:
  if its program counter is outside the compiled instruction interval, then
  output register zero is not one.  It is an ordinary PA formula over the
  state layout supplied by [CanonicalCheckerDefinableInvariant].

  This file completely proves the initial-state and accepting-final-state
  obligations.  It also identifies the final genuine machine step of any
  purported accepting trace.  The only remaining premise is preservation of
  this explicit invariant by the compiled checker.  That premise is stated as
  a [Prop], not introduced as an axiom: discharging it requires the missing
  fixed-level partial-truth/compiler-soundness development.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedCheckerRawReduction CanonicalCheckerTrace
  CanonicalCheckerRawReduction CanonicalCheckerRawTraceReflection
  CanonicalCheckerRawTraceCoherence CanonicalCheckerDefinableInvariant.

Import ListNotations.

Module PABoundedCanonicalCheckerConcreteInvariant.

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
Import PABoundedCanonicalCheckerDefinableInvariant.

(** State component zero is the PC and component one is machine register
    zero, the compiler's output register. *)
Definition canonicalCheckerNoAcceptingExitInvariant : PA.formula :=
  pImp
    (outsideCanonicalProgram (invariantStateComponent 0))
    (pImp
      (pEq (invariantStateComponent 1) (Term.numeral 1))
      pBot).

Definition RawCanonicalNoAcceptingExit (M : RawPAModel)
    (state : RawCanonicalMachineState M) : Prop :=
  RawCanonicalOutsideProgram M (rawCanonicalPC state) ->
  rawCanonicalRegister state 0 = rawStandardNumeral M 1 ->
  False.

Arguments RawCanonicalNoAcceptingExit M state : clear implicits.

(** Evaluation of an invariant state variable is exactly the corresponding
    component of the supplied raw state. *)
Lemma raw_concreteInvariant_state_component : forall (M : RawPAModel)
    outerSlots tail index state sequence,
  sequence < machineSequenceCount ->
  raw_term_eval M
    (rawCanonicalInvariantEnv M outerSlots tail index state)
    (invariantStateComponent sequence) =
  rawCanonicalStateComponent M state sequence.
Proof.
  intros M outerSlots tail index state sequence hsequence.
  unfold rawCanonicalInvariantEnv.
  apply raw_invariant_inner_state.
  exact hsequence.
Qed.

(** Exact arbitrary-model semantics of the concrete invariant. *)
Theorem raw_canonicalCheckerNoAcceptingExitInvariant_iff : forall
    (M : RawPAModel) outerSlots tail index state,
  RawCanonicalInvariantHolds M canonicalCheckerNoAcceptingExitInvariant
    outerSlots tail index state <->
  RawCanonicalNoAcceptingExit M state.
Proof.
  intros M outerSlots tail index state.
  unfold RawCanonicalInvariantHolds,
    canonicalCheckerNoAcceptingExitInvariant,
    RawCanonicalNoAcceptingExit.
  change
    ((raw_formula_sat M
        (rawCanonicalInvariantEnv M outerSlots tail index state)
        (outsideCanonicalProgram (invariantStateComponent 0)) ->
      raw_term_eval M
        (rawCanonicalInvariantEnv M outerSlots tail index state)
        (invariantStateComponent 1) =
      raw_term_eval M
        (rawCanonicalInvariantEnv M outerSlots tail index state)
        (Term.numeral 1) -> False) <->
     (RawCanonicalOutsideProgram M (rawCanonicalPC state) ->
      rawCanonicalRegister state 0 = rawStandardNumeral M 1 -> False)).
  rewrite (@raw_outsideCanonicalProgram_iff M
    (rawCanonicalInvariantEnv M outerSlots tail index state)
    (invariantStateComponent 0)).
  rewrite raw_concreteInvariant_state_component by
    (unfold machineSequenceCount; lia).
  rewrite raw_concreteInvariant_state_component by
    (unfold machineSequenceCount, canonicalCheckerCounterCount; lia).
  rewrite raw_term_eval_standard_numeral.
  reflexivity.
Qed.

(** Zero and the standard numeral one are distinct in every raw PA model.
    This is derived from PA order, not assumed as a field of [RawPAModel]. *)
Lemma raw_zero_ne_one_concrete : forall (M : RawPAModel),
  RawPASatisfies M ->
  raw_zero M <> rawStandardNumeral M 1.
Proof.
  intros M hPA heq.
  pose proof (@raw_lt_self_succ_coherence M hPA (raw_zero M)) as hlt.
  change (raw_zero M = raw_succ M (raw_zero M)) in heq.
  rewrite <- heq in hlt.
  exact (@raw_not_lt_zero M hPA (raw_zero M) hlt).
Qed.

(** The compiled checker starts with output register zero, hence cannot
    already be an accepting exit.  No trace-code assumption is needed. *)
Theorem raw_noAcceptingExitInvariant_initial : forall (M : RawPAModel),
  RawPASatisfies M -> forall outerSlots tail bound certificate,
  RawCanonicalInvariantHolds M canonicalCheckerNoAcceptingExitInvariant
    outerSlots tail (raw_zero M)
    (rawCanonicalInitialState M bound certificate).
Proof.
  intros M hPA outerSlots tail bound certificate.
  apply (proj2 (@raw_canonicalCheckerNoAcceptingExitInvariant_iff
    M outerSlots tail (raw_zero M)
    (rawCanonicalInitialState M bound certificate))).
  intros _ houtput.
  apply (@raw_zero_ne_one_concrete M hPA).
  exact houtput.
Qed.

(** An accepting final state is, by definition, precisely a counterexample
    to the concrete invariant. *)
Theorem raw_noAcceptingExitInvariant_excludes : forall (M : RawPAModel)
    outerSlots tail,
  RawCanonicalInvariantExcludesAcceptance M
    canonicalCheckerNoAcceptingExitInvariant outerSlots tail.
Proof.
  intros M outerSlots tail final
    [hstate [houtside houtput]] hinvariant.
  apply (proj1 (@raw_canonicalCheckerNoAcceptingExitInvariant_iff
    M outerSlots tail (outerSlots 0) final)) in hinvariant.
  exact (hinvariant houtside houtput).
Qed.

(** ------------------------------------------------------------------
    The exact one-step preservation seam. *)

Definition RawCanonicalNoAcceptingExitStepClosed (M : RawPAModel)
    (outerSlots : nat -> M) (tail : nat -> M) : Prop :=
  forall index current next,
    rawLt M index (outerSlots 0) ->
    RawCanonicalTraceStateAt M outerSlots index current ->
    RawCanonicalTraceStateAt M outerSlots (raw_succ M index) next ->
    RawCanonicalProgramStep M current next ->
    RawCanonicalNoAcceptingExit M current ->
    RawCanonicalNoAcceptingExit M next.

Arguments RawCanonicalNoAcceptingExitStepClosed M outerSlots tail
  : clear implicits.

Theorem raw_noAcceptingExitInvariant_preserved_iff : forall
    (M : RawPAModel) outerSlots tail,
  RawCanonicalInvariantPreserved M
    canonicalCheckerNoAcceptingExitInvariant outerSlots tail <->
  RawCanonicalNoAcceptingExitStepClosed M outerSlots tail.
Proof.
  intros M outerSlots tail. split.
  - intros hpreserved index current next hindex hcurrent hnext
      hmachine hsafe.
    apply (proj1 (@raw_canonicalCheckerNoAcceptingExitInvariant_iff
      M outerSlots tail (raw_succ M index) next)).
    apply (hpreserved index current next hindex hcurrent hnext hmachine).
    apply (proj2 (@raw_canonicalCheckerNoAcceptingExitInvariant_iff
      M outerSlots tail index current)).
    exact hsafe.
  - intros hclosed index current next hindex hcurrent hnext
      hmachine hinvariant.
    apply (proj2 (@raw_canonicalCheckerNoAcceptingExitInvariant_iff
      M outerSlots tail (raw_succ M index) next)).
    apply (hclosed index current next hindex hcurrent hnext hmachine).
    apply (proj1 (@raw_canonicalCheckerNoAcceptingExitInvariant_iff
      M outerSlots tail index current)).
    exact hinvariant.
Qed.

(** The only checker-specific obligation left by this module.  It is a
    metatheoretic family indexed by the external fixed bound, but quantifies
    over arbitrary raw PA models and nonstandard candidate certificates. *)
Definition CanonicalCheckerNoAcceptingExitPreservation (n : nat) : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
  forall (certificate : M) (outerSlots : nat -> M),
    RawCanonicalNoAcceptingExitStepClosed M outerSlots
      (@rawCanonicalRestrictedCheckerEnv M n certificate).

(** Base and final contradiction are now discharged; preservation is the
    sole named premise. *)
Theorem raw_noAcceptingExit_safety_certificate : forall n,
  CanonicalCheckerNoAcceptingExitPreservation n ->
  RawCanonicalDefinableSafetyCertificate n
    canonicalCheckerNoAcceptingExitInvariant.
Proof.
  intros n hpreserved M hPA certificate outerSlots.
  split.
  - apply (@raw_noAcceptingExitInvariant_initial M hPA outerSlots
      (@rawCanonicalRestrictedCheckerEnv M n certificate)
      (rawStandardNumeral M n) certificate).
  - split.
    + apply (proj2 (@raw_noAcceptingExitInvariant_preserved_iff M
        outerSlots (@rawCanonicalRestrictedCheckerEnv M n certificate))).
      exact (hpreserved M hPA certificate outerSlots).
    + apply raw_noAcceptingExitInvariant_excludes.
Qed.

Corollary raw_rejection_of_noAcceptingExit_preservation : forall n,
  CanonicalCheckerNoAcceptingExitPreservation n ->
  RawCanonicalRestrictedCheckerRejection n.
Proof.
  intros n hpreserved.
  apply (@raw_rejection_of_definable_safety_certificate n
    canonicalCheckerNoAcceptingExitInvariant).
  exact (@raw_noAcceptingExit_safety_certificate n hpreserved).
Qed.

Corollary PA_BProv_NoCanonicalRestrictedPAProofFormula_of_concrete_invariant :
  forall n,
  CanonicalCheckerNoAcceptingExitPreservation n ->
  Formula.BProv Formula.Ax_s []
    (NoCanonicalRestrictedPAProofFormula n).
Proof.
  intros n hpreserved.
  apply (@PA_BProv_NoCanonicalRestrictedPAProofFormula_of_definable_invariant
    n canonicalCheckerNoAcceptingExitInvariant).
  exact (@raw_noAcceptingExit_safety_certificate n hpreserved).
Qed.

(** ------------------------------------------------------------------
    Concrete control-flow checkpoints. *)

Definition RawCanonicalCurrentPCInCompiledCode (M : RawPAModel)
    (state : RawCanonicalMachineState M) : Prop :=
  exists offset instruction,
    In (offset, instruction)
      (combine (seq 0 (length canonicalCheckerMMAProgram))
        canonicalCheckerMMAProgram) /\
    rawCanonicalPC state = rawStandardNumeral M (S offset).

Arguments RawCanonicalCurrentPCInCompiledCode M state : clear implicits.

(** Every reflected machine step names the exact compiled instruction at its
    current PC.  This theorem is purely structural and needs no arithmetic
    laws. *)
Lemma raw_programStep_currentPC_in_compiled_code : forall (M : RawPAModel)
    current next,
  RawCanonicalProgramStep M current next ->
  RawCanonicalCurrentPCInCompiledCode M current.
Proof.
  intros M current next [entry [hinstruction hstep]].
  destruct entry as [offset instruction].
  exists offset, instruction. split; [exact hinstruction |].
  unfold RawCanonicalInstructionStep in hstep. cbn in hstep.
  exact (proj1 hstep).
Qed.

(** A purported accepting coherent trace cannot have length zero: its
    initial output is zero whereas its accepting final output is one. *)
Lemma raw_accepting_trace_length_nonzero : forall (M : RawPAModel),
  RawPASatisfies M -> forall outerSlots bound certificate final,
  RawCanonicalCoherentTrace M outerSlots ->
  RawCanonicalTraceStateAt M outerSlots (raw_zero M)
    (rawCanonicalInitialState M bound certificate) ->
  RawCanonicalAcceptingFinalState M outerSlots final ->
  outerSlots 0 <> raw_zero M.
Proof.
  intros M hPA outerSlots bound certificate final
    [_ hfunctional] hinitial [hfinal [_ houtput]] hzero.
  assert (hagreement : RawCanonicalStateAgreement M
      (rawCanonicalInitialState M bound certificate) final).
  {
    apply (hfunctional (raw_zero M)); [exact hinitial |].
    rewrite <- hzero. exact hfinal.
  }
  destruct hagreement as [_ hregisters].
  assert (hregister : rawCanonicalRegister
      (rawCanonicalInitialState M bound certificate) 0 =
      rawCanonicalRegister final 0).
  {
    apply hregisters. apply in_seq.
    unfold canonicalCheckerCounterCount. lia.
  }
  cbn [rawCanonicalInitialState rawCanonicalInitialRegister] in hregister.
  rewrite houtput in hregister.
  exact (@raw_zero_ne_one_concrete M hPA hregister).
Qed.

(** Consequently every accepting trace exposes a genuine final transition
    from a PC naming one of the concrete compiled instructions. *)
Theorem raw_accepting_trace_has_compiled_exit_step : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall outerSlots bound certificate final,
  RawCanonicalCoherentTrace M outerSlots ->
  RawCanonicalTraceStateAt M outerSlots (raw_zero M)
    (rawCanonicalInitialState M bound certificate) ->
  RawCanonicalAcceptingFinalState M outerSlots final ->
  exists predecessor current exit,
    outerSlots 0 = raw_succ M predecessor /\
    RawCanonicalTraceStateAt M outerSlots predecessor current /\
    RawCanonicalTraceStateAt M outerSlots (outerSlots 0) exit /\
    RawCanonicalProgramStep M current exit /\
    RawCanonicalCurrentPCInCompiledCode M current /\
    (RawCanonicalNoAcceptingExit M exit -> False).
Proof.
  intros M hPA outerSlots bound certificate final
    hcoherent hinitial haccepting.
  destruct (@raw_zero_or_successor_coherence M hPA (outerSlots 0))
    as [hzero | [predecessor hsuccessor]].
  - exfalso. exact
      (@raw_accepting_trace_length_nonzero M hPA outerSlots bound
        certificate final hcoherent hinitial haccepting hzero).
  - destruct hcoherent as [hstepwise hfunctional].
    assert (hlt : rawLt M predecessor (outerSlots 0)).
    {
      rewrite hsuccessor.
      exact (@raw_lt_self_succ_coherence M hPA predecessor).
    }
    destruct (hstepwise predecessor hlt) as
      [current [exit [hcurrent [hexit hmachine]]]].
    exists predecessor, current, exit.
    split; [exact hsuccessor |].
    split; [exact hcurrent |].
    split.
    + rewrite hsuccessor. exact hexit.
    + split; [exact hmachine |].
      split.
      * apply raw_programStep_currentPC_in_compiled_code with exit.
        exact hmachine.
      * intro hexitSafe.
      destruct haccepting as [hfinal [houtside houtput]].
      assert (hagreement : RawCanonicalStateAgreement M exit final).
      {
        apply (hfunctional (outerSlots 0)).
        - rewrite hsuccessor. exact hexit.
        - exact hfinal.
      }
      destruct hagreement as [hpc hregisters].
      assert (hexitOutside :
          RawCanonicalOutsideProgram M (rawCanonicalPC exit)).
      { rewrite hpc. exact houtside. }
      assert (hexitOutput : rawCanonicalRegister exit 0 =
          rawStandardNumeral M 1).
      {
        rewrite (hregisters 0) by
          (apply in_seq; unfold canonicalCheckerCounterCount; lia).
        exact houtput.
      }
      exact (hexitSafe hexitOutside hexitOutput).
Qed.

End PABoundedCanonicalCheckerConcreteInvariant.
