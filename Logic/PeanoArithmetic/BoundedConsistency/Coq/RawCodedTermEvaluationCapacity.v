(**
  Discharging the fixed-step capacity premise for coded term evaluation.

  A value table uses one Goedel-beta step for its whole (possibly
  nonstandard) prefix.  Choosing that step before evaluating the prefix
  appears circular: its moduli must dominate values which have not yet been
  computed.  The construction here removes the circle with a PA-definable,
  step-parametric capacity trace.

  At each prefix [i] the trace stores a carrier element [capacity] such that
  *every* beta coding step which is common through [i] and at least
  [S capacity] realizes an evaluation traversal through [i].  A probe step
  realizes the old prefix and discovers the next value.  The new capacity is
  [oldCapacity + value].  For an arbitrary larger step, global prefix
  agreement and local-row extensionality prove that the next value is the
  same one found by the probe, so CRT can append it.  PA induction, rather
  than Rocq recursion on the carrier, iterates this argument through an
  arbitrary model-valued bound.

  Finally, one complete traversal implies the universal local-output bound
  required by [RawTermEvaluationFixedStepCapacity]: compare any proposed
  local row with the complete traversal below its target, then use the
  complete table's beta remainder bound.  Thus no capacity premise remains
  on the honest model-internal syntax/assignment domain.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedAssignment
  RawCodedTermEvaluationTraversal RawCodedTermEvaluationRealization.

Import ListNotations.

Module PABoundedRawCodedTermEvaluationCapacity.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationRealization.

(** ------------------------------------------------------------------
    Coding steps above an explicit capacity. *)

Definition RawTermEvaluationCodingStep (M : RawPAModel)
    (bound capacity step : M) : Prop :=
  RawCommonMultipleThrough M bound step /\
  rawLe M (raw_succ M capacity) step.

Arguments RawTermEvaluationCodingStep M bound capacity step
  : clear implicits.

Lemma raw_sat_termEvaluationCodingStepTermAt_iff : forall
    (M : RawPAModel) e bound capacity step,
  raw_formula_sat M e
    (Formula.betaCodingStepTermAt bound capacity step) <->
  RawTermEvaluationCodingStep M
    (raw_term_eval M e bound)
    (raw_term_eval M e capacity) (raw_term_eval M e step).
Proof.
  intros M e bound capacity step.
  unfold Formula.betaCodingStepTermAt, RawTermEvaluationCodingStep.
  cbn [raw_formula_sat].
  rewrite raw_sat_commonMultipleThroughTermAt_iff,
    raw_sat_leTermAt_iff_traversal.
  reflexivity.
Qed.

Theorem raw_termEvaluationCodingStep_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall bound capacity : M,
  exists step : M,
    RawTermEvaluationCodingStep M bound capacity step.
Proof.
  intros M hPA bound capacity.
  set (tail := fun _ : nat => raw_zero M).
  set (e := scons M bound (scons M capacity tail)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (BProv_Ax_s_betaCodingStepExistsTermAt []
      (tVar 0) (tVar 1)) e) as hsat.
  unfold Formula.betaCodingStepExistsTermAt in hsat.
  cbn [raw_formula_sat] in hsat.
  destruct hsat as [step hstep]. exists step.
  apply (proj1 (raw_sat_termEvaluationCodingStepTermAt_iff M
    (scons M step e)
    (Term.rename S (tVar 0))
    (Term.rename S (tVar 1)) (tVar 0))).
  exact hstep.
Qed.

(** Elementary capacity inequalities. *)
Lemma raw_capacity_le_add_left : forall (M : RawPAModel),
  forall left right : M,
  rawLe M left (raw_add M left right).
Proof.
  intros M left right. exists right. reflexivity.
Qed.

Lemma raw_capacity_le_add_right : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right : M,
  rawLe M right (raw_add M left right).
Proof.
  intros M hPA left right. exists left.
  apply raw_add_comm. exact hPA.
Qed.

Lemma raw_capacity_succ_le : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right : M,
  rawLe M left right ->
  rawLe M (raw_succ M left) (raw_succ M right).
Proof.
  intros M hPA left right [gap hgap]. exists gap.
  rewrite raw_succ_add_pair by exact hPA.
  now rewrite hgap.
Qed.

Lemma raw_termEvaluationCodingStep_old_of_sum : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall current oldCapacity value step,
  RawTermEvaluationCodingStep M (raw_succ M current)
    (raw_add M oldCapacity value) step ->
  RawTermEvaluationCodingStep M current oldCapacity step.
Proof.
  intros M hPA current oldCapacity value step [hcommon hlarge]. split.
  - exact (raw_commonMultipleThrough_weaken M hPA
      current (raw_succ M current) step
      (raw_assignment_lt_self_succ M hPA current) hcommon).
  - apply (raw_le_trans M hPA
      (raw_succ M oldCapacity)
      (raw_succ M (raw_add M oldCapacity value)) step).
    + apply raw_capacity_succ_le; [exact hPA |].
      apply raw_capacity_le_add_left.
    + exact hlarge.
Qed.

Lemma raw_termEvaluationCodingStep_old_same_capacity : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall current capacity step,
  RawTermEvaluationCodingStep M (raw_succ M current) capacity step ->
  RawTermEvaluationCodingStep M current capacity step.
Proof.
  intros M hPA current capacity step [hcommon hlarge]. split.
  - exact (raw_commonMultipleThrough_weaken M hPA
      current (raw_succ M current) step
      (raw_assignment_lt_self_succ M hPA current) hcommon).
  - exact hlarge.
Qed.

(** A step above [S (oldCapacity + value)] makes [value] a valid beta
    remainder at the new target. *)
Lemma raw_termEvaluationCodingStep_value_bound : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall current oldCapacity value step,
  RawTermEvaluationCodingStep M (raw_succ M current)
    (raw_add M oldCapacity value) step ->
  rawLt M value (rawBetaModulus M step current).
Proof.
  intros M hPA current oldCapacity value step [_ hlarge].
  assert (hvalueSum : rawLe M value
      (raw_add M oldCapacity value)).
  { exact (raw_capacity_le_add_right M hPA oldCapacity value). }
  assert (hsuccValueStep : rawLe M (raw_succ M value) step).
  {
    apply (raw_le_trans M hPA
      (raw_succ M value)
      (raw_succ M (raw_add M oldCapacity value)) step).
    - exact (raw_capacity_succ_le M hPA
        value (raw_add M oldCapacity value) hvalueSum).
    - exact hlarge.
  }
  assert (hvalueStep : rawLt M value step).
  { exact (raw_lt_of_succ_le_traversal M hPA value step hsuccValueStep). }
  assert (hstepProduct : rawLe M step
      (raw_mul M (raw_succ M current) step)).
  {
    exists (raw_mul M current step).
    rewrite raw_succ_mul by exact hPA.
    apply raw_add_comm. exact hPA.
  }
  assert (hstepModulus : rawLt M step
      (raw_succ M (raw_mul M (raw_succ M current) step))).
  { exact (raw_lt_succ_of_le M hPA _ _ hstepProduct). }
  unfold rawBetaModulus.
  exact (raw_assignment_lt_trans M hPA
    value step _ hvalueStep hstepModulus).
Qed.

(** ------------------------------------------------------------------
    The step-parametric capacity trace and its exact PA semantics. *)

Definition RawTermEvaluationTraceCapacity (M : RawPAModel)
    (current assignmentCode assignmentStep supportCode supportStep : M)
    : Prop :=
  exists capacity : M,
    forall tableStep : M,
      RawTermEvaluationCodingStep M current capacity tableStep ->
      RawTermEvaluationPrefixRealized M current
        assignmentCode assignmentStep tableStep supportCode supportStep.

Arguments RawTermEvaluationTraceCapacity
  M current assignmentCode assignmentStep supportCode supportStep
  : clear implicits.

Definition termEvaluationTraceCapacityTermAt
    (current assignmentCode assignmentStep supportCode supportStep : term)
    : formula :=
  pEx (pAll
    (pImp
      (Formula.betaCodingStepTermAt
        (liftTerm 2 current) (tVar 1) (tVar 0))
      (termEvaluationPrefixRealizedTermAt
        (liftTerm 2 current)
        (liftTerm 2 assignmentCode) (liftTerm 2 assignmentStep)
        (tVar 0) (liftTerm 2 supportCode) (liftTerm 2 supportStep)))).

Lemma raw_sat_termEvaluationTraceCapacityTermAt_iff : forall
    (M : RawPAModel) e current assignmentCode assignmentStep
      supportCode supportStep,
  raw_formula_sat M e
    (termEvaluationTraceCapacityTermAt
      current assignmentCode assignmentStep supportCode supportStep) <->
  RawTermEvaluationTraceCapacity M
    (raw_term_eval M e current)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e current assignmentCode assignmentStep supportCode supportStep.
  unfold termEvaluationTraceCapacityTermAt,
    RawTermEvaluationTraceCapacity.
  cbn [raw_formula_sat]. split.
  - intros [capacity hall]. exists capacity.
    intros tableStep hcoding.
    assert (hcodingSat : raw_formula_sat M
        (scons M tableStep (scons M capacity e))
        (Formula.betaCodingStepTermAt
          (liftTerm 2 current) (tVar 1) (tVar 0))).
    {
      apply (proj2 (raw_sat_termEvaluationCodingStepTermAt_iff M
        (scons M tableStep (scons M capacity e))
        (liftTerm 2 current) (tVar 1) (tVar 0))).
      rewrite raw_term_eval_liftTerm_two_traversal.
      cbn [raw_term_eval scons]. exact hcoding.
    }
    pose proof (hall tableStep hcodingSat) as hprefixSat.
    apply (proj1 (raw_sat_termEvaluationPrefixRealizedTermAt_iff M
      (scons M tableStep (scons M capacity e))
      (liftTerm 2 current)
      (liftTerm 2 assignmentCode) (liftTerm 2 assignmentStep)
      (tVar 0) (liftTerm 2 supportCode) (liftTerm 2 supportStep)))
      in hprefixSat.
    rewrite !raw_term_eval_liftTerm_two_traversal in hprefixSat.
    cbn [raw_term_eval scons] in hprefixSat. exact hprefixSat.
  - intros [capacity hall]. exists capacity.
    intros tableStep hcodingSat.
    pose proof (proj1 (raw_sat_termEvaluationCodingStepTermAt_iff M
      (scons M tableStep (scons M capacity e))
      (liftTerm 2 current) (tVar 1) (tVar 0)) hcodingSat)
      as hcoding.
    rewrite raw_term_eval_liftTerm_two_traversal in hcoding.
    cbn [raw_term_eval scons] in hcoding.
    pose proof (hall tableStep hcoding) as hprefix.
    apply (proj2 (raw_sat_termEvaluationPrefixRealizedTermAt_iff M
      (scons M tableStep (scons M capacity e))
      (liftTerm 2 current)
      (liftTerm 2 assignmentCode) (liftTerm 2 assignmentStep)
      (tVar 0) (liftTerm 2 supportCode) (liftTerm 2 supportStep))).
    rewrite !raw_term_eval_liftTerm_two_traversal.
    cbn [raw_term_eval scons]. exact hprefix.
Qed.

Lemma raw_termEvaluationTraceCapacity_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall assignmentCode assignmentStep supportCode supportStep,
  RawTermEvaluationTraceCapacity M (raw_zero M)
    assignmentCode assignmentStep supportCode supportStep.
Proof.
  intros M hPA assignmentCode assignmentStep supportCode supportStep.
  exists (raw_zero M). intros tableStep _.
  exact (raw_termEvaluationPrefixRealized_zero M hPA
    assignmentCode assignmentStep tableStep supportCode supportStep).
Qed.

(** Compare two old prefixes, possibly using different beta steps, to show
    that their proposed next values coincide. *)
Lemma raw_termEvaluation_next_value_independent : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall current assignmentCode assignmentStep supportCode supportStep
    leftTableCode leftTableStep rightTableCode rightTableStep
    leftValue rightValue,
  RawTermEvaluationTraversal M current
    assignmentCode assignmentStep leftTableCode leftTableStep
    supportCode supportStep ->
  RawTermEvaluationTraversal M current
    assignmentCode assignmentStep rightTableCode rightTableStep
    supportCode supportStep ->
  RawTermEvaluationClosedStep M current leftValue
    assignmentCode assignmentStep leftTableCode leftTableStep
    supportCode supportStep ->
  RawTermEvaluationClosedStep M current rightValue
    assignmentCode assignmentStep rightTableCode rightTableStep
    supportCode supportStep ->
  leftValue = rightValue.
Proof.
  intros M hPA current assignmentCode assignmentStep supportCode supportStep
    leftTableCode leftTableStep rightTableCode rightTableStep
    leftValue rightValue hleftTraversal hrightTraversal hleftStep hrightStep.
  pose proof (raw_termEvaluationTraversals_agree_below M hPA
    current assignmentCode assignmentStep
    leftTableCode leftTableStep supportCode supportStep
    rightTableCode rightTableStep supportCode supportStep
    hleftTraversal hrightTraversal) as hagree.
  exact (raw_termEvaluationClosedStep_extensional M hPA
    assignmentCode assignmentStep
    leftTableCode leftTableStep supportCode supportStep
    rightTableCode rightTableStep supportCode supportStep
    current leftValue rightValue hagree hleftStep hrightStep).
Qed.

Theorem raw_termEvaluationTraceCapacity_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep supportCode supportStep current,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  RawTermSyntaxAssignmentAdequate M limit
    assignmentCode assignmentStep supportCode supportStep ->
  rawLt M current limit ->
  RawTermEvaluationTraceCapacity M current
    assignmentCode assignmentStep supportCode supportStep ->
  RawTermEvaluationTraceCapacity M (raw_succ M current)
    assignmentCode assignmentStep supportCode supportStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep supportCode supportStep
    current [hsupportDefined hsyntaxRows] hadequate hcurrent
    [oldCapacity holdCapacity].
  destruct (raw_termEvaluationCodingStep_exists M hPA
    current oldCapacity) as [probeStep hprobeCoding].
  destruct (holdCapacity probeStep hprobeCoding)
    as [probeTableCode hprobeTraversal].
  destruct (hsupportDefined current hcurrent)
    as [supportValue hsupportValue].
  destruct (classic (supportValue = rawNumeralValue M 1))
    as [hsupportedValue | hnotSupported].
  - subst supportValue.
    pose proof hsupportValue as hcurrentSupported.
    pose proof (hsyntaxRows current hcurrent hcurrentSupported)
      as hsyntaxStep.
    destruct (raw_termSyntaxStep_evaluation_exists M hPA
      limit assignmentCode assignmentStep supportCode supportStep
      probeTableCode probeStep current hadequate hcurrent
      hcurrentSupported (proj1 (proj2 hprobeTraversal)) hsyntaxStep)
      as [probeValue hprobeStep].
    exists (raw_add M oldCapacity probeValue).
    intros tableStep hnewCoding.
    pose proof (raw_termEvaluationCodingStep_old_of_sum M hPA
      current oldCapacity probeValue tableStep hnewCoding)
      as holdCoding.
    destruct (holdCapacity tableStep holdCoding)
      as [oldTableCode holdTraversal].
    destruct (raw_termSyntaxStep_evaluation_exists M hPA
      limit assignmentCode assignmentStep supportCode supportStep
      oldTableCode tableStep current hadequate hcurrent
      hcurrentSupported (proj1 (proj2 holdTraversal)) hsyntaxStep)
      as [value hstep].
    assert (hvalue : probeValue = value).
    {
      exact (raw_termEvaluation_next_value_independent M hPA
        current assignmentCode assignmentStep supportCode supportStep
        probeTableCode probeStep oldTableCode tableStep
        probeValue value hprobeTraversal holdTraversal hprobeStep hstep).
    }
    subst value.
    assert (hbound : rawLt M probeValue
        (rawBetaModulus M tableStep current)).
    {
      exact (raw_termEvaluationCodingStep_value_bound M hPA
        current oldCapacity probeValue tableStep hnewCoding).
    }
    assert (hcommon : RawCommonMultipleThrough M current tableStep).
    { exact (proj1 holdCoding). }
    destruct (raw_betaCodeExtension_exists M hPA oldTableCode tableStep
      current probeValue hcommon hbound) as [newTableCode hext].
    exists newTableCode.
    apply (raw_termEvaluationTraversal_beta_extend M hPA
      assignmentCode assignmentStep supportCode supportStep
      oldTableCode newTableCode tableStep current probeValue).
    + exact holdTraversal.
    + exact (raw_definedThrough_support_succ M hPA
        limit supportCode supportStep current hsupportDefined hcurrent).
    + exact hext.
    + intros _. exact hstep.
  - exists oldCapacity. intros tableStep hnewCoding.
    pose proof (raw_termEvaluationCodingStep_old_same_capacity M hPA
      current oldCapacity tableStep hnewCoding) as holdCoding.
    destruct (holdCapacity tableStep holdCoding)
      as [oldTableCode holdTraversal].
    assert (hcommon : RawCommonMultipleThrough M current tableStep).
    { exact (proj1 holdCoding). }
    pose proof (raw_zero_lt_betaModulus M hPA tableStep current)
      as hzeroBound.
    destruct (raw_betaCodeExtension_exists M hPA oldTableCode tableStep
      current (raw_zero M) hcommon hzeroBound)
      as [newTableCode hext].
    exists newTableCode.
    apply (raw_termEvaluationTraversal_beta_extend M hPA
      assignmentCode assignmentStep supportCode supportStep
      oldTableCode newTableCode tableStep current (raw_zero M)).
    + exact holdTraversal.
    + exact (raw_definedThrough_support_succ M hPA
        limit supportCode supportStep current hsupportDefined hcurrent).
    + exact hext.
    + intros hsupported. exfalso. apply hnotSupported.
      exact (raw_codedAssignmentLookup_functional M hPA
        supportCode supportStep current
        supportValue (rawNumeralValue M 1)
        hsupportValue hsupported).
Qed.

(** ------------------------------------------------------------------
    Genuine PA induction through the syntax bound. *)

Definition RawTermEvaluationTraceCapacityThrough (M : RawPAModel)
    (current limit assignmentCode assignmentStep supportCode supportStep : M)
    : Prop :=
  rawLe M current limit ->
  RawTermEvaluationTraceCapacity M current
    assignmentCode assignmentStep supportCode supportStep.

Definition termEvaluationTraceCapacityThroughTermAt
    (current limit assignmentCode assignmentStep supportCode supportStep
      : term) : formula :=
  pImp
    (Formula.leTermAt current limit)
    (termEvaluationTraceCapacityTermAt current
      assignmentCode assignmentStep supportCode supportStep).

Lemma raw_sat_termEvaluationTraceCapacityThroughTermAt_iff : forall
    (M : RawPAModel) e current limit assignmentCode assignmentStep
      supportCode supportStep,
  raw_formula_sat M e
    (termEvaluationTraceCapacityThroughTermAt current limit
      assignmentCode assignmentStep supportCode supportStep) <->
  RawTermEvaluationTraceCapacityThrough M
    (raw_term_eval M e current) (raw_term_eval M e limit)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros. unfold termEvaluationTraceCapacityThroughTermAt,
    RawTermEvaluationTraceCapacityThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_traversal,
    raw_sat_termEvaluationTraceCapacityTermAt_iff.
  tauto.
Qed.

Theorem raw_termEvaluationTraceCapacity_through_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep supportCode supportStep,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  RawTermSyntaxAssignmentAdequate M limit
    assignmentCode assignmentStep supportCode supportStep ->
  forall current,
  RawTermEvaluationTraceCapacityThrough M current limit
    assignmentCode assignmentStep supportCode supportStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep supportCode supportStep
    hsyntax hadequate.
  set (parameterEnv := scons M limit
    (scons M assignmentCode (scons M assignmentStep
      (scons M supportCode
        (scons M supportStep (fun _ : nat => raw_zero M)))))).
  set (phi := termEvaluationTraceCapacityThroughTermAt
    (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_termEvaluationTraceCapacityThroughTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5))).
      unfold parameterEnv. cbn [raw_term_eval scons]. intros _.
      exact (raw_termEvaluationTraceCapacity_zero M hPA
        assignmentCode assignmentStep supportCode supportStep).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_termEvaluationTraceCapacityThroughTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5))
        hcurrentSat) as hcurrentRaw.
      apply (proj2
        (raw_sat_termEvaluationTraceCapacityThroughTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5))).
      unfold parameterEnv in hcurrentRaw |- *.
      cbn [raw_term_eval scons] in hcurrentRaw |- *.
      intro hsuccLe.
      assert (hcurrentLimit : rawLt M current limit).
      { exact (raw_lt_of_succ_le_traversal M hPA current limit hsuccLe). }
      apply (raw_termEvaluationTraceCapacity_succ M hPA
        limit assignmentCode assignmentStep supportCode supportStep current
        hsyntax hadequate hcurrentLimit).
      apply hcurrentRaw.
      exact (raw_lt_to_le M current limit hcurrentLimit).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_termEvaluationTraceCapacityThroughTermAt_iff M
      (scons M current parameterEnv)
      (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5))
    (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

(** A complete traversal exists for some coding step, without assuming a
    fixed-step capacity predicate. *)
Theorem raw_termEvaluationTraversal_exists_of_syntax : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep supportCode supportStep,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  RawTermSyntaxAssignmentAdequate M limit
    assignmentCode assignmentStep supportCode supportStep ->
  exists capacity tableStep tableCode : M,
    RawTermEvaluationCodingStep M limit capacity tableStep /\
    RawTermEvaluationTraversal M limit
      assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep supportCode supportStep
    hsyntax hadequate.
  pose proof (raw_termEvaluationTraceCapacity_through_all M hPA
    limit assignmentCode assignmentStep supportCode supportStep
    hsyntax hadequate limit) as htrace.
  specialize (htrace (raw_le_refl_traversal M hPA limit)).
  destruct htrace as [capacity hcapacity].
  destruct (raw_termEvaluationCodingStep_exists M hPA limit capacity)
    as [tableStep hcoding].
  destruct (hcapacity tableStep hcoding) as [tableCode htraversal].
  exists capacity, tableStep, tableCode. split; assumption.
Qed.

(** ------------------------------------------------------------------
    A complete traversal discharges the universal fixed-step condition. *)

Lemma raw_termEvaluationTraversal_restrict : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep target,
  RawTermEvaluationTraversal M limit
    assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep ->
  rawLt M target limit ->
  RawTermEvaluationTraversal M target
    assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep target
    [hsupport [htable hrows]] htarget.
  split.
  - intros index hindex. apply hsupport.
    exact (raw_assignment_lt_trans M hPA
      index target limit hindex htarget).
  - split.
    + intros index hindex. apply htable.
      exact (raw_assignment_lt_trans M hPA
        index target limit hindex htarget).
    + intros code hcode hsupported. apply hrows; [|exact hsupported].
      exact (raw_assignment_lt_trans M hPA
        code target limit hcode htarget).
Qed.

Lemma raw_codedAssignmentLookup_lt_betaModulus : forall
    (M : RawPAModel) code step index value,
  RawCodedAssignmentLookup M code step index value ->
  rawLt M value (rawBetaModulus M step index).
Proof.
  intros M code step index value hlookup.
  unfold RawCodedAssignmentLookup, RawBetaEntry in hlookup.
  destruct hlookup as [modulus [hmod [quotient [hbound hcode]]]].
  unfold rawBetaModulus. rewrite <- hmod. exact hbound.
Qed.

Theorem raw_termEvaluationFixedStepCapacity_of_complete_traversal : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep,
  RawCommonMultipleThrough M limit tableStep ->
  RawTermEvaluationTraversal M limit
    assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep ->
  RawTermEvaluationFixedStepCapacity M limit
    assignmentCode assignmentStep supportCode supportStep tableStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep hcommon hcomplete.
  split; [exact hcommon |].
  intros target otherTableCode value htarget hpartial
    htargetSupport hvalueStep.
  pose proof (raw_termEvaluationTraversal_restrict M hPA
    limit assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep target hcomplete htarget)
    as hrestricted.
  pose proof (raw_termEvaluationTraversals_agree_below M hPA
    target assignmentCode assignmentStep
    otherTableCode tableStep supportCode supportStep
    tableCode tableStep supportCode supportStep
    hpartial hrestricted) as hagree.
  destruct hcomplete as [_ [_ hrows]].
  destruct (hrows target htarget htargetSupport)
    as [canonical [hcanonicalLookup hcanonicalStep]].
  assert (hvalue : value = canonical).
  {
    exact (raw_termEvaluationClosedStep_extensional M hPA
      assignmentCode assignmentStep
      otherTableCode tableStep supportCode supportStep
      tableCode tableStep supportCode supportStep
      target value canonical hagree hvalueStep hcanonicalStep).
  }
  rewrite hvalue.
  exact (raw_codedAssignmentLookup_lt_betaModulus M
    tableCode tableStep target canonical hcanonicalLookup).
Qed.

(** Main capacity theorem: syntax closure plus assignment adequacy entails
    the formerly conditional realization premise. *)
Theorem raw_termEvaluationRealizationCapacity_of_syntax : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep supportCode supportStep,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  RawTermSyntaxAssignmentAdequate M limit
    assignmentCode assignmentStep supportCode supportStep ->
  RawTermEvaluationRealizationCapacity M limit
    assignmentCode assignmentStep supportCode supportStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep supportCode supportStep
    hsyntax hadequate.
  destruct (raw_termEvaluationTraversal_exists_of_syntax M hPA
    limit assignmentCode assignmentStep supportCode supportStep
    hsyntax hadequate) as
    [capacity [tableStep [tableCode [hcoding htraversal]]]].
  exists tableStep.
  exact (raw_termEvaluationFixedStepCapacity_of_complete_traversal M hPA
    limit assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep (proj1 hcoding) htraversal).
Qed.

Corollary raw_termEvaluationRealizationCapacity_of_certificate : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep supportCode supportStep,
  RawTermSyntaxCertificateWithSupport M
    root assignmentCode assignmentStep supportCode supportStep ->
  RawTermEvaluationRealizationCapacity M (raw_succ M root)
    assignmentCode assignmentStep supportCode supportStep.
Proof.
  intros M hPA root assignmentCode assignmentStep supportCode supportStep
    [hsyntax [hadequate hroot]].
  exact (raw_termEvaluationRealizationCapacity_of_syntax M hPA
    (raw_succ M root) assignmentCode assignmentStep
    supportCode supportStep hsyntax hadequate).
Qed.

(** The previously conditional realization theorem is now unconditional on
    the honest syntax domain, with uniqueness inherited from the independent
    cross-certificate theorem. *)
Corollary raw_termEvaluationCertificate_exists_of_syntax : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep supportCode supportStep,
  RawTermSyntaxCertificateWithSupport M
    root assignmentCode assignmentStep supportCode supportStep ->
  exists value : M,
    RawTermEvaluationCertificate M
      root value assignmentCode assignmentStep.
Proof.
  intros M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax.
  apply (raw_termEvaluationCertificate_exists_of_syntax_capacity M hPA
    root assignmentCode assignmentStep supportCode supportStep hsyntax).
  exact (raw_termEvaluationRealizationCapacity_of_certificate M hPA
    root assignmentCode assignmentStep supportCode supportStep hsyntax).
Qed.

Corollary raw_termEvaluationCertificate_exists_unique_of_syntax : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep supportCode supportStep,
  RawTermSyntaxCertificateWithSupport M
    root assignmentCode assignmentStep supportCode supportStep ->
  exists value : M,
    RawTermEvaluationCertificate M
      root value assignmentCode assignmentStep /\
    forall otherValue,
      RawTermEvaluationCertificate M
        root otherValue assignmentCode assignmentStep ->
      value = otherValue.
Proof.
  intros M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax.
  destruct (raw_termEvaluationCertificate_exists_of_syntax M hPA
    root assignmentCode assignmentStep supportCode supportStep hsyntax)
    as [value hvalue].
  exists value. split; [exact hvalue |].
  intros otherValue hother.
  exact (raw_termEvaluationCertificate_value_functional M hPA
    root assignmentCode assignmentStep value otherValue hvalue hother).
Qed.

End PABoundedRawCodedTermEvaluationCapacity.
