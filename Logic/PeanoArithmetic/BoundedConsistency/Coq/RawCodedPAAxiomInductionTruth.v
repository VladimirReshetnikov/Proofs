(**
  Truth of arbitrary model-internal PA induction instances.

  There are two independent nonstandard inductions in this proof.  First,
  [RawCodedUniversalClosure] may add a nonstandard number of universal
  binders.  Second, the semantic induction axiom itself ranges over every
  (possibly nonstandard) element of the ambient PA model.  Both inductions
  below are applications of PA's object-language [raw_definable_induction];
  neither recurses in Rocq over a decoded carrier element.
*)

From Stdlib Require Import Arith Lia Classical ClassicalEpsilon.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedAssignmentUniversalDefinedness RawCodedProofDescent
  PolynomialPairInjectivity RawCodedTermEvaluationTraversal
  RawCodedTermEvaluationStandardAdequacy
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFixedLevelTruthSchedule
  RawCodedFixedLevelTruthQuantifierConstruction
  RawCodedFixedLevelTruthLaws RawCodedFixedLevelTruthOperationTransport
  RawCodedFixedLevelTruthOperationTarski
  RawCodedFixedLevelTruthOperationTarskiPositive
  RawCodedPAAxiomWitness RawCodedPAAxiomTruth.

Module PABoundedRawCodedPAAxiomInductionTruth.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentUniversalDefinedness.
Import PABoundedRawCodedProofDescent.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationStandardAdequacy.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFixedLevelTruthSchedule.
Import PABoundedRawCodedFixedLevelTruthQuantifierConstruction.
Import PABoundedRawCodedFixedLevelTruthLaws.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.
Import PABoundedRawCodedFixedLevelTruthOperationTarski.
Import PABoundedRawCodedFixedLevelTruthOperationTarskiPositive.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomTruth.

(** If every represented binder instance of a universal's child is true,
    then the universal is true.  The fixed-level constructor is formulated
    as absence of a lower Pi counterexample; admissible coherence raises any
    alleged lower counterexample and exclusivity contradicts the supplied
    same-level Sigma certificate. *)
Lemma raw_fixedLevelAll_sigma_of_all_binders : forall
    (M : RawPAModel), RawPASatisfies M -> forall level child
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    (rawFormulaAllCode M child) assignmentCode assignmentStep ->
  (forall witness newAssignmentCode newAssignmentStep,
    RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
      (rawFormulaAllCode M child)
      newAssignmentCode newAssignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      child newAssignmentCode newAssignmentStep) ->
  RawFixedLevelSigmaTruthCertificate M (S level)
    (rawFormulaAllCode M child) assignmentCode assignmentStep.
Proof.
  intros M hPA level child assignmentCode assignmentStep
    hadmissible hall.
  apply (raw_fixedLevelAll_sigma_of_no_lower_pi M hPA level child
    assignmentCode assignmentStep).
  - exact (proj1 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
      level (rawFormulaAllCode M child)
      assignmentCode assignmentStep hadmissible)).
  - intros (witness & newAssignmentCode & newAssignmentStep &
      hprepend & hlowerPi).
    destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
      level child assignmentCode assignmentStep witness
      newAssignmentCode newAssignmentStep hadmissible hprepend)
      as [hchildAtomic [hchildDefined hchildPiDomain]].
    assert (hchildAdmissible : RawFixedLevelTruthAdmissible M level child
        newAssignmentCode newAssignmentStep).
    { repeat split; try assumption. now right. }
    pose proof (raw_fixedLevelAdmissibleTruthCertificateCoherence_all
      level M hPA) as hcoherence.
    pose proof (proj2 (hcoherence child newAssignmentCode newAssignmentStep
      hchildAdmissible) hchildPiDomain) as hpiIff.
    exact (raw_fixedLevelAdmissibleTruthCertificate_exclusive level M hPA
      child newAssignmentCode newAssignmentStep hchildAdmissible
      (hall witness newAssignmentCode newAssignmentStep hprepend)
      (proj1 hpiIff hlowerPi)).
Qed.

(** A weak inequality followed by a strict one is strict.  The surrounding
    assignment API exposes the opposite mixed transitivity direction; this
    elementary companion is useful when a unit shift turns [i < source]
    into [S i <= source]. *)
Lemma raw_inductionTruth_le_lt_trans : forall
    (M : RawPAModel), RawPASatisfies M -> forall left middle right,
  rawLe M left middle -> rawLt M middle right -> rawLt M left right.
Proof.
  intros M hPA left middle right [leftGap hleft] [rightGap hright].
  exists (raw_add M leftGap rightGap).
  rewrite raw_add_succ by exact hPA.
  rewrite <- raw_add_assoc by exact hPA.
  rewrite hleft.
  rewrite <- raw_add_succ by exact hPA.
  exact hright.
Qed.

(** A unit shift above the innermost binder cannot leave the enclosing
    universal formula's code bound.  This small bound fact lets the local
    operation invariant recover the stronger global assignment graph. *)
Lemma raw_inductionTruth_unitShift_output_lt_parent : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      input output source parent,
  rawLt M input source ->
  rawLt M source parent ->
  RawShiftedIndex M (rawNumeralValue M 1) (rawNumeralValue M 1)
    input output ->
  rawLt M output parent.
Proof.
  intros M hPA input output source parent hinput hsource hshift.
  destruct hshift as [[_ ->] | [_ ->]].
  - exact (raw_assignment_lt_trans M hPA input source parent
      hinput hsource).
  - change (rawLt M
      (raw_add M input (raw_succ M (raw_zero M))) parent).
    rewrite raw_add_succ by exact hPA.
    rewrite raw_add_zero_right_operationTransport by exact hPA.
    exact (raw_inductionTruth_le_lt_trans M hPA
      (raw_succ M input) source parent
      (raw_succ_le_of_lt_pair M hPA input source hinput) hsource).
Qed.

(** The successor induction instance uses three related environments:

      C = (S x) :: A,   B = x :: A,   D = (S x) :: B.

    Shifting [source] above its first binder by one therefore transports it
    from [C] to [D].  The beta prepend certificates for [B] and [D] may be
    chosen at larger bounds than the independently supplied certificate for
    [C].  Universal assignment definedness and restriction make those
    choices compatible without decoding any model-internal formula. *)
Theorem raw_inductionTruth_unitShift_nested_prepend_relation : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      source parent targetParent head shiftedHead
      assignmentCode assignmentStep
      middleCode middleStep sourceChildCode sourceChildStep
      targetChildCode targetChildStep,
  rawLt M source parent ->
  rawLt M parent targetParent ->
  RawCodedAssignmentPrepend M
    assignmentCode assignmentStep head parent middleCode middleStep ->
  RawCodedAssignmentPrepend M
    assignmentCode assignmentStep shiftedHead parent
    sourceChildCode sourceChildStep ->
  RawCodedAssignmentPrepend M
    middleCode middleStep shiftedHead targetParent
    targetChildCode targetChildStep ->
  RawCodedFormulaShiftAssignmentRelation M
    (rawNumeralValue M 1) (rawNumeralValue M 1) source
    sourceChildCode sourceChildStep targetChildCode targetChildStep.
Proof.
  intros M hPA source parent targetParent head shiftedHead
    assignmentCode assignmentStep middleCode middleStep
    sourceChildCode sourceChildStep targetChildCode targetChildStep
    hsource hparent hmiddle hsourceChild htargetChild.
  pose proof (raw_codedFormulaUnitShiftAssignmentRelation_of_prepend
    M hPA parent assignmentCode assignmentStep head middleCode middleStep
    (raw_codedAssignment_definedThrough_all M hPA
      assignmentCode assignmentStep parent) hmiddle) as hrootRelation.
  pose proof (raw_codedFormulaShiftAssignmentRelation_local M hPA
    (raw_zero M) (rawNumeralValue M 1) parent targetParent
    assignmentCode assignmentStep middleCode middleStep hrootRelation)
    as hrootLocal.
  pose proof (raw_codedFormulaShiftAssignmentLocalCompatibility_prepend
    M hPA (raw_zero M) (rawNumeralValue M 1)
    parent targetParent source parent shiftedHead
    assignmentCode assignmentStep middleCode middleStep
    sourceChildCode sourceChildStep targetChildCode targetChildStep
    hrootLocal
    (raw_codedAssignment_definedThrough_all M hPA
      assignmentCode assignmentStep parent)
    (raw_codedAssignment_definedThrough_all M hPA
      middleCode middleStep targetParent)
    hsourceChild htargetChild hsource
    hparent) as hlocal.
  change (RawCodedFormulaShiftAssignmentLocalCompatibility M
    (rawNumeralValue M 1) (rawNumeralValue M 1) source parent
    sourceChildCode sourceChildStep targetChildCode targetChildStep)
    in hlocal.
  intros input output value hinput hshift. split.
  - intro hsourceLookup.
    destruct (raw_codedAssignmentLookup_exists_all M hPA
      targetChildCode targetChildStep output) as [targetValue htargetLookup].
    assert (houtput : rawLt M output parent).
    { exact (raw_inductionTruth_unitShift_output_lt_parent M hPA
        input output source parent hinput hsource hshift). }
    pose proof (hlocal input output value targetValue
      hinput houtput hshift hsourceLookup htargetLookup) as ->.
    exact htargetLookup.
  - intro htargetLookup.
    destruct (raw_codedAssignmentLookup_exists_all M hPA
      sourceChildCode sourceChildStep input) as [sourceValue hsourceLookup].
    assert (houtput : rawLt M output parent).
    { exact (raw_inductionTruth_unitShift_output_lt_parent M hPA
        input output source parent hinput hsource hshift). }
    pose proof (hlocal input output sourceValue value
      hinput houtput hshift hsourceLookup htargetLookup) as <-.
    exact hsourceLookup.
Qed.

(** Standard replacement terms still have to be evaluated under the exact
    beta assignment used by substitution transport.  Universal lookup
    existence selects an external environment extension of that assignment;
    standard term-evaluation adequacy then builds the represented certificate
    while retaining the original assignment code and step. *)
Lemma raw_inductionTruth_standardTermEvaluation_total_assignment : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      assignmentCode assignmentStep (t : term),
  exists env : nat -> M,
    (forall index,
      RawCodedAssignmentLookup M assignmentCode assignmentStep
        (rawNumeralValue M index) (env index)) /\
    RawTermEvaluationCertificate M
      (rawNumeralValue M (termCode t)) (raw_term_eval M env t)
      assignmentCode assignmentStep.
Proof.
  intros M hPA assignmentCode assignmentStep t.
  set (env := fun index : nat =>
    proj1_sig (constructive_indefinite_description
      (fun value : M =>
        RawCodedAssignmentLookup M assignmentCode assignmentStep
          (rawNumeralValue M index) value)
      (raw_codedAssignmentLookup_exists_all M hPA
        assignmentCode assignmentStep (rawNumeralValue M index)))).
  assert (henv : forall index,
      RawCodedAssignmentLookup M assignmentCode assignmentStep
        (rawNumeralValue M index) (env index)).
  {
    intro index. unfold env.
    destruct (constructive_indefinite_description
      (fun value : M =>
        RawCodedAssignmentLookup M assignmentCode assignmentStep
          (rawNumeralValue M index) value)
      (raw_codedAssignmentLookup_exists_all M hPA
        assignmentCode assignmentStep (rawNumeralValue M index)))
      as [value hvalue]. exact hvalue.
  }
  exists env. split; [exact henv |].
  pose proof (raw_termEvaluationCertificate_standard_of_assignment
    M hPA env (S (termCode t)) assignmentCode assignmentStep
    (fun index _ => henv index) t (Nat.lt_succ_diag_r _)) as hcertificate.
  rewrite rawQuotedTermCode_standard in hcertificate by exact hPA.
  exact hcertificate.
Qed.

Lemma raw_inductionTruth_zeroTermEvaluation : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      assignmentCode assignmentStep,
  RawTermEvaluationCertificate M
    (rawNumeralValue M (termCode tZero)) (raw_zero M)
    assignmentCode assignmentStep.
Proof.
  intros M hPA assignmentCode assignmentStep.
  destruct (raw_inductionTruth_standardTermEvaluation_total_assignment
    M hPA assignmentCode assignmentStep tZero) as [env [_ hcertificate]].
  cbn [raw_term_eval] in hcertificate. exact hcertificate.
Qed.

Lemma raw_inductionTruth_successorVariableTermEvaluation : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      assignmentCode assignmentStep value,
  RawCodedAssignmentLookup M assignmentCode assignmentStep
    (raw_zero M) value ->
  RawTermEvaluationCertificate M
    (rawNumeralValue M (termCode (tSucc (tVar 0))))
    (raw_succ M value) assignmentCode assignmentStep.
Proof.
  intros M hPA assignmentCode assignmentStep value hvalue.
  destruct (raw_inductionTruth_standardTermEvaluation_total_assignment
    M hPA assignmentCode assignmentStep (tSucc (tVar 0)))
    as [env [henv hcertificate]].
  assert (henvZero : env 0 = value).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      assignmentCode assignmentStep (raw_zero M) (env 0) value
      (henv 0) hvalue).
  }
  cbn [raw_term_eval] in hcertificate.
  now rewrite henvZero in hcertificate.
Qed.

(** ------------------------------------------------------------------
    A PA-definable invariant for a nonstandard universal-closure count. *)

Definition universalClosureSigmaSoundAtTermAt (level : nat)
    (current body : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (codedUniversalClosureTermAt
        (liftTerm 3 current) (liftTerm 3 body) (tVar 2))
      (pImp
        (fixedLevelTruthAdmissibleTermAt level
          (tVar 2) (tVar 1) (tVar 0))
        (fixedLevelSigmaTruthCertificateTermAt (S level)
          (tVar 2) (tVar 1) (tVar 0)))))).

Definition RawUniversalClosureSigmaSoundAt (M : RawPAModel)
    (level : nat) (current body : M) : Prop :=
  forall output assignmentCode assignmentStep : M,
    RawCodedUniversalClosure M current body output ->
    RawFixedLevelTruthAdmissible M level
      output assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      output assignmentCode assignmentStep.

Arguments RawUniversalClosureSigmaSoundAt M level current body
  : clear implicits.

Lemma raw_inductionTruth_eval_liftTerm_three : forall
    (M : RawPAModel) a b c (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b (scons M c e)))
    (liftTerm 3 t) = raw_term_eval M e t.
Proof.
  intros M a b c e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 3) with (S (S (S index))) by lia. reflexivity.
Qed.

Lemma raw_sat_universalClosureSigmaSoundAtTermAt_iff : forall
    (M : RawPAModel) e level current body,
  raw_formula_sat M e
    (universalClosureSigmaSoundAtTermAt level current body) <->
  RawUniversalClosureSigmaSoundAt M level
    (raw_term_eval M e current) (raw_term_eval M e body).
Proof.
  intros M e level current body.
  unfold universalClosureSigmaSoundAtTermAt,
    RawUniversalClosureSigmaSoundAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedUniversalClosureTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelTruthAdmissibleTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  repeat setoid_rewrite raw_inductionTruth_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_universalClosureSigmaSoundAt_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall level body,
  (forall assignmentCode assignmentStep,
    RawFixedLevelTruthAdmissible M level
      body assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      body assignmentCode assignmentStep) ->
  RawUniversalClosureSigmaSoundAt M level (raw_zero M) body.
Proof.
  intros M hPA level body hbody output assignmentCode assignmentStep
    hclosure hadmissible.
  pose proof (raw_codedUniversalClosure_zero M hPA
    body output hclosure) as ->.
  exact (hbody assignmentCode assignmentStep hadmissible).
Qed.

Lemma raw_universalClosureSigmaSoundAt_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall level body current,
  RawUniversalClosureSigmaSoundAt M level current body ->
  RawUniversalClosureSigmaSoundAt M level (raw_succ M current) body.
Proof.
  intros M hPA level body current hcurrent
    output assignmentCode assignmentStep hclosure hadmissible.
  destruct (raw_codedUniversalClosure_succ_inversion M hPA
    current body output hclosure) as [previous [hprevious ->]].
  apply (raw_fixedLevelAll_sigma_of_all_binders M hPA level previous
    assignmentCode assignmentStep hadmissible).
  intros witness newAssignmentCode newAssignmentStep hprepend.
  destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
    level previous assignmentCode assignmentStep witness
    newAssignmentCode newAssignmentStep hadmissible hprepend)
    as [hpreviousAtomic [hpreviousDefined hpreviousDomain]].
  apply (hcurrent previous newAssignmentCode newAssignmentStep hprevious).
  repeat split; try assumption. now right.
Qed.

(** PA induction reaches every model-internal closure count.  The hypothesis
    says that the unclosed body is valid under every assignment at which the
    fixed-level truth predicate is admissible. *)
Theorem raw_universalClosure_sigma_sound_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall level body,
  (forall assignmentCode assignmentStep,
    RawFixedLevelTruthAdmissible M level
      body assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      body assignmentCode assignmentStep) ->
  forall count output assignmentCode assignmentStep,
  RawCodedUniversalClosure M count body output ->
  RawFixedLevelTruthAdmissible M level
    output assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S level)
    output assignmentCode assignmentStep.
Proof.
  intros M hPA level body hbody.
  set (parameterEnv := scons M body (fun _ : nat => raw_zero M)).
  set (phi := universalClosureSigmaSoundAtTermAt
    level (tVar 0) (tVar 1)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_universalClosureSigmaSoundAtTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        level (tVar 0) (tVar 1))).
      cbn [raw_term_eval scons].
      apply raw_universalClosureSigmaSoundAt_zero;
        [exact hPA | exact hbody].
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_universalClosureSigmaSoundAtTermAt_iff M
          (scons M current parameterEnv)
          level (tVar 0) (tVar 1)) hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_universalClosureSigmaSoundAtTermAt_iff M
        (scons M (raw_succ M current) parameterEnv)
        level (tVar 0) (tVar 1))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_universalClosureSigmaSoundAt_succ M hPA
        level body current hcurrent).
  }
  intros count output assignmentCode assignmentStep hclosure hadmissible.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_universalClosureSigmaSoundAtTermAt_iff M
      (scons M count parameterEnv) level (tVar 0) (tVar 1))
    (hall count)) as hcount.
  cbn [raw_term_eval scons] in hcount.
  exact (hcount output assignmentCode assignmentStep
    hclosure hadmissible).
Qed.

(** ------------------------------------------------------------------
    The semantic induction invariant for the nonstandard source formula.

    At stage [current], every beta prepend of the ambient assignment by that
    value (through the displayed universal source formula) makes [source]
    Sigma-true.  Quantifying over *all* prepend tables is essential: the
    induction step constructs auxiliary tables through larger formula bounds,
    while universal-introduction later presents an independently chosen table.
*)

Definition inductionSourceProgressAtTermAt (level : nat)
    (current source sourceAll assignmentCode assignmentStep : term)
    : formula :=
  pAll (pAll
    (pImp
      (codedAssignmentPrependTermAt
        (liftTerm 2 assignmentCode) (liftTerm 2 assignmentStep)
        (liftTerm 2 current) (liftTerm 2 sourceAll)
        (tVar 1) (tVar 0))
      (fixedLevelSigmaTruthCertificateTermAt (S level)
        (liftTerm 2 source) (tVar 1) (tVar 0)))).

Definition RawInductionSourceProgressAt (M : RawPAModel)
    (level : nat)
    (current source sourceAll assignmentCode assignmentStep : M) : Prop :=
  forall newAssignmentCode newAssignmentStep : M,
    RawCodedAssignmentPrepend M assignmentCode assignmentStep current
      sourceAll newAssignmentCode newAssignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S level)
      source newAssignmentCode newAssignmentStep.

Arguments RawInductionSourceProgressAt
  M level current source sourceAll assignmentCode assignmentStep
  : clear implicits.

Lemma raw_inductionTruth_eval_liftTerm_two : forall
    (M : RawPAModel) a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e))
    (liftTerm 2 t) = raw_term_eval M e t.
Proof.
  intros M a b e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 2) with (S (S index)) by lia. reflexivity.
Qed.

Lemma raw_sat_inductionSourceProgressAtTermAt_iff : forall
    (M : RawPAModel) e level current source sourceAll
      assignmentCode assignmentStep,
  raw_formula_sat M e
    (inductionSourceProgressAtTermAt level current source sourceAll
      assignmentCode assignmentStep) <->
  RawInductionSourceProgressAt M level
    (raw_term_eval M e current)
    (raw_term_eval M e source) (raw_term_eval M e sourceAll)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intros M e level current source sourceAll assignmentCode assignmentStep.
  unfold inductionSourceProgressAtTermAt, RawInductionSourceProgressAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedAssignmentPrependTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  repeat setoid_rewrite raw_inductionTruth_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** This theorem is intentionally parameterized by the local zero and
    successor arguments.  Those arguments are the only place where coded
    shift/substitution Tarski transport is needed; the passage through every
    nonstandard model element is PA's own definable induction. *)
Theorem raw_inductionSourceProgressAt_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall level
      source sourceAll assignmentCode assignmentStep,
  RawInductionSourceProgressAt M level (raw_zero M)
    source sourceAll assignmentCode assignmentStep ->
  (forall current,
    RawInductionSourceProgressAt M level current
      source sourceAll assignmentCode assignmentStep ->
    RawInductionSourceProgressAt M level (raw_succ M current)
      source sourceAll assignmentCode assignmentStep) ->
  forall current,
    RawInductionSourceProgressAt M level current
      source sourceAll assignmentCode assignmentStep.
Proof.
  intros M hPA level source sourceAll assignmentCode assignmentStep
    hzero hsucc.
  set (parameterEnv := scons M source
    (scons M sourceAll
      (scons M assignmentCode
        (scons M assignmentStep (fun _ : nat => raw_zero M))))).
  set (phi := inductionSourceProgressAtTermAt level
    (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_inductionSourceProgressAtTermAt_iff M
        (scons M (raw_zero M) parameterEnv) level
        (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4))).
      cbn [raw_term_eval scons]. exact hzero.
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_inductionSourceProgressAtTermAt_iff M
          (scons M current parameterEnv) level
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_inductionSourceProgressAtTermAt_iff M
        (scons M (raw_succ M current) parameterEnv) level
        (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (hsucc current hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_inductionSourceProgressAtTermAt_iff M
      (scons M current parameterEnv) level
      (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4))
    (hall current)) as hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

(** The purely logical assembly of the induction body.  Operation Tarski is
    confined to the two callback hypotheses: zero substitution establishes
    the base progress certificate, and successor shift/substitution preserves
    it.  Everything else is fixed-level propositional/quantifier reasoning. *)
Theorem raw_inductionBody_sigma_of_progress : forall
    (M : RawPAModel), RawPASatisfies M -> forall level
      source zeroInstance stepAll premise sourceAll body
      assignmentCode assignmentStep,
  body = rawFormulaImpCode M premise sourceAll ->
  premise = rawFormulaAndCode M zeroInstance stepAll ->
  sourceAll = rawFormulaAllCode M source ->
  RawFixedLevelTruthAdmissible M level
    body assignmentCode assignmentStep ->
  (RawFixedLevelSigmaTruthCertificate M (S level)
      zeroInstance assignmentCode assignmentStep ->
    RawInductionSourceProgressAt M level (raw_zero M)
      source sourceAll assignmentCode assignmentStep) ->
  (RawFixedLevelSigmaTruthCertificate M (S level)
      stepAll assignmentCode assignmentStep ->
    forall current,
      RawInductionSourceProgressAt M level current
        source sourceAll assignmentCode assignmentStep ->
      RawInductionSourceProgressAt M level (raw_succ M current)
        source sourceAll assignmentCode assignmentStep) ->
  RawFixedLevelSigmaTruthCertificate M (S level)
    body assignmentCode assignmentStep.
Proof.
  intros M hPA level source zeroInstance stepAll premise sourceAll body
    assignmentCode assignmentStep -> -> -> hadmissible hzeroStep hsuccStep.
  destruct (raw_fixedLevelTruthAdmissible_imp_children M hPA level
    (rawFormulaAndCode M zeroInstance stepAll)
    (rawFormulaAllCode M source)
    assignmentCode assignmentStep hadmissible)
    as [hpremiseAdmissible hsourceAllAdmissible].
  apply (proj2 (raw_fixedLevelImp_sigma_iff M hPA level
    (rawFormulaAndCode M zeroInstance stepAll)
    (rawFormulaAllCode M source)
    assignmentCode assignmentStep hadmissible)).
  destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
    level M hPA (rawFormulaAndCode M zeroInstance stepAll)
    assignmentCode assignmentStep hpremiseAdmissible)
    as [hpremiseSigma | hpremisePi].
  - right.
    destruct (raw_fixedLevelAnd_sigma_elim M hPA level
      zeroInstance stepAll assignmentCode assignmentStep
      hpremiseAdmissible hpremiseSigma) as [hzeroSigma hstepAllSigma].
    apply (raw_fixedLevelAll_sigma_of_all_binders M hPA level source
      assignmentCode assignmentStep hsourceAllAdmissible).
    intros current newAssignmentCode newAssignmentStep hprepend.
    exact (raw_inductionSourceProgressAt_all M hPA level
      source (rawFormulaAllCode M source) assignmentCode assignmentStep
      (hzeroStep hzeroSigma) (hsuccStep hstepAllSigma)
      current newAssignmentCode newAssignmentStep hprepend).
  - now left.
Qed.

(** Operation Tarski at certificate level [S level] asks for admissibility
    at that same level.  An admissible formula at [level] has both successor
    domains, while atomic adequacy and assignment definedness are unchanged. *)
Lemma raw_inductionTruth_admissible_successor : forall
    (M : RawPAModel), RawPASatisfies M -> forall level formulaCode
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    formulaCode assignmentCode assignmentStep ->
  RawFixedLevelTruthAdmissible M (S level)
    formulaCode assignmentCode assignmentStep.
Proof.
  intros M hPA level formulaCode assignmentCode assignmentStep
    [hatomic [hassignment hdomain]].
  split; [exact hatomic |]. split; [exact hassignment |].
  left. exact (proj1 (raw_fixedLevel_rank_bound_both_at_successor
    M hPA level formulaCode hdomain)).
Qed.

Lemma raw_inductionTruth_targetData_of_admissible : forall
    (M : RawPAModel) level formulaCode assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    formulaCode assignmentCode assignmentStep ->
  RawCodedFormulaTargetAdmissibilityData M
    formulaCode assignmentCode assignmentStep.
Proof.
  intros M level formulaCode assignmentCode assignmentStep
    [hatomic [hassignment _]].
  exact (conj hatomic hassignment).
Qed.

(** The final narrow operation boundary.  Unlike the earlier context-level
    placeholder, this predicate says only that the two concrete substitution
    traces and the one concrete shift trace establish the zero/successor
    progress callbacks.  Its proof is entirely operation Tarski plus beta
    assignment bookkeeping; all logical induction and universal closure have
    already been discharged above. *)
Definition RawFixedLevelInductionProgressTransport (M : RawPAModel)
    (level : nat)
    (source shifted successorInstance zeroInstance sourceAll stepAll body : M)
    : Prop :=
  RawCodedFormulaShift M
      (rawNumeralValue M 1) (rawNumeralValue M 1)
      source shifted ->
  RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M (termCode (tSucc (tVar 0))))
      shifted successorInstance ->
  RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M (termCode tZero)) source zeroInstance ->
  forall assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
      body assignmentCode assignmentStep ->
  (RawFixedLevelSigmaTruthCertificate M (S level)
      zeroInstance assignmentCode assignmentStep ->
    RawInductionSourceProgressAt M level (raw_zero M)
      source sourceAll assignmentCode assignmentStep) /\
  (RawFixedLevelSigmaTruthCertificate M (S level)
      stepAll assignmentCode assignmentStep ->
    forall current,
      RawInductionSourceProgressAt M level current
        source sourceAll assignmentCode assignmentStep ->
      RawInductionSourceProgressAt M level (raw_succ M current)
        source sourceAll assignmentCode assignmentStep).

Arguments RawFixedLevelInductionProgressTransport
  M level source shifted successorInstance zeroInstance sourceAll stepAll body
  : clear implicits.

Definition RawFixedLevelInductionProgressTransportAll
    (M : RawPAModel) (level : nat) : Prop :=
  forall source shifted successorInstance zeroInstance
      sourceAll stepImp stepAll premise body : M,
    sourceAll = rawFormulaAllCode M source ->
    stepImp = rawFormulaImpCode M source successorInstance ->
    stepAll = rawFormulaAllCode M stepImp ->
    premise = rawFormulaAndCode M zeroInstance stepAll ->
    body = rawFormulaImpCode M premise sourceAll ->
    RawFixedLevelInductionProgressTransport M level
      source shifted successorInstance zeroInstance sourceAll stepAll body.

Arguments RawFixedLevelInductionProgressTransportAll M level
  : clear implicits.

(** All beta bookkeeping and logical reasoning for the final callbacks.  The
    five hypotheses are precisely the operation-generic facts proved by the
    shift/substitution Tarski development: rank preservation, atomic syntax
    transport for the intermediate shifted formula, and the two same-level
    certificate laws. *)
Theorem raw_fixedLevelInductionProgressTransport_of_operation_facts : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawCodedFormulaShiftRankPreserving M ->
  RawCodedFormulaSingleSubstitutionRankPreserving M ->
  (forall cutoff amount input output,
    RawCodedFormulaShift M cutoff amount input output ->
    RawCodedFormulaAtomicallyAdequate M input ->
    RawCodedFormulaAtomicallyAdequate M output) ->
  (forall cutoff amount input output
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
    RawFixedLevelFormulaShiftTarskiStep M (S level)
      cutoff amount input output
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) ->
  (forall replacement input output
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
    RawFixedLevelFormulaSubstitutionTarskiStep M (S level)
      replacement input output
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) ->
  RawFixedLevelInductionProgressTransportAll M level.
Proof.
  intros M hPA level hshiftRank hsubstitutionRank hshiftAtomic
    hshiftTarski hsubstitutionTarski
    source shifted successorInstance zeroInstance
    sourceAll stepImp stepAll premise body
    -> -> -> -> ->
    hshift hsuccessorSubstitution hzeroSubstitution
    assignmentCode assignmentStep hbodyAdmissible.
  destruct (raw_fixedLevelTruthAdmissible_imp_children M hPA level
    (rawFormulaAndCode M zeroInstance
      (rawFormulaAllCode M
        (rawFormulaImpCode M source successorInstance)))
    (rawFormulaAllCode M source)
    assignmentCode assignmentStep hbodyAdmissible)
    as [hpremiseAdmissible hsourceAllAdmissible].
  destruct (raw_fixedLevelTruthAdmissible_and_children M hPA level
    zeroInstance
    (rawFormulaAllCode M (rawFormulaImpCode M source successorInstance))
    assignmentCode assignmentStep hpremiseAdmissible)
    as [hzeroAdmissible hstepAllAdmissible].
  split.
  - intro hzeroSigma.
    intros sourceAssignmentCode sourceAssignmentStep hsourcePrepend.
    destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
      level source assignmentCode assignmentStep (raw_zero M)
      sourceAssignmentCode sourceAssignmentStep
      hsourceAllAdmissible hsourcePrepend)
      as [hsourceAtomic [hsourceDefined hsourceDomain]].
    assert (hsourceAdmissible : RawFixedLevelTruthAdmissible M level
        source sourceAssignmentCode sourceAssignmentStep).
    { repeat split; try assumption. now right. }
    assert (hsubstitutionAssignments :
        RawCodedFormulaSubstitutionAssignmentRelation M
          (rawNumeralValue M (termCode tZero)) source
          sourceAssignmentCode sourceAssignmentStep
          assignmentCode assignmentStep).
    {
      exists (raw_zero M). split.
      - exact (raw_inductionTruth_zeroTermEvaluation M hPA
          assignmentCode assignmentStep).
      - exact (raw_codedAssignmentPrepend_restrict M hPA
          assignmentCode assignmentStep (raw_zero M)
          source (rawFormulaAllCode M source)
          sourceAssignmentCode sourceAssignmentStep
          (raw_formulaCodeList2_child_lt M hPA
            (rawNumeralValue M 5) source)
          hsourcePrepend).
    }
    assert (hready : RawFixedLevelFormulaSubstitutionTransportReady M
        (S level) (rawNumeralValue M (termCode tZero))
        source zeroInstance
        sourceAssignmentCode sourceAssignmentStep
        assignmentCode assignmentStep).
    {
      apply (raw_fixedLevelFormulaSubstitutionTransportReady_of_rankPreservation
        M hsubstitutionRank (S level)
        (rawNumeralValue M (termCode tZero)) source zeroInstance
        sourceAssignmentCode sourceAssignmentStep
        assignmentCode assignmentStep).
      - exact hzeroSubstitution.
      - exact hsubstitutionAssignments.
      - exact (raw_inductionTruth_admissible_successor M hPA level
          source sourceAssignmentCode sourceAssignmentStep
          hsourceAdmissible).
      - exact (raw_inductionTruth_targetData_of_admissible M level
          zeroInstance assignmentCode assignmentStep hzeroAdmissible).
    }
    pose proof (hsubstitutionTarski
      (rawNumeralValue M (termCode tZero)) source zeroInstance
      sourceAssignmentCode sourceAssignmentStep
      assignmentCode assignmentStep hready) as htransport.
    exact (proj2 (proj1 htransport) hzeroSigma).
  - intro hstepAllSigma.
    intros current hcurrent
      sourceAssignmentCode sourceAssignmentStep hsourcePrepend.
    set (middleBound := raw_succ M
      (raw_add M (rawFormulaAllCode M source)
        (rawFormulaAllCode M
          (rawFormulaImpCode M source successorInstance)))).
    assert (hsourceAllMiddle : rawLt M (rawFormulaAllCode M source)
        middleBound).
    {
      unfold middleBound. apply raw_lt_succ_of_le; [exact hPA |].
      apply raw_proof_left_le_sum.
    }
    assert (hstepAllMiddle :
        rawLt M
          (rawFormulaAllCode M
            (rawFormulaImpCode M source successorInstance)) middleBound).
    {
      unfold middleBound. apply raw_lt_succ_of_le; [exact hPA |].
      apply raw_proof_right_le_sum. exact hPA.
    }
    destruct (raw_codedAssignmentPrepend_exists M hPA
      assignmentCode assignmentStep current middleBound)
      as [middleCode [middleStep hmiddleLarge]].
    pose proof (raw_codedAssignmentPrepend_restrict M hPA
      assignmentCode assignmentStep current
      (rawFormulaAllCode M source) middleBound middleCode middleStep
      hsourceAllMiddle hmiddleLarge) as hmiddleSource.
    pose proof (raw_codedAssignmentPrepend_restrict M hPA
      assignmentCode assignmentStep current
      (rawFormulaAllCode M
        (rawFormulaImpCode M source successorInstance))
      middleBound middleCode middleStep
      hstepAllMiddle hmiddleLarge) as hmiddleStep.
    pose proof (hcurrent middleCode middleStep hmiddleSource)
      as hsourceSigma.
    pose proof (raw_fixedLevelAll_sigma_instantiate M hPA level
      (rawFormulaImpCode M source successorInstance)
      assignmentCode assignmentStep current middleCode middleStep
      hstepAllAdmissible hstepAllSigma hmiddleStep) as hstepImpSigma.
    destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
      level (rawFormulaImpCode M source successorInstance)
      assignmentCode assignmentStep current middleCode middleStep
      hstepAllAdmissible hmiddleStep)
      as [hstepImpAtomic [hstepImpDefined hstepImpDomain]].
    assert (hstepImpAdmissible : RawFixedLevelTruthAdmissible M level
        (rawFormulaImpCode M source successorInstance)
        middleCode middleStep).
    { repeat split; try assumption. now right. }
    destruct (raw_fixedLevelTruthAdmissible_imp_children M hPA level
      source successorInstance middleCode middleStep hstepImpAdmissible)
      as [hsourceMiddleAdmissible hsuccessorAdmissible].
    pose proof (raw_fixedLevelImp_sigma_modus_ponens M hPA level
      source successorInstance middleCode middleStep
      hstepImpAdmissible hstepImpSigma hsourceSigma)
      as hsuccessorSigma.
    set (targetBound := raw_succ M
      (raw_add M (rawFormulaAllCode M source) shifted)).
    assert (hsourceAllTarget : rawLt M (rawFormulaAllCode M source)
        targetBound).
    {
      unfold targetBound. apply raw_lt_succ_of_le; [exact hPA |].
      apply raw_proof_left_le_sum.
    }
    assert (hshiftedTarget : rawLt M shifted targetBound).
    {
      unfold targetBound. apply raw_lt_succ_of_le; [exact hPA |].
      apply raw_proof_right_le_sum. exact hPA.
    }
    destruct (raw_codedAssignmentPrepend_exists M hPA
      middleCode middleStep (raw_succ M current) targetBound)
      as [shiftedCode [shiftedStep hshiftedLarge]].
    pose proof (raw_codedAssignmentPrepend_restrict M hPA
      middleCode middleStep (raw_succ M current)
      shifted targetBound shiftedCode shiftedStep
      hshiftedTarget hshiftedLarge) as hshiftedPrepend.
    assert (hshiftAssignments : RawCodedFormulaShiftAssignmentRelation M
        (rawNumeralValue M 1) (rawNumeralValue M 1) source
        sourceAssignmentCode sourceAssignmentStep shiftedCode shiftedStep).
    {
      exact (raw_inductionTruth_unitShift_nested_prepend_relation M hPA
        source (rawFormulaAllCode M source) targetBound current
        (raw_succ M current) assignmentCode assignmentStep
        middleCode middleStep sourceAssignmentCode sourceAssignmentStep
        shiftedCode shiftedStep
        (raw_formulaCodeList2_child_lt M hPA
          (rawNumeralValue M 5) source)
        hsourceAllTarget hmiddleSource hsourcePrepend hshiftedLarge).
    }
    destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
      level source assignmentCode assignmentStep (raw_succ M current)
      sourceAssignmentCode sourceAssignmentStep
      hsourceAllAdmissible hsourcePrepend)
      as [hsourceChildAtomic [hsourceChildDefined hsourceChildDomain]].
    assert (hsourceChildAdmissible : RawFixedLevelTruthAdmissible M level
        source sourceAssignmentCode sourceAssignmentStep).
    { repeat split; try assumption. now right. }
    assert (hshiftReady : RawFixedLevelFormulaShiftTransportReady M
        (S level) (rawNumeralValue M 1) (rawNumeralValue M 1)
        source shifted sourceAssignmentCode sourceAssignmentStep
        shiftedCode shiftedStep).
    {
      apply (raw_fixedLevelFormulaShiftTransportReady_of_rankPreservation
        M hshiftRank (S level)
        (rawNumeralValue M 1) (rawNumeralValue M 1) source shifted
        sourceAssignmentCode sourceAssignmentStep shiftedCode shiftedStep).
      - exact hshift.
      - exact hshiftAssignments.
      - exact (raw_inductionTruth_admissible_successor M hPA level
          source sourceAssignmentCode sourceAssignmentStep
          hsourceChildAdmissible).
      - split.
        + exact (hshiftAtomic
            (rawNumeralValue M 1) (rawNumeralValue M 1)
            source shifted hshift hsourceChildAtomic).
        + exact (raw_codedAssignment_definedThrough_all M hPA
            shiftedCode shiftedStep shifted).
    }
    pose proof (raw_fixedLevelFormulaShiftTransportReady_target_admissible
      M hPA (S level)
      (rawNumeralValue M 1) (rawNumeralValue M 1) source shifted
      sourceAssignmentCode sourceAssignmentStep shiftedCode shiftedStep
      hshiftReady) as hshiftedAdmissible.
    assert (hsubstitutionAssignments :
        RawCodedFormulaSubstitutionAssignmentRelation M
          (rawNumeralValue M (termCode (tSucc (tVar 0)))) shifted
          shiftedCode shiftedStep middleCode middleStep).
    {
      exists (raw_succ M current). split.
      - apply (raw_inductionTruth_successorVariableTermEvaluation M hPA
          middleCode middleStep current).
        exact (raw_codedAssignmentPrepend_head M
          assignmentCode assignmentStep current
          (rawFormulaAllCode M source) middleCode middleStep
          hmiddleSource).
      - exact hshiftedPrepend.
    }
    assert (hsubstitutionReady :
        RawFixedLevelFormulaSubstitutionTransportReady M (S level)
          (rawNumeralValue M (termCode (tSucc (tVar 0))))
          shifted successorInstance shiftedCode shiftedStep
          middleCode middleStep).
    {
      apply (raw_fixedLevelFormulaSubstitutionTransportReady_of_rankPreservation
        M hsubstitutionRank (S level)
        (rawNumeralValue M (termCode (tSucc (tVar 0))))
        shifted successorInstance shiftedCode shiftedStep
        middleCode middleStep).
      - exact hsuccessorSubstitution.
      - exact hsubstitutionAssignments.
      - exact hshiftedAdmissible.
      - exact (raw_inductionTruth_targetData_of_admissible M level
          successorInstance middleCode middleStep hsuccessorAdmissible).
    }
    pose proof (hsubstitutionTarski
      (rawNumeralValue M (termCode (tSucc (tVar 0))))
      shifted successorInstance shiftedCode shiftedStep
      middleCode middleStep hsubstitutionReady) as hsubstitutionTransport.
    pose proof (hshiftTarski
      (rawNumeralValue M 1) (rawNumeralValue M 1) source shifted
      sourceAssignmentCode sourceAssignmentStep shiftedCode shiftedStep
      hshiftReady) as hshiftTransport.
    apply (proj2 (proj1 hshiftTransport)).
    apply (proj2 (proj1 hsubstitutionTransport)).
    exact hsuccessorSigma.
Qed.

Theorem raw_codedPAAxiomInduction_sigma_of_progress_transport : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawFixedLevelInductionProgressTransportAll M level ->
  RawFixedLevelPAAxiomInductionSigmaSound M level.
Proof.
  intros M hPA level htransport source axiom
    (shifted & successorInstance & zeroInstance & sourceAll &
     stepImp & stepAll & premise & body & closureCount &
     hshift & hsuccessorSubstitution & hzeroSubstitution &
     hsourceAll & hstepImp & hstepAll & hpremise & hbody &
     _ & hclosure) hadmissible.
  assert (hbodySigma : forall assignmentCode assignmentStep,
      RawFixedLevelTruthAdmissible M level
        body assignmentCode assignmentStep ->
      RawFixedLevelSigmaTruthCertificate M (S level)
        body assignmentCode assignmentStep).
  {
    intros assignmentCode assignmentStep hbodyAdmissible.
    pose proof (htransport source shifted successorInstance zeroInstance
      sourceAll stepImp stepAll premise body
      hsourceAll hstepImp hstepAll hpremise hbody
      hshift hsuccessorSubstitution hzeroSubstitution
      assignmentCode assignmentStep hbodyAdmissible)
      as [hzeroProgress hsuccProgress].
    exact (raw_inductionBody_sigma_of_progress M hPA level
      source zeroInstance stepAll premise sourceAll body
      assignmentCode assignmentStep hbody hpremise hsourceAll
      hbodyAdmissible hzeroProgress hsuccProgress).
  }
  exact (raw_universalClosure_sigma_sound_all M hPA level body hbodySigma
    closureCount axiom (raw_zero M) (raw_zero M) hclosure hadmissible).
Qed.

End PABoundedRawCodedPAAxiomInductionTruth.
