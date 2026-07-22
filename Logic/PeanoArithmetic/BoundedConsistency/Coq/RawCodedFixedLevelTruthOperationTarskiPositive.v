(**
  Positive-level Tarski transport for coded formula shift/substitution.

  The key scheduling trick is to prove transport at [S inputLevel] while
  assuming admissibility at [inputLevel].  At precisely that offset the clean
  Boolean and quantifier laws from [RawCodedFixedLevelTruthLaws] apply, so
  their proofs absorb the permissive rank-zero shortcut in successor truth
  certificates.  The final public theorem uses admissible adjacent-level
  coherence to raise a certificate, transport it at the scheduled level,
  and lower it again.

  Formula-operation traces may have nonstandard length.  All row inductions
  below are therefore represented by first-order PA formulae and use PA's
  internal induction, never Rocq recursion over a decoded formula.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedTermEvaluationTraversal
  RawCodedFormulaRankTraversal RawCodedFormulaOperations
  RawCodedRankZeroTruthTraversal
  RawCodedRankZeroTruthStepFunctionality
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFixedLevelTruthSchedule RawCodedFixedLevelTruthLaws
  RawCodedFixedLevelTruthOperationTransport
  RawCodedFixedLevelTruthOperationTarski.

Import ListNotations.

Module PABoundedRawCodedFixedLevelTruthOperationTarskiPositive.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFixedLevelTruthSchedule.
Import PABoundedRawCodedFixedLevelTruthLaws.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.
Import PABoundedRawCodedFixedLevelTruthOperationTarski.

(** ------------------------------------------------------------------
    A represented, syntax-local shift environment. *)

Definition operationTarskiPositiveAll4 (body : formula) : formula :=
  pAll (pAll (pAll (pAll body))).

Definition operationTarskiPositiveAll8 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll body))))))).

Definition codedFormulaShiftAssignmentLocalCompatibilityTermAt
    (cutoff amount sourceBound targetBound
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  operationTarskiPositiveAll4
    (pImp
      (Formula.ltTermAt (tVar 3) (liftTerm 4 sourceBound))
      (pImp
        (Formula.ltTermAt (tVar 2) (liftTerm 4 targetBound))
        (pImp
          (codedShiftedIndexTermAt
            (liftTerm 4 cutoff) (liftTerm 4 amount)
            (tVar 3) (tVar 2))
          (pImp
            (codedAssignmentLookupTermAt
              (liftTerm 4 sourceAssignmentCode)
              (liftTerm 4 sourceAssignmentStep)
              (tVar 3) (tVar 1))
            (pImp
              (codedAssignmentLookupTermAt
                (liftTerm 4 targetAssignmentCode)
                (liftTerm 4 targetAssignmentStep)
                (tVar 2) (tVar 0))
              (pEq (tVar 1) (tVar 0))))))).

Lemma raw_operationTarskiPositive_eval_liftTerm_four : forall
    (M : RawPAModel) a b c d (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b (scons M c (scons M d e))))
    (liftTerm 4 t) = raw_term_eval M e t.
Proof.
  intros M a b c d e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 4) with (S (S (S (S index)))) by lia. reflexivity.
Qed.

Lemma raw_sat_codedFormulaShiftAssignmentLocalCompatibilityTermAt_iff :
  forall (M : RawPAModel) e cutoff amount sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (codedFormulaShiftAssignmentLocalCompatibilityTermAt
      cutoff amount sourceBound targetBound
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawCodedFormulaShiftAssignmentLocalCompatibility M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e sourceBound) (raw_term_eval M e targetBound)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold codedFormulaShiftAssignmentLocalCompatibilityTermAt,
    operationTarskiPositiveAll4,
    RawCodedFormulaShiftAssignmentLocalCompatibility.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedShiftedIndexTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  repeat setoid_rewrite raw_operationTarskiPositive_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedFormulaShiftAssignmentLocalCompatibility_restrict : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount sourceParentBound targetParentBound
    sourceChildBound targetChildBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaShiftAssignmentLocalCompatibility M cutoff amount
    sourceParentBound targetParentBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  rawLt M sourceChildBound sourceParentBound ->
  rawLt M targetChildBound targetParentBound ->
  RawCodedFormulaShiftAssignmentLocalCompatibility M cutoff amount
    sourceChildBound targetChildBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA cutoff amount sourceParentBound targetParentBound
    sourceChildBound targetChildBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hcompat hsource htarget
    inputIndex outputIndex sourceValue targetValue
    hinput houtput hshift hsourceLookup htargetLookup.
  apply (hcompat inputIndex outputIndex sourceValue targetValue).
  - exact (raw_assignment_lt_trans M hPA
      inputIndex sourceChildBound sourceParentBound hinput hsource).
  - exact (raw_assignment_lt_trans M hPA
      outputIndex targetChildBound targetParentBound houtput htarget).
  - exact hshift.
  - exact hsourceLookup.
  - exact htargetLookup.
Qed.

(** Equality is the only logical leaf whose value depends on the paired
    environments.  This is the syntax-local counterpart of the root theorem
    in the preceding file. *)
Theorem raw_formulaShiftEqOperationRow_rankZero_outputs_agree_local : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount source target sourceOutput targetOutput
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaEqOperationRow M (RawCodedFormulaShiftAtom M)
    amount cutoff source target ->
  RawCodedFormulaShiftAssignmentLocalCompatibility M cutoff amount
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawRankZeroTruthCertificate M source sourceOutput
    sourceAssignmentCode sourceAssignmentStep ->
  RawRankZeroTruthCertificate M target targetOutput
    targetAssignmentCode targetAssignmentStep ->
  sourceOutput = targetOutput.
Proof.
  intros M hPA cutoff amount source target sourceOutput targetOutput
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (sourceLeft & targetLeft & sourceRight & targetRight &
     hsource & htarget & hleftShift & hrightShift)
    hcompat hsourceCertificate htargetCertificate.
  destruct (raw_rankZeroTruthCertificate_eq_view M hPA
    source sourceOutput sourceAssignmentCode sourceAssignmentStep
    sourceLeft sourceRight hsource hsourceCertificate) as
    (sourceLeftValue & sourceRightValue &
     hsourceLeft & hsourceRight & hsourceTruth).
  destruct (raw_rankZeroTruthCertificate_eq_view M hPA
    target targetOutput targetAssignmentCode targetAssignmentStep
    targetLeft targetRight htarget htargetCertificate) as
    (targetLeftValue & targetRightValue &
     htargetLeft & htargetRight & htargetTruth).
  assert (hleftValue : sourceLeftValue = targetLeftValue).
  {
    apply (raw_codedTermShift_evaluation_values_agree_local M hPA
      cutoff amount source target sourceLeft targetLeft
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep hleftShift hcompat).
    - rewrite hsource. apply raw_formulaEq_left_lt. exact hPA.
    - rewrite htarget. apply raw_formulaEq_left_lt. exact hPA.
    - exact hsourceLeft.
    - exact htargetLeft.
  }
  assert (hrightValue : sourceRightValue = targetRightValue).
  {
    apply (raw_codedTermShift_evaluation_values_agree_local M hPA
      cutoff amount source target sourceRight targetRight
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep hrightShift hcompat).
    - rewrite hsource. apply raw_formulaEq_right_lt. exact hPA.
    - rewrite htarget. apply raw_formulaEq_right_lt. exact hPA.
    - exact hsourceRight.
    - exact htargetRight.
  }
  subst targetLeftValue. subst targetRightValue.
  exact (raw_equalityTruth_functional M
    sourceLeftValue sourceRightValue sourceOutput targetOutput
    hsourceTruth htargetTruth).
Qed.

(** ------------------------------------------------------------------
    Scheduled certificate transport. *)

Lemma raw_scheduledTruthCertificateTransport_of_sigma_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    source sourceAssignmentCode sourceAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    target targetAssignmentCode targetAssignmentStep ->
  (RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      source sourceAssignmentCode sourceAssignmentStep <->
   RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      target targetAssignmentCode targetAssignmentStep) ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA inputLevel source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsourceAdmissible htargetAdmissible hsigma.
  split; [exact hsigma |]. split.
  - intro hsourcePi.
    destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
      inputLevel M hPA target targetAssignmentCode targetAssignmentStep
      htargetAdmissible) as [htargetSigma | htargetPi].
    + exfalso. exact (raw_fixedLevelAdmissibleTruthCertificate_exclusive
        inputLevel M hPA source sourceAssignmentCode sourceAssignmentStep
        hsourceAdmissible (proj2 hsigma htargetSigma) hsourcePi).
    + exact htargetPi.
  - intro htargetPi.
    destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
      inputLevel M hPA source sourceAssignmentCode sourceAssignmentStep
      hsourceAdmissible) as [hsourceSigma | hsourcePi].
    + exfalso. exact (raw_fixedLevelAdmissibleTruthCertificate_exclusive
        inputLevel M hPA target targetAssignmentCode targetAssignmentStep
        htargetAdmissible (proj1 hsigma hsourceSigma) htargetPi).
    + exact hsourcePi.
Qed.

Lemma raw_fixedLevelBot_sigma_false_scheduled : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
      assignmentCode assignmentStep,
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
    (rawFormulaBotCode M) assignmentCode assignmentStep -> False.
Proof.
  intros M hPA inputLevel assignmentCode assignmentStep hsigma.
  pose proof (raw_fixedLevelSigmaTruthCertificate_successor_shape_view
    M hPA inputLevel rawShapeBot assignmentCode assignmentStep hsigma)
    as hview.
  cbn [RawFixedLevelSigmaSuccessorShapeView] in hview.
  destruct hview as [hrankZero | hfalse]; [|exact hfalse].
  pose proof (raw_rankZeroTruthCertificate_bot_view M hPA
    (rawFormulaBotCode M) (rawNumeralValue M 1)
    assignmentCode assignmentStep eq_refl hrankZero) as hone.
  exact (raw_zero_neq_truthOne M hPA (eq_sym hone)).
Qed.

Lemma raw_formulaShiftEqOperationRow_scheduled_transport : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
    amount depth source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaEqOperationRow M (RawCodedFormulaShiftAtom M)
    amount depth source target ->
  RawCodedFormulaShiftAssignmentLocalCompatibility M depth amount
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    source sourceAssignmentCode sourceAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    target targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA inputLevel amount depth source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    heq hcompat hsourceAdmissible htargetAdmissible.
  apply (raw_scheduledTruthCertificateTransport_of_sigma_iff M hPA
    inputLevel source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsourceAdmissible htargetAdmissible).
  split.
  - intro hsourceSigma.
    destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
      inputLevel M hPA target targetAssignmentCode targetAssignmentStep
      htargetAdmissible) as [htargetSigma | htargetPi]; [exact htargetSigma |].
    destruct heq as
      (sourceLeft & targetLeft & sourceRight & targetRight &
       hsource & htarget & hleft & hright).
    pose proof (raw_fixedLevelSigmaTruthCertificate_successor_shape_view
      M hPA inputLevel (rawShapeEq sourceLeft sourceRight)
      sourceAssignmentCode sourceAssignmentStep
      (eq_rect source
        (fun code => RawFixedLevelSigmaTruthCertificate M (S inputLevel)
          code sourceAssignmentCode sourceAssignmentStep)
        hsourceSigma (rawFormulaEqCode M sourceLeft sourceRight) hsource))
      as hsourceView.
    pose proof (raw_fixedLevelPiFalsityCertificate_successor_shape_view
      M hPA inputLevel (rawShapeEq targetLeft targetRight)
      targetAssignmentCode targetAssignmentStep
      (eq_rect target
        (fun code => RawFixedLevelPiFalsityCertificate M (S inputLevel)
          code targetAssignmentCode targetAssignmentStep)
        htargetPi (rawFormulaEqCode M targetLeft targetRight) htarget))
      as htargetView.
    cbn [RawFixedLevelSigmaSuccessorShapeView] in hsourceView.
    cbn [RawFixedLevelPiSuccessorShapeView] in htargetView.
    destruct hsourceView as [hsourceZero | hfalse];
      [|exact (False_rect _ hfalse)].
    destruct htargetView as [htargetZero | hfalse];
      [|exact (False_rect _ hfalse)].
    change (RawRankZeroTruthCertificate M
      (rawFormulaEqCode M sourceLeft sourceRight)
      (rawNumeralValue M 1) sourceAssignmentCode sourceAssignmentStep)
      in hsourceZero.
    change (RawRankZeroTruthCertificate M
      (rawFormulaEqCode M targetLeft targetRight)
      (raw_zero M) targetAssignmentCode targetAssignmentStep)
      in htargetZero.
    rewrite <- hsource in hsourceZero.
    rewrite <- htarget in htargetZero.
    pose proof (raw_formulaShiftEqOperationRow_rankZero_outputs_agree_local
      M hPA depth amount source target
      (rawNumeralValue M 1) (raw_zero M)
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      (ex_intro _ sourceLeft (ex_intro _ targetLeft
        (ex_intro _ sourceRight (ex_intro _ targetRight
          (conj hsource (conj htarget (conj hleft hright)))))))
      hcompat hsourceZero htargetZero) as hone.
    exact (False_rect _ (raw_zero_neq_truthOne M hPA (eq_sym hone))).
  - intro htargetSigma.
    destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
      inputLevel M hPA source sourceAssignmentCode sourceAssignmentStep
      hsourceAdmissible) as [hsourceSigma | hsourcePi]; [exact hsourceSigma |].
    destruct heq as
      (sourceLeft & targetLeft & sourceRight & targetRight &
       hsource & htarget & hleft & hright).
    pose proof (raw_fixedLevelPiFalsityCertificate_successor_shape_view
      M hPA inputLevel (rawShapeEq sourceLeft sourceRight)
      sourceAssignmentCode sourceAssignmentStep
      (eq_rect source
        (fun code => RawFixedLevelPiFalsityCertificate M (S inputLevel)
          code sourceAssignmentCode sourceAssignmentStep)
        hsourcePi (rawFormulaEqCode M sourceLeft sourceRight) hsource))
      as hsourceView.
    pose proof (raw_fixedLevelSigmaTruthCertificate_successor_shape_view
      M hPA inputLevel (rawShapeEq targetLeft targetRight)
      targetAssignmentCode targetAssignmentStep
      (eq_rect target
        (fun code => RawFixedLevelSigmaTruthCertificate M (S inputLevel)
          code targetAssignmentCode targetAssignmentStep)
        htargetSigma (rawFormulaEqCode M targetLeft targetRight) htarget))
      as htargetView.
    cbn [RawFixedLevelPiSuccessorShapeView] in hsourceView.
    cbn [RawFixedLevelSigmaSuccessorShapeView] in htargetView.
    destruct hsourceView as [hsourceZero | hfalse];
      [|exact (False_rect _ hfalse)].
    destruct htargetView as [htargetZero | hfalse];
      [|exact (False_rect _ hfalse)].
    change (RawRankZeroTruthCertificate M
      (rawFormulaEqCode M sourceLeft sourceRight)
      (raw_zero M) sourceAssignmentCode sourceAssignmentStep)
      in hsourceZero.
    change (RawRankZeroTruthCertificate M
      (rawFormulaEqCode M targetLeft targetRight)
      (rawNumeralValue M 1) targetAssignmentCode targetAssignmentStep)
      in htargetZero.
    rewrite <- hsource in hsourceZero.
    rewrite <- htarget in htargetZero.
    pose proof (raw_formulaShiftEqOperationRow_rankZero_outputs_agree_local
      M hPA depth amount source target
      (raw_zero M) (rawNumeralValue M 1)
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      (ex_intro _ sourceLeft (ex_intro _ targetLeft
        (ex_intro _ sourceRight (ex_intro _ targetRight
          (conj hsource (conj htarget (conj hleft hright)))))))
      hcompat hsourceZero htargetZero) as hzero.
    exact (False_rect _ (raw_zero_neq_truthOne M hPA hzero)).
Qed.

Lemma raw_formulaShiftBotOperationRow_scheduled_transport : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaBotOperationRow M source target ->
  RawFixedLevelTruthAdmissible M inputLevel
    source sourceAssignmentCode sourceAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    target targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA inputLevel source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep [-> ->]
    hsourceAdmissible htargetAdmissible.
  apply (raw_scheduledTruthCertificateTransport_of_sigma_iff M hPA
    inputLevel (rawFormulaBotCode M) (rawFormulaBotCode M)
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsourceAdmissible htargetAdmissible).
  split; intro hsigma;
    exfalso; eapply raw_fixedLevelBot_sigma_false_scheduled; eauto.
Qed.

Lemma raw_fixedLevelImp_scheduled_transport_of_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
      sourceLeft sourceRight targetLeft targetRight
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaImpCode M sourceLeft sourceRight)
    sourceAssignmentCode sourceAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaImpCode M targetLeft targetRight)
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    sourceLeft targetLeft sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    sourceRight targetRight sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    (rawFormulaImpCode M sourceLeft sourceRight)
    (rawFormulaImpCode M targetLeft targetRight)
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA inputLevel sourceLeft sourceRight targetLeft targetRight
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsource htarget hleft hright.
  apply (raw_scheduledTruthCertificateTransport_of_sigma_iff M hPA
    inputLevel
    (rawFormulaImpCode M sourceLeft sourceRight)
    (rawFormulaImpCode M targetLeft targetRight)
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hsource htarget).
  rewrite (raw_fixedLevelImp_sigma_iff M hPA inputLevel
    sourceLeft sourceRight sourceAssignmentCode sourceAssignmentStep hsource).
  rewrite (raw_fixedLevelImp_sigma_iff M hPA inputLevel
    targetLeft targetRight targetAssignmentCode targetAssignmentStep htarget).
  destruct hleft as [hleftSigma hleftPi].
  destruct hright as [hrightSigma hrightPi]. tauto.
Qed.

Lemma raw_fixedLevelAnd_scheduled_transport_of_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
      sourceLeft sourceRight targetLeft targetRight
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaAndCode M sourceLeft sourceRight)
    sourceAssignmentCode sourceAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaAndCode M targetLeft targetRight)
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    sourceLeft targetLeft sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    sourceRight targetRight sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    (rawFormulaAndCode M sourceLeft sourceRight)
    (rawFormulaAndCode M targetLeft targetRight)
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA inputLevel sourceLeft sourceRight targetLeft targetRight
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsource htarget hleft hright.
  apply (raw_scheduledTruthCertificateTransport_of_sigma_iff M hPA
    inputLevel
    (rawFormulaAndCode M sourceLeft sourceRight)
    (rawFormulaAndCode M targetLeft targetRight)
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hsource htarget).
  rewrite (raw_fixedLevelAnd_sigma_iff M hPA inputLevel
    sourceLeft sourceRight sourceAssignmentCode sourceAssignmentStep hsource).
  rewrite (raw_fixedLevelAnd_sigma_iff M hPA inputLevel
    targetLeft targetRight targetAssignmentCode targetAssignmentStep htarget).
  destruct hleft as [hleftSigma _].
  destruct hright as [hrightSigma _]. tauto.
Qed.

Lemma raw_fixedLevelOr_scheduled_transport_of_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
      sourceLeft sourceRight targetLeft targetRight
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaOrCode M sourceLeft sourceRight)
    sourceAssignmentCode sourceAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaOrCode M targetLeft targetRight)
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    sourceLeft targetLeft sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    sourceRight targetRight sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    (rawFormulaOrCode M sourceLeft sourceRight)
    (rawFormulaOrCode M targetLeft targetRight)
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA inputLevel sourceLeft sourceRight targetLeft targetRight
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsource htarget hleft hright.
  apply (raw_scheduledTruthCertificateTransport_of_sigma_iff M hPA
    inputLevel
    (rawFormulaOrCode M sourceLeft sourceRight)
    (rawFormulaOrCode M targetLeft targetRight)
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hsource htarget).
  rewrite (raw_fixedLevelOr_sigma_iff M hPA inputLevel
    sourceLeft sourceRight sourceAssignmentCode sourceAssignmentStep hsource).
  rewrite (raw_fixedLevelOr_sigma_iff M hPA inputLevel
    targetLeft targetRight targetAssignmentCode targetAssignmentStep htarget).
  destruct hleft as [hleftSigma _].
  destruct hright as [hrightSigma _]. tauto.
Qed.

Definition formulaShiftScheduledTransportBelowTermAt (inputLevel : nat)
    (current amount sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep : term) : formula :=
  operationTarskiPositiveAll8
    (pImp
      (Formula.ltTermAt (tVar 7) (liftTerm 8 current))
      (pImp
        (codedFormulaOperationTripleLookupTermAt
          (liftTerm 8 sourceCode) (liftTerm 8 sourceStep)
          (liftTerm 8 targetCode) (liftTerm 8 targetStep)
          (liftTerm 8 depthCode) (liftTerm 8 depthStep)
          (tVar 7) (tVar 6) (tVar 5) (tVar 4))
        (pImp
          (Formula.ltTermAt (tVar 6) (liftTerm 8 sourceRoot))
          (pImp
            (Formula.ltTermAt (tVar 5) (liftTerm 8 targetRoot))
            (pImp
              (codedFormulaShiftAssignmentLocalCompatibilityTermAt
                (tVar 4) (liftTerm 8 amount) (tVar 6) (tVar 5)
                (tVar 3) (tVar 2) (tVar 1) (tVar 0))
              (pImp
                (fixedLevelTruthAdmissibleTermAt inputLevel
                  (tVar 6) (tVar 3) (tVar 2))
                (pImp
                  (fixedLevelTruthAdmissibleTermAt inputLevel
                    (tVar 5) (tVar 1) (tVar 0))
                  (fixedLevelTruthCertificateTransportTermAt (S inputLevel)
                    (tVar 6) (tVar 5) (tVar 3) (tVar 2)
                    (tVar 1) (tVar 0))))))))).

Definition RawFormulaShiftScheduledTransportBelow (M : RawPAModel)
    (inputLevel : nat)
    (current amount sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep : M) : Prop :=
  forall index input output depth
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M,
    rawLt M index current ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth ->
    rawLt M input sourceRoot ->
    rawLt M output targetRoot ->
    RawCodedFormulaShiftAssignmentLocalCompatibility M depth amount
      input output sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep ->
    RawFixedLevelTruthAdmissible M inputLevel
      input sourceAssignmentCode sourceAssignmentStep ->
    RawFixedLevelTruthAdmissible M inputLevel
      output targetAssignmentCode targetAssignmentStep ->
    RawFixedLevelTruthCertificateTransport M (S inputLevel)
      input output sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep.

Arguments RawFormulaShiftScheduledTransportBelow
  M inputLevel current amount sourceRoot targetRoot sourceCode sourceStep
    targetCode targetStep depthCode depthStep : clear implicits.

Lemma raw_operationTarskiPositive_eval_liftTerm_eight : forall
    (M : RawPAModel) a b c d f g h i (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i e))))))))
    (liftTerm 8 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 8) with
    (S (S (S (S (S (S (S (S index)))))))) by lia. reflexivity.
Qed.

Lemma raw_sat_formulaShiftScheduledTransportBelowTermAt_iff : forall
    (M : RawPAModel) e inputLevel current amount sourceRoot targetRoot
      sourceCode sourceStep targetCode targetStep depthCode depthStep,
  raw_formula_sat M e
    (formulaShiftScheduledTransportBelowTermAt inputLevel
      current amount sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep) <->
  RawFormulaShiftScheduledTransportBelow M inputLevel
    (raw_term_eval M e current) (raw_term_eval M e amount)
    (raw_term_eval M e sourceRoot) (raw_term_eval M e targetRoot)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep).
Proof.
  intros. unfold formulaShiftScheduledTransportBelowTermAt,
    operationTarskiPositiveAll8,
    RawFormulaShiftScheduledTransportBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaOperationTripleLookupTermAt_iff.
  setoid_rewrite
    raw_sat_codedFormulaShiftAssignmentLocalCompatibilityTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelTruthAdmissibleTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelTruthCertificateTransportTermAt_iff.
  repeat setoid_rewrite raw_operationTarskiPositive_eval_liftTerm_eight.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_formulaShiftScheduledTransportBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel amount
    sourceRoot targetRoot sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound current,
  RawCodedFormulaOperationRows M (RawCodedFormulaShiftAtom M) amount
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound ->
  rawLt M current bound ->
  RawFormulaShiftScheduledTransportBelow M inputLevel current amount
    sourceRoot targetRoot sourceCode sourceStep targetCode targetStep
    depthCode depthStep ->
  RawFormulaShiftScheduledTransportBelow M inputLevel (raw_succ M current)
    amount sourceRoot targetRoot sourceCode sourceStep targetCode targetStep
    depthCode depthStep.
Proof.
  intros M hPA inputLevel amount sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound current hrows hcurrent hagree
    index input output depth
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hindex hlookup hinputRoot houtputRoot hcompat
    hsourceAdmissible htargetAdmissible.
  destruct (raw_lt_succ_cases M hPA index current hindex)
    as [hbelow | hequal].
  - exact (hagree index input output depth
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      hbelow hlookup hinputRoot houtputRoot hcompat
      hsourceAdmissible htargetAdmissible).
  - subst index.
    pose proof (hrows current input output depth hcurrent hlookup) as hrow.
    destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
    + exact (raw_formulaShiftEqOperationRow_scheduled_transport M hPA
        inputLevel amount depth input output
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        heq hcompat hsourceAdmissible htargetAdmissible).
    + exact (raw_formulaShiftBotOperationRow_scheduled_transport M hPA
        inputLevel input output
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        hbot hsourceAdmissible htargetAdmissible).
    + destruct himp as
        (leftIndex & inputLeft & outputLeft & leftDepth &
         rightIndex & inputRight & outputRight & rightDepth &
         hleftIndex & hleftLookup & hleftDepth &
         hrightIndex & hrightLookup & hrightDepth & hinput & houtput).
      subst input. subst output.
      destruct (raw_fixedLevelTruthAdmissible_imp_children M hPA
        inputLevel inputLeft inputRight
        sourceAssignmentCode sourceAssignmentStep hsourceAdmissible)
        as [hsourceLeftAdmissible hsourceRightAdmissible].
      destruct (raw_fixedLevelTruthAdmissible_imp_children M hPA
        inputLevel outputLeft outputRight
        targetAssignmentCode targetAssignmentStep htargetAdmissible)
        as [htargetLeftAdmissible htargetRightAdmissible].
      assert (hsourceLeftParent : rawLt M inputLeft
          (rawFormulaImpCode M inputLeft inputRight)).
      { apply raw_formulaBinary_left_lt. exact hPA. }
      assert (hsourceRightParent : rawLt M inputRight
          (rawFormulaImpCode M inputLeft inputRight)).
      { apply raw_formulaBinary_right_lt. exact hPA. }
      assert (htargetLeftParent : rawLt M outputLeft
          (rawFormulaImpCode M outputLeft outputRight)).
      { apply raw_formulaBinary_left_lt. exact hPA. }
      assert (htargetRightParent : rawLt M outputRight
          (rawFormulaImpCode M outputLeft outputRight)).
      { apply raw_formulaBinary_right_lt. exact hPA. }
      assert (hleftCompat :
          RawCodedFormulaShiftAssignmentLocalCompatibility M leftDepth amount
            inputLeft outputLeft
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep).
      {
        rewrite hleftDepth.
        exact (raw_codedFormulaShiftAssignmentLocalCompatibility_restrict
          M hPA depth amount
          (rawFormulaImpCode M inputLeft inputRight)
          (rawFormulaImpCode M outputLeft outputRight)
          inputLeft outputLeft
          sourceAssignmentCode sourceAssignmentStep
          targetAssignmentCode targetAssignmentStep
          hcompat hsourceLeftParent htargetLeftParent).
      }
      assert (hrightCompat :
          RawCodedFormulaShiftAssignmentLocalCompatibility M rightDepth amount
            inputRight outputRight
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep).
      {
        rewrite hrightDepth.
        exact (raw_codedFormulaShiftAssignmentLocalCompatibility_restrict
          M hPA depth amount
          (rawFormulaImpCode M inputLeft inputRight)
          (rawFormulaImpCode M outputLeft outputRight)
          inputRight outputRight
          sourceAssignmentCode sourceAssignmentStep
          targetAssignmentCode targetAssignmentStep
          hcompat hsourceRightParent htargetRightParent).
      }
      pose proof (hagree leftIndex inputLeft outputLeft leftDepth
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        hleftIndex hleftLookup
        (raw_assignment_lt_trans M hPA inputLeft
          (rawFormulaImpCode M inputLeft inputRight) sourceRoot
          hsourceLeftParent hinputRoot)
        (raw_assignment_lt_trans M hPA outputLeft
          (rawFormulaImpCode M outputLeft outputRight) targetRoot
          htargetLeftParent houtputRoot)
        hleftCompat hsourceLeftAdmissible htargetLeftAdmissible)
        as hleftTransport.
      pose proof (hagree rightIndex inputRight outputRight rightDepth
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        hrightIndex hrightLookup
        (raw_assignment_lt_trans M hPA inputRight
          (rawFormulaImpCode M inputLeft inputRight) sourceRoot
          hsourceRightParent hinputRoot)
        (raw_assignment_lt_trans M hPA outputRight
          (rawFormulaImpCode M outputLeft outputRight) targetRoot
          htargetRightParent houtputRoot)
        hrightCompat hsourceRightAdmissible htargetRightAdmissible)
        as hrightTransport.
      exact (raw_fixedLevelImp_scheduled_transport_of_children M hPA
        inputLevel inputLeft inputRight outputLeft outputRight
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        hsourceAdmissible htargetAdmissible
        hleftTransport hrightTransport).
    + destruct hand as
        (leftIndex & inputLeft & outputLeft & leftDepth &
         rightIndex & inputRight & outputRight & rightDepth &
         hleftIndex & hleftLookup & hleftDepth &
         hrightIndex & hrightLookup & hrightDepth & hinput & houtput).
      subst input. subst output.
      destruct (raw_fixedLevelTruthAdmissible_and_children M hPA
        inputLevel inputLeft inputRight
        sourceAssignmentCode sourceAssignmentStep hsourceAdmissible)
        as [hsourceLeftAdmissible hsourceRightAdmissible].
      destruct (raw_fixedLevelTruthAdmissible_and_children M hPA
        inputLevel outputLeft outputRight
        targetAssignmentCode targetAssignmentStep htargetAdmissible)
        as [htargetLeftAdmissible htargetRightAdmissible].
      assert (hsourceLeftParent : rawLt M inputLeft
          (rawFormulaAndCode M inputLeft inputRight)).
      { apply raw_formulaBinary_left_lt. exact hPA. }
      assert (hsourceRightParent : rawLt M inputRight
          (rawFormulaAndCode M inputLeft inputRight)).
      { apply raw_formulaBinary_right_lt. exact hPA. }
      assert (htargetLeftParent : rawLt M outputLeft
          (rawFormulaAndCode M outputLeft outputRight)).
      { apply raw_formulaBinary_left_lt. exact hPA. }
      assert (htargetRightParent : rawLt M outputRight
          (rawFormulaAndCode M outputLeft outputRight)).
      { apply raw_formulaBinary_right_lt. exact hPA. }
      assert (hleftCompat :
          RawCodedFormulaShiftAssignmentLocalCompatibility M leftDepth amount
            inputLeft outputLeft
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep).
      {
        rewrite hleftDepth.
        exact (raw_codedFormulaShiftAssignmentLocalCompatibility_restrict
          M hPA depth amount
          (rawFormulaAndCode M inputLeft inputRight)
          (rawFormulaAndCode M outputLeft outputRight)
          inputLeft outputLeft
          sourceAssignmentCode sourceAssignmentStep
          targetAssignmentCode targetAssignmentStep
          hcompat hsourceLeftParent htargetLeftParent).
      }
      assert (hrightCompat :
          RawCodedFormulaShiftAssignmentLocalCompatibility M rightDepth amount
            inputRight outputRight
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep).
      {
        rewrite hrightDepth.
        exact (raw_codedFormulaShiftAssignmentLocalCompatibility_restrict
          M hPA depth amount
          (rawFormulaAndCode M inputLeft inputRight)
          (rawFormulaAndCode M outputLeft outputRight)
          inputRight outputRight
          sourceAssignmentCode sourceAssignmentStep
          targetAssignmentCode targetAssignmentStep
          hcompat hsourceRightParent htargetRightParent).
      }
      pose proof (hagree leftIndex inputLeft outputLeft leftDepth
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        hleftIndex hleftLookup
        (raw_assignment_lt_trans M hPA inputLeft
          (rawFormulaAndCode M inputLeft inputRight) sourceRoot
          hsourceLeftParent hinputRoot)
        (raw_assignment_lt_trans M hPA outputLeft
          (rawFormulaAndCode M outputLeft outputRight) targetRoot
          htargetLeftParent houtputRoot)
        hleftCompat hsourceLeftAdmissible htargetLeftAdmissible)
        as hleftTransport.
      pose proof (hagree rightIndex inputRight outputRight rightDepth
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        hrightIndex hrightLookup
        (raw_assignment_lt_trans M hPA inputRight
          (rawFormulaAndCode M inputLeft inputRight) sourceRoot
          hsourceRightParent hinputRoot)
        (raw_assignment_lt_trans M hPA outputRight
          (rawFormulaAndCode M outputLeft outputRight) targetRoot
          htargetRightParent houtputRoot)
        hrightCompat hsourceRightAdmissible htargetRightAdmissible)
        as hrightTransport.
      exact (raw_fixedLevelAnd_scheduled_transport_of_children M hPA
        inputLevel inputLeft inputRight outputLeft outputRight
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        hsourceAdmissible htargetAdmissible
        hleftTransport hrightTransport).
    + destruct hor as
        (leftIndex & inputLeft & outputLeft & leftDepth &
         rightIndex & inputRight & outputRight & rightDepth &
         hleftIndex & hleftLookup & hleftDepth &
         hrightIndex & hrightLookup & hrightDepth & hinput & houtput).
      subst input. subst output.
      destruct (raw_fixedLevelTruthAdmissible_or_children M hPA
        inputLevel inputLeft inputRight
        sourceAssignmentCode sourceAssignmentStep hsourceAdmissible)
        as [hsourceLeftAdmissible hsourceRightAdmissible].
      destruct (raw_fixedLevelTruthAdmissible_or_children M hPA
        inputLevel outputLeft outputRight
        targetAssignmentCode targetAssignmentStep htargetAdmissible)
        as [htargetLeftAdmissible htargetRightAdmissible].
      assert (hsourceLeftParent : rawLt M inputLeft
          (rawFormulaOrCode M inputLeft inputRight)).
      { apply raw_formulaBinary_left_lt. exact hPA. }
      assert (hsourceRightParent : rawLt M inputRight
          (rawFormulaOrCode M inputLeft inputRight)).
      { apply raw_formulaBinary_right_lt. exact hPA. }
      assert (htargetLeftParent : rawLt M outputLeft
          (rawFormulaOrCode M outputLeft outputRight)).
      { apply raw_formulaBinary_left_lt. exact hPA. }
      assert (htargetRightParent : rawLt M outputRight
          (rawFormulaOrCode M outputLeft outputRight)).
      { apply raw_formulaBinary_right_lt. exact hPA. }
      assert (hleftCompat :
          RawCodedFormulaShiftAssignmentLocalCompatibility M leftDepth amount
            inputLeft outputLeft
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep).
      {
        rewrite hleftDepth.
        exact (raw_codedFormulaShiftAssignmentLocalCompatibility_restrict
          M hPA depth amount
          (rawFormulaOrCode M inputLeft inputRight)
          (rawFormulaOrCode M outputLeft outputRight)
          inputLeft outputLeft
          sourceAssignmentCode sourceAssignmentStep
          targetAssignmentCode targetAssignmentStep
          hcompat hsourceLeftParent htargetLeftParent).
      }
      assert (hrightCompat :
          RawCodedFormulaShiftAssignmentLocalCompatibility M rightDepth amount
            inputRight outputRight
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep).
      {
        rewrite hrightDepth.
        exact (raw_codedFormulaShiftAssignmentLocalCompatibility_restrict
          M hPA depth amount
          (rawFormulaOrCode M inputLeft inputRight)
          (rawFormulaOrCode M outputLeft outputRight)
          inputRight outputRight
          sourceAssignmentCode sourceAssignmentStep
          targetAssignmentCode targetAssignmentStep
          hcompat hsourceRightParent htargetRightParent).
      }
      pose proof (hagree leftIndex inputLeft outputLeft leftDepth
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        hleftIndex hleftLookup
        (raw_assignment_lt_trans M hPA inputLeft
          (rawFormulaOrCode M inputLeft inputRight) sourceRoot
          hsourceLeftParent hinputRoot)
        (raw_assignment_lt_trans M hPA outputLeft
          (rawFormulaOrCode M outputLeft outputRight) targetRoot
          htargetLeftParent houtputRoot)
        hleftCompat hsourceLeftAdmissible htargetLeftAdmissible)
        as hleftTransport.
      pose proof (hagree rightIndex inputRight outputRight rightDepth
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        hrightIndex hrightLookup
        (raw_assignment_lt_trans M hPA inputRight
          (rawFormulaOrCode M inputLeft inputRight) sourceRoot
          hsourceRightParent hinputRoot)
        (raw_assignment_lt_trans M hPA outputRight
          (rawFormulaOrCode M outputLeft outputRight) targetRoot
          htargetRightParent houtputRoot)
        hrightCompat hsourceRightAdmissible htargetRightAdmissible)
        as hrightTransport.
      exact (raw_fixedLevelOr_scheduled_transport_of_children M hPA
        inputLevel inputLeft inputRight outputLeft outputRight
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        hsourceAdmissible htargetAdmissible
        hleftTransport hrightTransport).
    + destruct hall as
        (childIndex & inputChild & outputChild & childDepth &
         hchildIndex & hchildLookup & hchildDepth & hinput & houtput).
      subst input. subst output.
      assert (hsourceChildParent : rawLt M inputChild
          (rawFormulaAllCode M inputChild)).
      { apply raw_formulaCodeList2_child_lt. exact hPA. }
      assert (htargetChildParent : rawLt M outputChild
          (rawFormulaAllCode M outputChild)).
      { apply raw_formulaCodeList2_child_lt. exact hPA. }
      apply (raw_scheduledTruthCertificateTransport_of_sigma_iff M hPA
        inputLevel (rawFormulaAllCode M inputChild)
        (rawFormulaAllCode M outputChild)
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        hsourceAdmissible htargetAdmissible).
      split.
      * intro hsourceSigma.
        destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
          inputLevel M hPA (rawFormulaAllCode M outputChild)
          targetAssignmentCode targetAssignmentStep htargetAdmissible)
          as [htargetSigma | htargetPi]; [exact htargetSigma |].
        destruct (raw_fixedLevelAll_pi_witness M hPA inputLevel outputChild
          targetAssignmentCode targetAssignmentStep htargetAdmissible
          htargetPi) as
          (witness & targetChildAssignmentCode & targetChildAssignmentStep &
           htargetPrepend & htargetChildPi).
        destruct (raw_codedAssignmentPrepend_exists M hPA
          sourceAssignmentCode sourceAssignmentStep witness
          (rawFormulaAllCode M inputChild)) as
          (sourceChildAssignmentCode & sourceChildAssignmentStep &
           hsourcePrepend).
        assert (hchildCompat :
          RawCodedFormulaShiftAssignmentLocalCompatibility M childDepth amount
            inputChild outputChild
            sourceChildAssignmentCode sourceChildAssignmentStep
            targetChildAssignmentCode targetChildAssignmentStep).
        {
          rewrite hchildDepth.
          apply (raw_codedFormulaShiftAssignmentLocalCompatibility_prepend
            M hPA depth amount
            (rawFormulaAllCode M inputChild)
            (rawFormulaAllCode M outputChild)
            inputChild outputChild witness
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep
            sourceChildAssignmentCode sourceChildAssignmentStep
            targetChildAssignmentCode targetChildAssignmentStep
            hcompat).
          - exact (proj1 (proj2 hsourceAdmissible)).
          - exact (proj1 (proj2 htargetAdmissible)).
          - exact hsourcePrepend.
          - exact htargetPrepend.
          - exact hsourceChildParent.
          - exact htargetChildParent.
        }
        destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
          inputLevel inputChild sourceAssignmentCode sourceAssignmentStep
          witness sourceChildAssignmentCode sourceChildAssignmentStep
          hsourceAdmissible hsourcePrepend) as
          [hsourceChildAtomic [hsourceChildDefined hsourceChildDomain]].
        destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
          inputLevel outputChild targetAssignmentCode targetAssignmentStep
          witness targetChildAssignmentCode targetChildAssignmentStep
          htargetAdmissible htargetPrepend) as
          [htargetChildAtomic [htargetChildDefined htargetChildDomain]].
        assert (hsourceChildAdmissible : RawFixedLevelTruthAdmissible M
          inputLevel inputChild sourceChildAssignmentCode
          sourceChildAssignmentStep).
        { repeat split; try assumption. now right. }
        assert (htargetChildAdmissible : RawFixedLevelTruthAdmissible M
          inputLevel outputChild targetChildAssignmentCode
          targetChildAssignmentStep).
        { repeat split; try assumption. now right. }
        pose proof (hagree childIndex inputChild outputChild childDepth
          sourceChildAssignmentCode sourceChildAssignmentStep
          targetChildAssignmentCode targetChildAssignmentStep
          hchildIndex hchildLookup
          (raw_assignment_lt_trans M hPA inputChild
            (rawFormulaAllCode M inputChild) sourceRoot
            hsourceChildParent hinputRoot)
          (raw_assignment_lt_trans M hPA outputChild
            (rawFormulaAllCode M outputChild) targetRoot
            htargetChildParent houtputRoot)
          hchildCompat hsourceChildAdmissible htargetChildAdmissible)
          as hchildTransport.
        pose proof (raw_fixedLevelAll_sigma_instantiate M hPA inputLevel
          inputChild sourceAssignmentCode sourceAssignmentStep witness
          sourceChildAssignmentCode sourceChildAssignmentStep
          hsourceAdmissible hsourceSigma hsourcePrepend)
          as hsourceChildSigma.
        pose proof (proj2 (proj2 hchildTransport) htargetChildPi)
          as hsourceChildPi.
        exact (False_rect _
          (raw_fixedLevelAdmissibleTruthCertificate_exclusive
            inputLevel M hPA inputChild
            sourceChildAssignmentCode sourceChildAssignmentStep
            hsourceChildAdmissible hsourceChildSigma hsourceChildPi)).
      * intro htargetSigma.
        destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
          inputLevel M hPA (rawFormulaAllCode M inputChild)
          sourceAssignmentCode sourceAssignmentStep hsourceAdmissible)
          as [hsourceSigma | hsourcePi]; [exact hsourceSigma |].
        destruct (raw_fixedLevelAll_pi_witness M hPA inputLevel inputChild
          sourceAssignmentCode sourceAssignmentStep hsourceAdmissible
          hsourcePi) as
          (witness & sourceChildAssignmentCode & sourceChildAssignmentStep &
           hsourcePrepend & hsourceChildPi).
        destruct (raw_codedAssignmentPrepend_exists M hPA
          targetAssignmentCode targetAssignmentStep witness
          (rawFormulaAllCode M outputChild)) as
          (targetChildAssignmentCode & targetChildAssignmentStep &
           htargetPrepend).
        assert (hchildCompat :
          RawCodedFormulaShiftAssignmentLocalCompatibility M childDepth amount
            inputChild outputChild
            sourceChildAssignmentCode sourceChildAssignmentStep
            targetChildAssignmentCode targetChildAssignmentStep).
        {
          rewrite hchildDepth.
          apply (raw_codedFormulaShiftAssignmentLocalCompatibility_prepend
            M hPA depth amount
            (rawFormulaAllCode M inputChild)
            (rawFormulaAllCode M outputChild)
            inputChild outputChild witness
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep
            sourceChildAssignmentCode sourceChildAssignmentStep
            targetChildAssignmentCode targetChildAssignmentStep
            hcompat).
          - exact (proj1 (proj2 hsourceAdmissible)).
          - exact (proj1 (proj2 htargetAdmissible)).
          - exact hsourcePrepend.
          - exact htargetPrepend.
          - exact hsourceChildParent.
          - exact htargetChildParent.
        }
        destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
          inputLevel inputChild sourceAssignmentCode sourceAssignmentStep
          witness sourceChildAssignmentCode sourceChildAssignmentStep
          hsourceAdmissible hsourcePrepend) as
          [hsourceChildAtomic [hsourceChildDefined hsourceChildDomain]].
        destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
          inputLevel outputChild targetAssignmentCode targetAssignmentStep
          witness targetChildAssignmentCode targetChildAssignmentStep
          htargetAdmissible htargetPrepend) as
          [htargetChildAtomic [htargetChildDefined htargetChildDomain]].
        assert (hsourceChildAdmissible : RawFixedLevelTruthAdmissible M
          inputLevel inputChild sourceChildAssignmentCode
          sourceChildAssignmentStep).
        { repeat split; try assumption. now right. }
        assert (htargetChildAdmissible : RawFixedLevelTruthAdmissible M
          inputLevel outputChild targetChildAssignmentCode
          targetChildAssignmentStep).
        { repeat split; try assumption. now right. }
        pose proof (hagree childIndex inputChild outputChild childDepth
          sourceChildAssignmentCode sourceChildAssignmentStep
          targetChildAssignmentCode targetChildAssignmentStep
          hchildIndex hchildLookup
          (raw_assignment_lt_trans M hPA inputChild
            (rawFormulaAllCode M inputChild) sourceRoot
            hsourceChildParent hinputRoot)
          (raw_assignment_lt_trans M hPA outputChild
            (rawFormulaAllCode M outputChild) targetRoot
            htargetChildParent houtputRoot)
          hchildCompat hsourceChildAdmissible htargetChildAdmissible)
          as hchildTransport.
        pose proof (raw_fixedLevelAll_sigma_instantiate M hPA inputLevel
          outputChild targetAssignmentCode targetAssignmentStep witness
          targetChildAssignmentCode targetChildAssignmentStep
          htargetAdmissible htargetSigma htargetPrepend)
          as htargetChildSigma.
        pose proof (proj1 (proj2 hchildTransport) hsourceChildPi)
          as htargetChildPi.
        exact (False_rect _
          (raw_fixedLevelAdmissibleTruthCertificate_exclusive
            inputLevel M hPA outputChild
            targetChildAssignmentCode targetChildAssignmentStep
            htargetChildAdmissible htargetChildSigma htargetChildPi)).
    + destruct hex as
        (childIndex & inputChild & outputChild & childDepth &
         hchildIndex & hchildLookup & hchildDepth & hinput & houtput).
      subst input. subst output.
      assert (hsourceChildParent : rawLt M inputChild
          (rawFormulaExCode M inputChild)).
      { apply raw_formulaCodeList2_child_lt. exact hPA. }
      assert (htargetChildParent : rawLt M outputChild
          (rawFormulaExCode M outputChild)).
      { apply raw_formulaCodeList2_child_lt. exact hPA. }
      apply (raw_scheduledTruthCertificateTransport_of_sigma_iff M hPA
        inputLevel (rawFormulaExCode M inputChild)
        (rawFormulaExCode M outputChild)
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        hsourceAdmissible htargetAdmissible).
      split.
      * intro hsourceSigma.
        destruct (proj1 (raw_fixedLevelEx_sigma_iff M hPA inputLevel
          inputChild sourceAssignmentCode sourceAssignmentStep
          hsourceAdmissible) hsourceSigma) as
          (witness & sourceChildAssignmentCode & sourceChildAssignmentStep &
           hsourcePrepend & hsourceChildSigma).
        destruct (raw_codedAssignmentPrepend_exists M hPA
          targetAssignmentCode targetAssignmentStep witness
          (rawFormulaExCode M outputChild)) as
          (targetChildAssignmentCode & targetChildAssignmentStep &
           htargetPrepend).
        assert (hchildCompat :
          RawCodedFormulaShiftAssignmentLocalCompatibility M childDepth amount
            inputChild outputChild
            sourceChildAssignmentCode sourceChildAssignmentStep
            targetChildAssignmentCode targetChildAssignmentStep).
        {
          rewrite hchildDepth.
          apply (raw_codedFormulaShiftAssignmentLocalCompatibility_prepend
            M hPA depth amount
            (rawFormulaExCode M inputChild)
            (rawFormulaExCode M outputChild)
            inputChild outputChild witness
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep
            sourceChildAssignmentCode sourceChildAssignmentStep
            targetChildAssignmentCode targetChildAssignmentStep hcompat).
          - exact (proj1 (proj2 hsourceAdmissible)).
          - exact (proj1 (proj2 htargetAdmissible)).
          - exact hsourcePrepend.
          - exact htargetPrepend.
          - exact hsourceChildParent.
          - exact htargetChildParent.
        }
        destruct (raw_fixedLevelTruthAdmissible_ex_binder_sigma_core M hPA
          inputLevel inputChild sourceAssignmentCode sourceAssignmentStep
          witness sourceChildAssignmentCode sourceChildAssignmentStep
          hsourceAdmissible hsourcePrepend) as
          [hsourceChildAtomic [hsourceChildDefined hsourceChildDomain]].
        destruct (raw_fixedLevelTruthAdmissible_ex_binder_sigma_core M hPA
          inputLevel outputChild targetAssignmentCode targetAssignmentStep
          witness targetChildAssignmentCode targetChildAssignmentStep
          htargetAdmissible htargetPrepend) as
          [htargetChildAtomic [htargetChildDefined htargetChildDomain]].
        assert (hsourceChildAdmissible : RawFixedLevelTruthAdmissible M
          inputLevel inputChild sourceChildAssignmentCode
          sourceChildAssignmentStep).
        { repeat split; try assumption. now left. }
        assert (htargetChildAdmissible : RawFixedLevelTruthAdmissible M
          inputLevel outputChild targetChildAssignmentCode
          targetChildAssignmentStep).
        { repeat split; try assumption. now left. }
        pose proof (hagree childIndex inputChild outputChild childDepth
          sourceChildAssignmentCode sourceChildAssignmentStep
          targetChildAssignmentCode targetChildAssignmentStep
          hchildIndex hchildLookup
          (raw_assignment_lt_trans M hPA inputChild
            (rawFormulaExCode M inputChild) sourceRoot
            hsourceChildParent hinputRoot)
          (raw_assignment_lt_trans M hPA outputChild
            (rawFormulaExCode M outputChild) targetRoot
            htargetChildParent houtputRoot)
          hchildCompat hsourceChildAdmissible htargetChildAdmissible)
          as hchildTransport.
        apply (proj2 (raw_fixedLevelEx_sigma_iff M hPA inputLevel
          outputChild targetAssignmentCode targetAssignmentStep
          htargetAdmissible)).
        exists witness, targetChildAssignmentCode, targetChildAssignmentStep.
        split; [exact htargetPrepend |].
        exact (proj1 (proj1 hchildTransport) hsourceChildSigma).
      * intro htargetSigma.
        destruct (proj1 (raw_fixedLevelEx_sigma_iff M hPA inputLevel
          outputChild targetAssignmentCode targetAssignmentStep
          htargetAdmissible) htargetSigma) as
          (witness & targetChildAssignmentCode & targetChildAssignmentStep &
           htargetPrepend & htargetChildSigma).
        destruct (raw_codedAssignmentPrepend_exists M hPA
          sourceAssignmentCode sourceAssignmentStep witness
          (rawFormulaExCode M inputChild)) as
          (sourceChildAssignmentCode & sourceChildAssignmentStep &
           hsourcePrepend).
        assert (hchildCompat :
          RawCodedFormulaShiftAssignmentLocalCompatibility M childDepth amount
            inputChild outputChild
            sourceChildAssignmentCode sourceChildAssignmentStep
            targetChildAssignmentCode targetChildAssignmentStep).
        {
          rewrite hchildDepth.
          apply (raw_codedFormulaShiftAssignmentLocalCompatibility_prepend
            M hPA depth amount
            (rawFormulaExCode M inputChild)
            (rawFormulaExCode M outputChild)
            inputChild outputChild witness
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep
            sourceChildAssignmentCode sourceChildAssignmentStep
            targetChildAssignmentCode targetChildAssignmentStep hcompat).
          - exact (proj1 (proj2 hsourceAdmissible)).
          - exact (proj1 (proj2 htargetAdmissible)).
          - exact hsourcePrepend.
          - exact htargetPrepend.
          - exact hsourceChildParent.
          - exact htargetChildParent.
        }
        destruct (raw_fixedLevelTruthAdmissible_ex_binder_sigma_core M hPA
          inputLevel inputChild sourceAssignmentCode sourceAssignmentStep
          witness sourceChildAssignmentCode sourceChildAssignmentStep
          hsourceAdmissible hsourcePrepend) as
          [hsourceChildAtomic [hsourceChildDefined hsourceChildDomain]].
        destruct (raw_fixedLevelTruthAdmissible_ex_binder_sigma_core M hPA
          inputLevel outputChild targetAssignmentCode targetAssignmentStep
          witness targetChildAssignmentCode targetChildAssignmentStep
          htargetAdmissible htargetPrepend) as
          [htargetChildAtomic [htargetChildDefined htargetChildDomain]].
        assert (hsourceChildAdmissible : RawFixedLevelTruthAdmissible M
          inputLevel inputChild sourceChildAssignmentCode
          sourceChildAssignmentStep).
        { repeat split; try assumption. now left. }
        assert (htargetChildAdmissible : RawFixedLevelTruthAdmissible M
          inputLevel outputChild targetChildAssignmentCode
          targetChildAssignmentStep).
        { repeat split; try assumption. now left. }
        pose proof (hagree childIndex inputChild outputChild childDepth
          sourceChildAssignmentCode sourceChildAssignmentStep
          targetChildAssignmentCode targetChildAssignmentStep
          hchildIndex hchildLookup
          (raw_assignment_lt_trans M hPA inputChild
            (rawFormulaExCode M inputChild) sourceRoot
            hsourceChildParent hinputRoot)
          (raw_assignment_lt_trans M hPA outputChild
            (rawFormulaExCode M outputChild) targetRoot
            htargetChildParent houtputRoot)
          hchildCompat hsourceChildAdmissible htargetChildAdmissible)
          as hchildTransport.
        apply (proj2 (raw_fixedLevelEx_sigma_iff M hPA inputLevel
          inputChild sourceAssignmentCode sourceAssignmentStep
          hsourceAdmissible)).
        exists witness, sourceChildAssignmentCode, sourceChildAssignmentStep.
        split; [exact hsourcePrepend |].
        exact (proj2 (proj1 hchildTransport) htargetChildSigma).
Qed.

Definition formulaShiftScheduledTransportThroughTermAt (inputLevel : nat)
    (current limit amount sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep : term) : formula :=
  pImp (Formula.leTermAt current limit)
    (formulaShiftScheduledTransportBelowTermAt inputLevel
      current amount sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep).

Definition RawFormulaShiftScheduledTransportThrough (M : RawPAModel)
    (inputLevel : nat)
    (current limit amount sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep : M) : Prop :=
  rawLe M current limit ->
  RawFormulaShiftScheduledTransportBelow M inputLevel current amount
    sourceRoot targetRoot sourceCode sourceStep targetCode targetStep
    depthCode depthStep.

Lemma raw_sat_formulaShiftScheduledTransportThroughTermAt_iff : forall
    (M : RawPAModel) e inputLevel current limit amount sourceRoot targetRoot
      sourceCode sourceStep targetCode targetStep depthCode depthStep,
  raw_formula_sat M e
    (formulaShiftScheduledTransportThroughTermAt inputLevel
      current limit amount sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep) <->
  RawFormulaShiftScheduledTransportThrough M inputLevel
    (raw_term_eval M e current) (raw_term_eval M e limit)
    (raw_term_eval M e amount)
    (raw_term_eval M e sourceRoot) (raw_term_eval M e targetRoot)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep).
Proof.
  intros. unfold formulaShiftScheduledTransportThroughTermAt,
    RawFormulaShiftScheduledTransportThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_traversal,
    raw_sat_formulaShiftScheduledTransportBelowTermAt_iff. tauto.
Qed.

Theorem raw_formulaShiftScheduledTransportBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel amount
    sourceRoot targetRoot sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound,
  RawCodedFormulaOperationRows M (RawCodedFormulaShiftAtom M) amount
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound ->
  RawFormulaShiftScheduledTransportBelow M inputLevel bound amount
    sourceRoot targetRoot sourceCode sourceStep targetCode targetStep
    depthCode depthStep.
Proof.
  intros M hPA inputLevel amount sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound hrows.
  set (parameterEnv := scons M bound (scons M amount
    (scons M sourceRoot (scons M targetRoot
      (scons M sourceCode (scons M sourceStep
        (scons M targetCode (scons M targetStep
          (scons M depthCode (scons M depthStep
            (fun _ : nat => raw_zero M))))))))))).
  set (phi := formulaShiftScheduledTransportThroughTermAt inputLevel
    (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
    (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_formulaShiftScheduledTransportThroughTermAt_iff M
          (scons M (raw_zero M) parameterEnv) inputLevel
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _ index input output depth
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep hindex.
      exfalso. exact (raw_not_lt_zero M hPA index hindex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_formulaShiftScheduledTransportThroughTermAt_iff M
          (scons M current parameterEnv) inputLevel
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10)) hcurrent)
        as hcurrentRaw.
      apply (proj2
        (raw_sat_formulaShiftScheduledTransportThroughTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) inputLevel
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10))).
      unfold parameterEnv in hcurrentRaw |- *.
      cbn [raw_term_eval scons] in hcurrentRaw |- *.
      intro hsuccLe.
      assert (hcurrentBound : rawLt M current bound).
      { exact (raw_lt_of_succ_le_traversal M hPA current bound hsuccLe). }
      exact (raw_formulaShiftScheduledTransportBelow_succ M hPA
        inputLevel amount sourceRoot targetRoot
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound current hrows hcurrentBound
        (hcurrentRaw (raw_lt_to_le M current bound hcurrentBound))).
  }
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_formulaShiftScheduledTransportThroughTermAt_iff M
      (scons M bound parameterEnv) inputLevel
      (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
      (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10))
    (hall bound)) as hbound.
  unfold parameterEnv in hbound. cbn [raw_term_eval scons] in hbound.
  exact (hbound (raw_le_refl_traversal M hPA bound)).
Qed.

Theorem raw_formulaShiftOperationTrace_scheduled_transport : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
    cutoff amount source target sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound rootIndex
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaOperationTrace M (RawCodedFormulaShiftAtom M)
    amount cutoff sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound rootIndex source target ->
  RawCodedFormulaShiftAssignmentLocalCompatibility M cutoff amount
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    source sourceAssignmentCode sourceAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    target targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA inputLevel cutoff amount source target
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (_ & _ & _ & hroot & hrootLookup & hrows)
    hcompat hsource htarget.
  pose proof (raw_formulaShiftScheduledTransportBelow_all M hPA
    inputLevel amount (raw_succ M source) (raw_succ M target)
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound hrows) as hall.
  exact (hall rootIndex source target cutoff
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hroot hrootLookup
    (raw_assignment_lt_self_succ M hPA source)
    (raw_assignment_lt_self_succ M hPA target)
    hcompat hsource htarget).
Qed.

Theorem raw_fixedLevelFormulaShiftTarskiStep_scheduled : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
    cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawFixedLevelFormulaShiftTransportReady M inputLevel
    cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA inputLevel cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hready.
  pose proof (raw_fixedLevelFormulaShiftTransportReady_target_admissible
    M hPA inputLevel cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hready) as htarget.
  destruct hready as
    [(sourceCode & sourceStep & targetCode & targetStep &
      depthCode & depthStep & bound & rootIndex & htrace)
     [hassignments [hsource [_ _]]]].
  apply (raw_formulaShiftOperationTrace_scheduled_transport M hPA
    inputLevel cutoff amount source target
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep htrace).
  - exact (raw_codedFormulaShiftAssignmentRelation_local M hPA
      cutoff amount source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep hassignments).
  - exact hsource.
  - exact htarget.
Qed.

(** Adjacent admissible coherence turns the scheduled theorem into the exact
    same-level public Tarski step.  This works uniformly at level zero too;
    the separately proved level-zero theorem remains useful as the atomic
    base audit. *)
Theorem raw_fixedLevelFormulaShiftTarskiStep_all : forall level
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawFixedLevelFormulaShiftTarskiStep M level
    cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros level M hPA cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hready.
  pose proof hready as hreadyFull.
  pose proof (raw_fixedLevelFormulaShiftTarskiStep_scheduled M hPA level
    cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hreadyFull) as hscheduled.
  pose proof (raw_fixedLevelFormulaShiftTransportReady_target_admissible
    M hPA level cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hreadyFull) as htargetAdmissible.
  destruct hready as
    [_ [_ [hsourceAdmissible [_ hranks]]]].
  pose proof (raw_fixedLevel_domains_iff_of_rankAgreement M hPA level
    source target
    (raw_fixedLevelTruthAdmissible_wellFormed M level source
      sourceAssignmentCode sourceAssignmentStep hsourceAdmissible)
    (raw_fixedLevelTruthAdmissible_wellFormed M level target
      targetAssignmentCode targetAssignmentStep htargetAdmissible)
    hranks) as [hsigmaDomains hpiDomains].
  pose proof (raw_fixedLevelAdmissibleTruthCertificateCoherence_all
    level M hPA source sourceAssignmentCode sourceAssignmentStep
    hsourceAdmissible) as [hsourceSigmaCoherence hsourcePiCoherence].
  pose proof (raw_fixedLevelAdmissibleTruthCertificateCoherence_all
    level M hPA target targetAssignmentCode targetAssignmentStep
    htargetAdmissible) as [htargetSigmaCoherence htargetPiCoherence].
  destruct hscheduled as [hscheduledSigma hscheduledPi]. split.
  - split.
    + intro hsourceCertificate.
      pose proof (raw_fixedLevelSigmaTruthCertificate_domain M hPA level
        source sourceAssignmentCode sourceAssignmentStep hsourceCertificate)
        as hsourceDomain.
      pose proof (proj1 hsigmaDomains hsourceDomain) as htargetDomain.
      apply (proj2 (htargetSigmaCoherence htargetDomain)).
      apply (proj1 hscheduledSigma).
      exact (proj1 (hsourceSigmaCoherence hsourceDomain) hsourceCertificate).
    + intro htargetCertificate.
      pose proof (raw_fixedLevelSigmaTruthCertificate_domain M hPA level
        target targetAssignmentCode targetAssignmentStep htargetCertificate)
        as htargetDomain.
      pose proof (proj2 hsigmaDomains htargetDomain) as hsourceDomain.
      apply (proj2 (hsourceSigmaCoherence hsourceDomain)).
      apply (proj2 hscheduledSigma).
      exact (proj1 (htargetSigmaCoherence htargetDomain) htargetCertificate).
  - split.
    + intro hsourceCertificate.
      pose proof (raw_fixedLevelPiFalsityCertificate_domain M hPA level
        source sourceAssignmentCode sourceAssignmentStep hsourceCertificate)
        as hsourceDomain.
      pose proof (proj1 hpiDomains hsourceDomain) as htargetDomain.
      apply (proj2 (htargetPiCoherence htargetDomain)).
      apply (proj1 hscheduledPi).
      exact (proj1 (hsourcePiCoherence hsourceDomain) hsourceCertificate).
    + intro htargetCertificate.
      pose proof (raw_fixedLevelPiFalsityCertificate_domain M hPA level
        target targetAssignmentCode targetAssignmentStep htargetCertificate)
        as htargetDomain.
      pose proof (proj2 hpiDomains htargetDomain) as hsourceDomain.
      apply (proj2 (hsourcePiCoherence hsourceDomain)).
      apply (proj2 hscheduledPi).
      exact (proj1 (htargetPiCoherence htargetDomain) htargetCertificate).
Qed.

Definition fixedLevelFormulaShiftTarskiStepFormula (level : nat) : formula :=
  fixedLevelFormulaShiftTarskiStepTermAt level
    (tVar 0) (tVar 1) (tVar 2) (tVar 3)
    (tVar 4) (tVar 5) (tVar 6) (tVar 7).

Theorem fixedLevelFormulaShiftTarskiStepFormula_raw_valid : forall level
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e (fixedLevelFormulaShiftTarskiStepFormula level).
Proof.
  intros level M hPA e.
  unfold fixedLevelFormulaShiftTarskiStepFormula.
  apply (proj2 (raw_sat_fixedLevelFormulaShiftTarskiStepTermAt_iff
    M e level (tVar 0) (tVar 1) (tVar 2) (tVar 3)
    (tVar 4) (tVar 5) (tVar 6) (tVar 7))).
  apply raw_fixedLevelFormulaShiftTarskiStep_all. exact hPA.
Qed.

Definition fixedLevelFormulaShiftTarskiStepFormula_closed (level : nat) :
    formula :=
  Formula.sealPA (fixedLevelFormulaShiftTarskiStepFormula level).

Theorem fixedLevelFormulaShiftTarskiStepFormula_closed_sentence :
  forall level,
  Formula.Sentence (fixedLevelFormulaShiftTarskiStepFormula_closed level).
Proof.
  intro level. unfold fixedLevelFormulaShiftTarskiStepFormula_closed.
  apply Formula.sealPA_sentence.
Qed.

Theorem fixedLevelFormulaShiftTarskiStepFormula_closed_raw_valid :
  forall level (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (fixedLevelFormulaShiftTarskiStepFormula_closed level).
Proof.
  intros level M hPA e.
  unfold fixedLevelFormulaShiftTarskiStepFormula_closed.
  apply (raw_formula_sat_sealPA_of_valid M). intro e'.
  exact (fixedLevelFormulaShiftTarskiStepFormula_raw_valid level M hPA e').
Qed.

Theorem PA_proves_fixedLevelFormulaShiftTarskiStepFormula_closed :
  forall level : nat,
  Formula.BProv Formula.Ax_s []
    (fixedLevelFormulaShiftTarskiStepFormula_closed level).
Proof.
  intro level. apply PA_BProv_of_raw_valid.
  - apply fixedLevelFormulaShiftTarskiStepFormula_closed_sentence.
  - apply fixedLevelFormulaShiftTarskiStepFormula_closed_raw_valid.
Qed.

Theorem PA_proves_fixedLevelFormulaShiftTarskiStepFormula :
  forall level : nat,
  Formula.BProv Formula.Ax_s []
    (fixedLevelFormulaShiftTarskiStepFormula level).
Proof.
  intro level.
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s [] (fixedLevelFormulaShiftTarskiStepFormula level)
    (fun n => n)
    (PA_proves_fixedLevelFormulaShiftTarskiStepFormula_closed level)) as h.
  now rewrite Formula.rename_id in h.
Qed.

End PABoundedRawCodedFixedLevelTruthOperationTarskiPositive.
