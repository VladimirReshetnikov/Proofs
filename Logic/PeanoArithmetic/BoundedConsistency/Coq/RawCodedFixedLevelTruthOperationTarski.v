(**
  Tarski compatibility for transparent coded formula operations.

  The public operation graph pairs source and target syntax rows, while the
  public evaluator and truth graphs hide independent beta tables.  The first
  part of this file develops the bridge needed between them.  In particular,
  child evaluator certificates are recovered from a parent's closed support
  traversal without decoding a carrier element.  The resulting nonstandard
  inductions prove complete rank-zero formula transport, the actual
  fixed-level Tarski steps at level zero, and PA proofs of their represented
  formulae.  The final section isolates the stronger, syntax-bounded
  assignment invariant required when a positive-level proof crosses a
  binder.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawModelCompleteness
  RawCodedSyntaxConstructors RawCodedSyntaxConstructorSeparation
  RawCodedProofDescent
  RawCodedAssignment RawCodedTermEvaluationStep
  RawCodedTermEvaluationStepFunctionality
  RawCodedTermEvaluationTraversal RawCodedTermEvaluationCapacity
  RawCodedFormulaOperations RawCodedRankZeroTruthTraversal
  RawCodedRankZeroTruthStep
  RawCodedRankZeroTruthStepFunctionality
  RawCodedRankZeroTruthElimination
  RawCodedRankZeroTruthTotality
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthBaseLaws
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFixedLevelTruthOperationTransport.

Import ListNotations.

Module PABoundedRawCodedFixedLevelTruthOperationTarski.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedTermEvaluationStep.
Import PABoundedRawCodedTermEvaluationStepFunctionality.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationCapacity.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedRankZeroTruthStep.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedRankZeroTruthElimination.
Import PABoundedRawCodedRankZeroTruthTotality.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthBaseLaws.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.

(** ------------------------------------------------------------------
    Constructor views of complete term-evaluation certificates. *)

Lemma raw_termEvaluationTraversal_restrict_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    root child assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep,
  RawTermEvaluationTraversal M (raw_succ M root)
    assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep ->
  rawLt M child root ->
  RawTermEvaluationTraversal M (raw_succ M child)
    assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep.
Proof.
  intros M hPA root child assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep [hsupport [htable hrows]] hchild.
  assert (hintoRoot : forall index,
      rawLt M index (raw_succ M child) ->
      rawLt M index (raw_succ M root)).
  {
    intros index hindex.
    assert (hindexRoot : rawLt M index root).
    {
      exact (raw_lt_le_trans_pair M hPA
        index (raw_succ M child) root hindex
        (raw_succ_le_of_lt_pair M hPA child root hchild)).
    }
    exact (raw_assignment_lt_trans M hPA index root (raw_succ M root)
      hindexRoot (raw_assignment_lt_self_succ M hPA root)).
  }
  split.
  - intros index hindex. exact (hsupport index (hintoRoot index hindex)).
  - split.
    + intros index hindex. exact (htable index (hintoRoot index hindex)).
    + intros code hcode hsupported.
      exact (hrows code (hintoRoot code hcode) hsupported).
Qed.

Lemma raw_termEvaluationCertificate_child_with_tables : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    root rootValue assignmentCode assignmentStep
      tableCode tableStep supportCode supportStep,
  RawTermEvaluationCertificateWithTables M
    root rootValue assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep ->
  forall child childValue,
    rawLt M child root ->
    rawTermCodeSupported M supportCode supportStep child ->
    RawCodedAssignmentLookup M tableCode tableStep child childValue ->
    RawTermEvaluationCertificate M
      child childValue assignmentCode assignmentStep.
Proof.
  intros M hPA root rootValue assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep
    [htraversal [hrootSupport hrootLookup]]
    child childValue hchild hchildSupport hchildLookup.
  exists supportCode, supportStep, tableCode, tableStep.
  split.
  - exact (raw_termEvaluationTraversal_restrict_child M hPA
      root child assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep htraversal hchild).
  - split; assumption.
Qed.

Lemma raw_termEvaluationCertificateWithTables_root_closed_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    root value assignmentCode assignmentStep
      tableCode tableStep supportCode supportStep,
  RawTermEvaluationCertificateWithTables M
    root value assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep ->
  RawTermEvaluationClosedStep M
    root value assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep.
Proof.
  intros M hPA root value assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep
    [[hsupportDefined [htableDefined hrows]]
     [hrootSupport hrootLookup]].
  destruct (hrows root (raw_assignment_lt_self_succ M hPA root)
    hrootSupport) as [canonical [hcanonicalLookup hstep]].
  assert (hvalue : value = canonical).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      tableCode tableStep root value canonical
      hrootLookup hcanonicalLookup).
  }
  now rewrite <- hvalue in hstep.
Qed.

Lemma raw_termEvaluationCertificate_var_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    index value assignmentCode assignmentStep,
  RawTermEvaluationCertificate M
    (rawTermVarCode M index) value assignmentCode assignmentStep ->
  RawCodedAssignmentLookup M assignmentCode assignmentStep index value.
Proof.
  intros M hPA index value assignmentCode assignmentStep
    (supportCode & supportStep & tableCode & tableStep & hcertificate).
  pose proof (raw_termEvaluationCertificateWithTables_root_closed_step
    M hPA (rawTermVarCode M index) value assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep hcertificate) as hstep.
  destruct hstep as (left & leftValue & right & rightValue & hrow).
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as [hcode hlookup].
    unfold rawTermVarCode in hcode.
    destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
      _ _ _ _ hcode) as [_ hindex].
    now subst left.
  - destruct hzero as [hcode _].
    exfalso. exact (raw_termVarCode_neq_termZeroCode M hPA index hcode).
  - destruct hsucc as [hsucc _]. destruct hsucc as [hcode _].
    exfalso. exact (raw_termVarCode_neq_termSuccCode M hPA index left hcode).
  - destruct hadd as [hadd _]. destruct hadd as [hcode _].
    exfalso. exact (raw_termVarCode_neq_termAddCode M hPA
      index left right hcode).
  - destruct hmul as [hmul _]. destruct hmul as [hcode _].
    exfalso. exact (raw_termVarCode_neq_termMulCode M hPA
      index left right hcode).
Qed.

Lemma raw_termEvaluationCertificate_zero_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    value assignmentCode assignmentStep,
  RawTermEvaluationCertificate M
    (rawTermZeroCode M) value assignmentCode assignmentStep ->
  value = raw_zero M.
Proof.
  intros M hPA value assignmentCode assignmentStep
    (supportCode & supportStep & tableCode & tableStep & hcertificate).
  pose proof (raw_termEvaluationCertificateWithTables_root_closed_step
    M hPA (rawTermZeroCode M) value assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep hcertificate) as hstep.
  destruct hstep as (left & leftValue & right & rightValue & hrow).
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as [hcode _].
    exfalso. exact (raw_termVarCode_neq_termZeroCode M hPA left
      (eq_sym hcode)).
  - exact (proj2 hzero).
  - destruct hsucc as [hsucc _]. destruct hsucc as [hcode _].
    exfalso. exact (raw_termZeroCode_neq_termSuccCode M hPA left hcode).
  - destruct hadd as [hadd _]. destruct hadd as [hcode _].
    exfalso. exact (raw_termZeroCode_neq_termAddCode M hPA left right hcode).
  - destruct hmul as [hmul _]. destruct hmul as [hcode _].
    exfalso. exact (raw_termZeroCode_neq_termMulCode M hPA left right hcode).
Qed.

Lemma raw_termEvaluationCertificate_succ_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    child value assignmentCode assignmentStep,
  RawTermEvaluationCertificate M
    (rawTermSuccCode M child) value assignmentCode assignmentStep ->
  exists childValue : M,
    RawTermEvaluationCertificate M
      child childValue assignmentCode assignmentStep /\
    value = raw_succ M childValue.
Proof.
  intros M hPA child value assignmentCode assignmentStep
    (supportCode & supportStep & tableCode & tableStep & hcertificate).
  pose proof (raw_termEvaluationCertificateWithTables_root_closed_step
    M hPA (rawTermSuccCode M child) value assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep hcertificate) as hstep.
  destruct hstep as (left & leftValue & right & rightValue & hrow).
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as [hcode _].
    exfalso. exact (raw_termVarCode_neq_termSuccCode M hPA left child
      (eq_sym hcode)).
  - destruct hzero as [hcode _].
    exfalso. exact (raw_termZeroCode_neq_termSuccCode M hPA child
      (eq_sym hcode)).
  - destruct hsucc as
      [[hcode [hlookup hvalue]] [hsupport hlt]].
    unfold rawTermSuccCode in hcode.
    destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
      _ _ _ _ hcode) as [_ hchild].
    subst left. exists leftValue. split; [|exact hvalue].
    exact (raw_termEvaluationCertificate_child_with_tables M hPA
      (rawTermSuccCode M child) value assignmentCode assignmentStep
      tableCode tableStep supportCode supportStep hcertificate
      child leftValue hlt hsupport hlookup).
  - destruct hadd as [hadd _]. destruct hadd as [hcode _].
    exfalso. exact (raw_termSuccCode_neq_termAddCode M hPA
      child left right hcode).
  - destruct hmul as [hmul _]. destruct hmul as [hcode _].
    exfalso. exact (raw_termSuccCode_neq_termMulCode M hPA
      child left right hcode).
Qed.

Lemma raw_termEvaluationCertificate_add_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    left right value assignmentCode assignmentStep,
  RawTermEvaluationCertificate M
    (rawTermAddCode M left right) value assignmentCode assignmentStep ->
  exists leftValue rightValue : M,
    RawTermEvaluationCertificate M
      left leftValue assignmentCode assignmentStep /\
    RawTermEvaluationCertificate M
      right rightValue assignmentCode assignmentStep /\
    value = raw_add M leftValue rightValue.
Proof.
  intros M hPA left right value assignmentCode assignmentStep
    (supportCode & supportStep & tableCode & tableStep & hcertificate).
  pose proof (raw_termEvaluationCertificateWithTables_root_closed_step
    M hPA (rawTermAddCode M left right) value assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep hcertificate) as hstep.
  destruct hstep as (actualLeft & leftValue & actualRight & rightValue & hrow).
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as [hcode _].
    exfalso. exact (raw_termVarCode_neq_termAddCode M hPA
      actualLeft left right (eq_sym hcode)).
  - destruct hzero as [hcode _].
    exfalso. exact (raw_termZeroCode_neq_termAddCode M hPA
      left right (eq_sym hcode)).
  - destruct hsucc as [hsucc _]. destruct hsucc as [hcode _].
    exfalso. exact (raw_termSuccCode_neq_termAddCode M hPA
      actualLeft left right (eq_sym hcode)).
  - destruct hadd as
      [[hcode [hleftLookup [hrightLookup hvalue]]]
       [hleftSupport [hrightSupport [hleftLt hrightLt]]]].
    unfold rawTermAddCode in hcode.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcode) as [_ [hleft hright]].
    subst actualLeft. subst actualRight.
    exists leftValue, rightValue. split.
    + exact (raw_termEvaluationCertificate_child_with_tables M hPA
        (rawTermAddCode M left right) value assignmentCode assignmentStep
        tableCode tableStep supportCode supportStep hcertificate
        left leftValue hleftLt hleftSupport hleftLookup).
    + split.
      * exact (raw_termEvaluationCertificate_child_with_tables M hPA
          (rawTermAddCode M left right) value assignmentCode assignmentStep
          tableCode tableStep supportCode supportStep hcertificate
          right rightValue hrightLt hrightSupport hrightLookup).
      * exact hvalue.
  - destruct hmul as [hmul _]. destruct hmul as [hcode _].
    exfalso. exact (raw_termAddCode_neq_termMulCode M hPA
      left right actualLeft actualRight hcode).
Qed.

Lemma raw_termEvaluationCertificate_mul_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    left right value assignmentCode assignmentStep,
  RawTermEvaluationCertificate M
    (rawTermMulCode M left right) value assignmentCode assignmentStep ->
  exists leftValue rightValue : M,
    RawTermEvaluationCertificate M
      left leftValue assignmentCode assignmentStep /\
    RawTermEvaluationCertificate M
      right rightValue assignmentCode assignmentStep /\
    value = raw_mul M leftValue rightValue.
Proof.
  intros M hPA left right value assignmentCode assignmentStep
    (supportCode & supportStep & tableCode & tableStep & hcertificate).
  pose proof (raw_termEvaluationCertificateWithTables_root_closed_step
    M hPA (rawTermMulCode M left right) value assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep hcertificate) as hstep.
  destruct hstep as (actualLeft & leftValue & actualRight & rightValue & hrow).
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as [hcode _].
    exfalso. exact (raw_termVarCode_neq_termMulCode M hPA
      actualLeft left right (eq_sym hcode)).
  - destruct hzero as [hcode _].
    exfalso. exact (raw_termZeroCode_neq_termMulCode M hPA
      left right (eq_sym hcode)).
  - destruct hsucc as [hsucc _]. destruct hsucc as [hcode _].
    exfalso. exact (raw_termSuccCode_neq_termMulCode M hPA
      actualLeft left right (eq_sym hcode)).
  - destruct hadd as [hadd _]. destruct hadd as [hcode _].
    exfalso. exact (raw_termAddCode_neq_termMulCode M hPA
      actualLeft actualRight left right (eq_sym hcode)).
  - destruct hmul as
      [[hcode [hleftLookup [hrightLookup hvalue]]]
       [hleftSupport [hrightSupport [hleftLt hrightLt]]]].
    unfold rawTermMulCode in hcode.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcode) as [_ [hleft hright]].
    subst actualLeft. subst actualRight.
    exists leftValue, rightValue. split.
    + exact (raw_termEvaluationCertificate_child_with_tables M hPA
        (rawTermMulCode M left right) value assignmentCode assignmentStep
        tableCode tableStep supportCode supportStep hcertificate
        left leftValue hleftLt hleftSupport hleftLookup).
    + split.
      * exact (raw_termEvaluationCertificate_child_with_tables M hPA
          (rawTermMulCode M left right) value assignmentCode assignmentStep
          tableCode tableStep supportCode supportStep hcertificate
          right rightValue hrightLt hrightSupport hrightLookup).
      * exact hvalue.
Qed.

(** ------------------------------------------------------------------
    Generic paired-term Tarski induction.

    Recursive constructors are uniform for shift and opening.  Only the
    variable row differs, so its semantic compatibility is an explicit
    premise.  The induction predicate is a genuine PA formula and therefore
    ranges through a nonstandard operation-table bound. *)

Definition operationTarskiAll5 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll body)))).

Definition termOperationEvaluationAgreementBelowTermAt
    (current sourceBound sourceCode sourceStep targetCode targetStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  operationTarskiAll5
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 5 current))
      (pImp
        (codedTermOperationPairLookupTermAt
          (liftTerm 5 sourceCode) (liftTerm 5 sourceStep)
          (liftTerm 5 targetCode) (liftTerm 5 targetStep)
          (tVar 4) (tVar 3) (tVar 2))
        (pImp
          (Formula.ltTermAt (tVar 3) (liftTerm 5 sourceBound))
          (pImp
            (termEvaluationCertificateTermAt
              (tVar 3) (tVar 1)
              (liftTerm 5 sourceAssignmentCode)
              (liftTerm 5 sourceAssignmentStep))
            (pImp
              (termEvaluationCertificateTermAt
                (tVar 2) (tVar 0)
                (liftTerm 5 targetAssignmentCode)
                (liftTerm 5 targetAssignmentStep))
              (pEq (tVar 1) (tVar 0))))))).

Definition RawTermOperationEvaluationAgreementBelow (M : RawPAModel)
    (current sourceBound sourceCode sourceStep targetCode targetStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  forall index input output : M,
  forall sourceValue targetValue : M,
    rawLt M index current ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep index input output ->
    rawLt M input sourceBound ->
    RawTermEvaluationCertificate M input sourceValue
      sourceAssignmentCode sourceAssignmentStep ->
    RawTermEvaluationCertificate M output targetValue
      targetAssignmentCode targetAssignmentStep ->
    sourceValue = targetValue.

Arguments RawTermOperationEvaluationAgreementBelow
  M current sourceBound sourceCode sourceStep targetCode targetStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_operationTarski_eval_liftTerm_five : forall (M : RawPAModel)
    a b c d f (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d (scons M f e)))))
    (liftTerm 5 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 5) with (S (S (S (S (S index))))) by lia.
  reflexivity.
Qed.

Lemma raw_sat_termOperationEvaluationAgreementBelowTermAt_iff : forall
    (M : RawPAModel) e current sourceBound
      sourceCode sourceStep targetCode targetStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (termOperationEvaluationAgreementBelowTermAt
      current sourceBound sourceCode sourceStep targetCode targetStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawTermOperationEvaluationAgreementBelow M
    (raw_term_eval M e current)
    (raw_term_eval M e sourceBound)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold termOperationEvaluationAgreementBelowTermAt,
    operationTarskiAll5, RawTermOperationEvaluationAgreementBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_termEvaluationCertificateTermAt_iff.
  repeat setoid_rewrite raw_operationTarski_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawTermOperationVariableEvaluationCompatible (M : RawPAModel)
    (variableRow : M -> M -> Prop)
    (sourceBound : M)
    (sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  forall input output sourceValue targetValue : M,
    variableRow input output ->
    rawLt M input sourceBound ->
    RawTermEvaluationCertificate M input sourceValue
      sourceAssignmentCode sourceAssignmentStep ->
    RawTermEvaluationCertificate M output targetValue
      targetAssignmentCode targetAssignmentStep ->
    sourceValue = targetValue.

Arguments RawTermOperationVariableEvaluationCompatible
  M variableRow sourceBound sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_termOperationEvaluationAgreementBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (variableRow : M -> M -> Prop)
    sourceBound sourceCode sourceStep targetCode targetStep limit
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep current,
  RawCodedTermOperationRows M
    (RawCodedTermOperationTraversalRow M variableRow
      sourceCode sourceStep targetCode targetStep)
    sourceCode sourceStep targetCode targetStep limit ->
  RawTermOperationVariableEvaluationCompatible M variableRow
    sourceBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  rawLt M current limit ->
  RawTermOperationEvaluationAgreementBelow M current
    sourceBound sourceCode sourceStep targetCode targetStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawTermOperationEvaluationAgreementBelow M (raw_succ M current)
    sourceBound sourceCode sourceStep targetCode targetStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA variableRow sourceBound sourceCode sourceStep targetCode targetStep
    limit sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep current
    hrows hvariable hcurrent hagree
    index input output sourceValue targetValue hindex hlookup
    hinputBound hsourceEvaluation htargetEvaluation.
  destruct (raw_lt_succ_cases M hPA index current hindex)
    as [hbelow | heq].
  - exact (hagree index input output sourceValue targetValue
      hbelow hlookup hinputBound hsourceEvaluation htargetEvaluation).
  - subst index.
    pose proof (hrows current input output hcurrent hlookup) as hrow.
    destruct hrow as
      [hvariableRow | [hzero | [hsucc | [hadd | hmul]]]].
    + exact (hvariable input output sourceValue targetValue
        hvariableRow hinputBound hsourceEvaluation htargetEvaluation).
    + destruct hzero as [hinput houtput]. subst input. subst output.
      rewrite (raw_termEvaluationCertificate_zero_view M hPA
        sourceValue sourceAssignmentCode sourceAssignmentStep
        hsourceEvaluation).
      rewrite (raw_termEvaluationCertificate_zero_view M hPA
        targetValue targetAssignmentCode targetAssignmentStep
        htargetEvaluation).
      reflexivity.
    + destruct hsucc as
        (childIndex & inputChild & outputChild & hchildIndex &
         hchildLookup & hinput & houtput).
      subst input. subst output.
      destruct (raw_termEvaluationCertificate_succ_view M hPA
        inputChild sourceValue sourceAssignmentCode sourceAssignmentStep
        hsourceEvaluation) as
        (sourceChildValue & hsourceChild & hsourceValue).
      destruct (raw_termEvaluationCertificate_succ_view M hPA
        outputChild targetValue targetAssignmentCode targetAssignmentStep
        htargetEvaluation) as
        (targetChildValue & htargetChild & htargetValue).
      rewrite hsourceValue, htargetValue.
      f_equal.
      assert (hchildBound : rawLt M inputChild sourceBound).
      {
        apply (raw_assignment_lt_trans M hPA inputChild
          (rawTermSuccCode M inputChild) sourceBound).
        - change (rawLt M inputChild
            (rawListCode M [rawNumeralValue M 2; inputChild])).
          apply rawProofListCode_member_lt; [exact hPA |].
          simpl. tauto.
        - exact hinputBound.
      }
      exact (hagree childIndex inputChild outputChild
        sourceChildValue targetChildValue hchildIndex hchildLookup
        hchildBound hsourceChild htargetChild).
    + destruct hadd as
        (leftIndex & inputLeft & outputLeft & rightIndex &
         inputRight & outputRight & hleftIndex & hleftLookup &
         hrightIndex & hrightLookup & hinput & houtput).
      subst input. subst output.
      destruct (raw_termEvaluationCertificate_add_view M hPA
        inputLeft inputRight sourceValue
        sourceAssignmentCode sourceAssignmentStep hsourceEvaluation) as
        (sourceLeftValue & sourceRightValue &
         hsourceLeft & hsourceRight & hsourceValue).
      destruct (raw_termEvaluationCertificate_add_view M hPA
        outputLeft outputRight targetValue
        targetAssignmentCode targetAssignmentStep htargetEvaluation) as
        (targetLeftValue & targetRightValue &
         htargetLeft & htargetRight & htargetValue).
      rewrite hsourceValue, htargetValue.
      f_equal.
      * apply (hagree leftIndex inputLeft outputLeft
          sourceLeftValue targetLeftValue hleftIndex hleftLookup).
        -- apply (raw_assignment_lt_trans M hPA inputLeft
            (rawTermAddCode M inputLeft inputRight) sourceBound).
           ++ change (rawLt M inputLeft
                (rawListCode M
                  [rawNumeralValue M 3; inputLeft; inputRight])).
              apply rawProofListCode_member_lt; [exact hPA |].
              simpl. tauto.
           ++ exact hinputBound.
        -- exact hsourceLeft.
        -- exact htargetLeft.
      * apply (hagree rightIndex inputRight outputRight
          sourceRightValue targetRightValue hrightIndex hrightLookup).
        -- apply (raw_assignment_lt_trans M hPA inputRight
            (rawTermAddCode M inputLeft inputRight) sourceBound).
           ++ change (rawLt M inputRight
                (rawListCode M
                  [rawNumeralValue M 3; inputLeft; inputRight])).
              apply rawProofListCode_member_lt; [exact hPA |].
              simpl. tauto.
           ++ exact hinputBound.
        -- exact hsourceRight.
        -- exact htargetRight.
    + destruct hmul as
        (leftIndex & inputLeft & outputLeft & rightIndex &
         inputRight & outputRight & hleftIndex & hleftLookup &
         hrightIndex & hrightLookup & hinput & houtput).
      subst input. subst output.
      destruct (raw_termEvaluationCertificate_mul_view M hPA
        inputLeft inputRight sourceValue
        sourceAssignmentCode sourceAssignmentStep hsourceEvaluation) as
        (sourceLeftValue & sourceRightValue &
         hsourceLeft & hsourceRight & hsourceValue).
      destruct (raw_termEvaluationCertificate_mul_view M hPA
        outputLeft outputRight targetValue
        targetAssignmentCode targetAssignmentStep htargetEvaluation) as
        (targetLeftValue & targetRightValue &
         htargetLeft & htargetRight & htargetValue).
      rewrite hsourceValue, htargetValue.
      f_equal.
      * apply (hagree leftIndex inputLeft outputLeft
          sourceLeftValue targetLeftValue hleftIndex hleftLookup).
        -- apply (raw_assignment_lt_trans M hPA inputLeft
            (rawTermMulCode M inputLeft inputRight) sourceBound).
           ++ change (rawLt M inputLeft
                (rawListCode M
                  [rawNumeralValue M 4; inputLeft; inputRight])).
              apply rawProofListCode_member_lt; [exact hPA |].
              simpl. tauto.
           ++ exact hinputBound.
        -- exact hsourceLeft.
        -- exact htargetLeft.
      * apply (hagree rightIndex inputRight outputRight
          sourceRightValue targetRightValue hrightIndex hrightLookup).
        -- apply (raw_assignment_lt_trans M hPA inputRight
            (rawTermMulCode M inputLeft inputRight) sourceBound).
           ++ change (rawLt M inputRight
                (rawListCode M
                  [rawNumeralValue M 4; inputLeft; inputRight])).
              apply rawProofListCode_member_lt; [exact hPA |].
              simpl. tauto.
           ++ exact hinputBound.
        -- exact hsourceRight.
        -- exact htargetRight.
Qed.

Definition termOperationEvaluationAgreementThroughTermAt
    (current limit sourceBound sourceCode sourceStep targetCode targetStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  pImp (Formula.leTermAt current limit)
    (termOperationEvaluationAgreementBelowTermAt
      current sourceBound sourceCode sourceStep targetCode targetStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep).

Definition RawTermOperationEvaluationAgreementThrough (M : RawPAModel)
    (current limit sourceBound sourceCode sourceStep targetCode targetStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  rawLe M current limit ->
  RawTermOperationEvaluationAgreementBelow M current
    sourceBound sourceCode sourceStep targetCode targetStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.

Lemma raw_sat_termOperationEvaluationAgreementThroughTermAt_iff : forall
    (M : RawPAModel) e current limit sourceBound
      sourceCode sourceStep targetCode targetStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (termOperationEvaluationAgreementThroughTermAt current limit
      sourceBound sourceCode sourceStep targetCode targetStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawTermOperationEvaluationAgreementThrough M
    (raw_term_eval M e current) (raw_term_eval M e limit)
    (raw_term_eval M e sourceBound)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold termOperationEvaluationAgreementThroughTermAt,
    RawTermOperationEvaluationAgreementThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_traversal,
    raw_sat_termOperationEvaluationAgreementBelowTermAt_iff.
  tauto.
Qed.

Theorem raw_termOperationEvaluationAgreementBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (variableRow : M -> M -> Prop)
    sourceBound sourceCode sourceStep targetCode targetStep limit
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedTermOperationRows M
    (RawCodedTermOperationTraversalRow M variableRow
      sourceCode sourceStep targetCode targetStep)
    sourceCode sourceStep targetCode targetStep limit ->
  RawTermOperationVariableEvaluationCompatible M variableRow
    sourceBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawTermOperationEvaluationAgreementBelow M limit
    sourceBound sourceCode sourceStep targetCode targetStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA variableRow sourceBound sourceCode sourceStep targetCode targetStep
    limit sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hrows hvariable.
  set (parameterEnv := scons M limit (scons M sourceBound
    (scons M sourceCode (scons M sourceStep
      (scons M targetCode (scons M targetStep
        (scons M sourceAssignmentCode (scons M sourceAssignmentStep
          (scons M targetAssignmentCode (scons M targetAssignmentStep
            (fun _ : nat => raw_zero M))))))))))).
  set (phi := termOperationEvaluationAgreementThroughTermAt
    (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
    (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_termOperationEvaluationAgreementThroughTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _. intros index input output sourceValue targetValue hindex.
      exfalso. exact (raw_not_lt_zero M hPA index hindex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_termOperationEvaluationAgreementThroughTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10)) hcurrent)
        as hcurrentRaw.
      apply (proj2
        (raw_sat_termOperationEvaluationAgreementThroughTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10))).
      unfold parameterEnv in hcurrentRaw |- *.
      cbn [raw_term_eval scons] in hcurrentRaw |- *.
      intro hsuccLe.
      assert (hcurrentLimit : rawLt M current limit).
      { exact (raw_lt_of_succ_le_traversal M hPA current limit hsuccLe). }
      exact (raw_termOperationEvaluationAgreementBelow_succ M hPA
        variableRow sourceBound sourceCode sourceStep targetCode targetStep limit
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep current
        hrows hvariable hcurrentLimit
        (hcurrentRaw (raw_lt_to_le M current limit hcurrentLimit))).
  }
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_termOperationEvaluationAgreementThroughTermAt_iff M
      (scons M limit parameterEnv)
      (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
      (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10))
    (hall limit)) as hlimit.
  unfold parameterEnv in hlimit.
  cbn [raw_term_eval scons] in hlimit.
  exact (hlimit (raw_le_refl_traversal M hPA limit)).
Qed.

Theorem raw_termOperationTrace_evaluation_values_agree : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (variableRow : M -> M -> Prop)
    sourceBound sourceCode sourceStep targetCode targetStep
      bound rootIndex input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound ->
  RawCodedAssignmentDefinedThrough M targetCode targetStep bound ->
  rawLt M rootIndex bound ->
  RawCodedTermOperationPairLookup M
    sourceCode sourceStep targetCode targetStep rootIndex input output ->
  RawCodedTermOperationRows M
    (RawCodedTermOperationTraversalRow M variableRow
      sourceCode sourceStep targetCode targetStep)
    sourceCode sourceStep targetCode targetStep bound ->
  RawTermOperationVariableEvaluationCompatible M variableRow
    sourceBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  forall sourceValue targetValue,
    rawLt M input sourceBound ->
    RawTermEvaluationCertificate M input sourceValue
      sourceAssignmentCode sourceAssignmentStep ->
    RawTermEvaluationCertificate M output targetValue
      targetAssignmentCode targetAssignmentStep ->
    sourceValue = targetValue.
Proof.
  intros M hPA variableRow sourceBound sourceCode sourceStep
    targetCode targetStep
    bound rootIndex input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    _ _ hroot hrootLookup hrows hvariable sourceValue targetValue
    hinputBound hsourceEvaluation htargetEvaluation.
  pose proof (raw_termOperationEvaluationAgreementBelow_all M hPA
    variableRow sourceBound sourceCode sourceStep targetCode targetStep bound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hrows hvariable) as hagree.
  exact (hagree rootIndex input output sourceValue targetValue
    hroot hrootLookup hinputBound hsourceEvaluation htargetEvaluation).
Qed.

(** A shifted variable obtains the same value from assignments related by
    the formula-level de Bruijn graph.  The source-term-code guard implies
    the variable-index guard because every list-code field is strictly below
    the enclosing constructor code. *)
Lemma raw_termShiftVariableEvaluationCompatible : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount sourceBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaShiftAssignmentRelation M cutoff amount sourceBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawTermOperationVariableEvaluationCompatible M
    (RawCodedTermShiftVariableRow M cutoff amount) sourceBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA cutoff amount sourceBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hrelation
    input output sourceValue targetValue
    (inputIndex & outputIndex & hinput & houtput & hshifted)
    hinputBound hsourceEvaluation htargetEvaluation.
  subst input. subst output.
  assert (hindexCode : rawLt M inputIndex (rawTermVarCode M inputIndex)).
  {
    change (rawLt M inputIndex
      (rawListCode M [rawNumeralValue M 0; inputIndex])).
    apply rawProofListCode_member_lt; [exact hPA |].
    simpl. tauto.
  }
  assert (hindexBound : rawLt M inputIndex sourceBound).
  {
    exact (raw_assignment_lt_trans M hPA inputIndex
      (rawTermVarCode M inputIndex) sourceBound hindexCode hinputBound).
  }
  pose proof (raw_termEvaluationCertificate_var_view M hPA
    inputIndex sourceValue sourceAssignmentCode sourceAssignmentStep
    hsourceEvaluation) as hsourceLookup.
  pose proof (raw_termEvaluationCertificate_var_view M hPA
    outputIndex targetValue targetAssignmentCode targetAssignmentStep
    htargetEvaluation) as htargetLookup.
  pose proof (proj1
    (hrelation inputIndex outputIndex sourceValue hindexBound hshifted)
    hsourceLookup) as htargetSourceValue.
  exact (raw_codedAssignmentLookup_functional M hPA
    targetAssignmentCode targetAssignmentStep outputIndex
    sourceValue targetValue htargetSourceValue htargetLookup).
Qed.

Theorem raw_codedTermShift_evaluation_values_agree : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount sourceBound input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedTermShift M cutoff amount input output ->
  RawCodedFormulaShiftAssignmentRelation M cutoff amount sourceBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  rawLt M input sourceBound ->
  forall sourceValue targetValue,
    RawTermEvaluationCertificate M input sourceValue
      sourceAssignmentCode sourceAssignmentStep ->
    RawTermEvaluationCertificate M output targetValue
      targetAssignmentCode targetAssignmentStep ->
    sourceValue = targetValue.
Proof.
  intros M hPA cutoff amount sourceBound input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace) hrelation hinputBound
    sourceValue targetValue hsourceEvaluation htargetEvaluation.
  destruct htrace as
    (hsourceDefined & htargetDefined & hroot & hrootLookup & hrows & _).
  exact (raw_termOperationTrace_evaluation_values_agree M hPA
    (RawCodedTermShiftVariableRow M cutoff amount)
    sourceBound sourceCode sourceStep targetCode targetStep
    bound rootIndex input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsourceDefined htargetDefined hroot hrootLookup hrows
    (raw_termShiftVariableEvaluationCompatible M hPA
      cutoff amount sourceBound
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep hrelation)
    sourceValue targetValue hinputBound
    hsourceEvaluation htargetEvaluation).
Qed.

(** Shifting by zero at cutoff zero is semantically the identity even for a
    nonstandard operation trace.  We phrase the fact as an assignment-graph
    lemma, then feed it to the generic evaluator theorem above. *)
Lemma raw_codedFormulaZeroShiftAssignmentRelation_refl : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    bound assignmentCode assignmentStep,
  RawCodedFormulaShiftAssignmentRelation M
    (raw_zero M) (raw_zero M) bound
    assignmentCode assignmentStep assignmentCode assignmentStep.
Proof.
  intros M hPA bound assignmentCode assignmentStep
    inputIndex outputIndex value _ hshifted.
  destruct hshifted as [[himpossible _] | [_ houtput]].
  - exfalso. exact (raw_not_lt_zero M hPA inputIndex himpossible).
  - assert (houtputIndex : outputIndex = inputIndex).
    {
      rewrite houtput.
      apply raw_add_zero_right_operationTransport. exact hPA.
    }
    rewrite houtputIndex. reflexivity.
Qed.

Theorem raw_codedTermShift_zero_evaluation_values_agree : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    input output assignmentCode assignmentStep,
  RawCodedTermShift M (raw_zero M) (raw_zero M) input output ->
  forall sourceValue targetValue,
    RawTermEvaluationCertificate M input sourceValue
      assignmentCode assignmentStep ->
    RawTermEvaluationCertificate M output targetValue
      assignmentCode assignmentStep ->
    sourceValue = targetValue.
Proof.
  intros M hPA input output assignmentCode assignmentStep
    hshift sourceValue targetValue hsource htarget.
  apply (raw_codedTermShift_evaluation_values_agree M hPA
    (raw_zero M) (raw_zero M) (raw_succ M input) input output
    assignmentCode assignmentStep assignmentCode assignmentStep
    hshift).
  - apply raw_codedFormulaZeroShiftAssignmentRelation_refl. exact hPA.
  - exact (raw_assignment_lt_self_succ M hPA input).
  - exact hsource.
  - exact htarget.
Qed.

(** Opening at cutoff zero is the atomic operation used by a single
    substitution at the root.  The public substitution environment says
    that the source assignment is the target assignment with the value of
    the replacement prepended.  Notice that the proof below does not invert
    the beta prepend outside its advertised bound.  In the tail case it
    instead lifts the lookup already supplied by the target evaluator and
    then uses functionality on the source table.  This distinction matters
    in a nonstandard model, where beta tables may contain arbitrary rows
    beyond their certified prefix. *)
Lemma raw_termOpeningZeroVariableEvaluationCompatible_of_prepend : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacement liftedReplacement replacementValue sourceBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedTermShift M (raw_zero M) (raw_zero M)
    replacement liftedReplacement ->
  RawTermEvaluationCertificate M replacement replacementValue
    targetAssignmentCode targetAssignmentStep ->
  RawCodedAssignmentPrepend M
    targetAssignmentCode targetAssignmentStep replacementValue sourceBound
    sourceAssignmentCode sourceAssignmentStep ->
  RawTermOperationVariableEvaluationCompatible M
    (RawCodedTermOpeningVariableRow M
      (raw_zero M) liftedReplacement) sourceBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA replacement liftedReplacement replacementValue sourceBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hreplacementShift hreplacement hprepend
    input output sourceValue targetValue
    (inputIndex & hinput & hcases) hinputBound
    hsourceEvaluation htargetEvaluation.
  subst input.
  pose proof (raw_termEvaluationCertificate_var_view M hPA
    inputIndex sourceValue sourceAssignmentCode sourceAssignmentStep
    hsourceEvaluation) as hsourceLookup.
  destruct hcases as
    [[hbelow houtput] | [[hequal houtput] |
      (predecessor & hsuccessor & _ & houtput)]].
  - exfalso. exact (raw_not_lt_zero M hPA inputIndex hbelow).
  - subst inputIndex. subst output.
    pose proof (proj1
      (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
        targetAssignmentCode targetAssignmentStep replacementValue
        sourceBound sourceAssignmentCode sourceAssignmentStep
        sourceValue hprepend) hsourceLookup) as hsourceValue.
    subst sourceValue.
    exact (raw_codedTermShift_zero_evaluation_values_agree M hPA
      replacement liftedReplacement
      targetAssignmentCode targetAssignmentStep hreplacementShift
      replacementValue targetValue hreplacement htargetEvaluation).
  - subst inputIndex. subst output.
    pose proof (raw_termEvaluationCertificate_var_view M hPA
      predecessor targetValue targetAssignmentCode targetAssignmentStep
      htargetEvaluation) as htargetLookup.
    assert (hpredecessorBound : rawLt M predecessor sourceBound).
    {
      assert (hsuccessorCode : rawLt M (raw_succ M predecessor)
          (rawTermVarCode M (raw_succ M predecessor))).
      {
        change (rawLt M (raw_succ M predecessor)
          (rawListCode M
            [rawNumeralValue M 0; raw_succ M predecessor])).
        apply rawProofListCode_member_lt; [exact hPA |].
        simpl. tauto.
      }
      exact (raw_assignment_lt_trans M hPA predecessor
        (rawTermVarCode M (raw_succ M predecessor)) sourceBound
        (raw_assignment_lt_trans M hPA predecessor
          (raw_succ M predecessor)
          (rawTermVarCode M (raw_succ M predecessor))
          (raw_assignment_lt_self_succ M hPA predecessor)
          hsuccessorCode)
        hinputBound).
    }
    pose proof (raw_codedAssignmentPrepend_tail M
      targetAssignmentCode targetAssignmentStep replacementValue
      sourceBound sourceAssignmentCode sourceAssignmentStep
      predecessor targetValue hprepend hpredecessorBound htargetLookup)
      as hsourceTargetValue.
    exact (raw_codedAssignmentLookup_functional M hPA
      sourceAssignmentCode sourceAssignmentStep
      (raw_succ M predecessor) sourceValue targetValue
      hsourceLookup hsourceTargetValue).
Qed.

Theorem raw_codedTermOpening_zero_evaluation_values_agree_of_prepend : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacement liftedReplacement replacementValue sourceBound input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedTermOpening M (raw_zero M) liftedReplacement input output ->
  RawCodedTermShift M (raw_zero M) (raw_zero M)
    replacement liftedReplacement ->
  RawTermEvaluationCertificate M replacement replacementValue
    targetAssignmentCode targetAssignmentStep ->
  RawCodedAssignmentPrepend M
    targetAssignmentCode targetAssignmentStep replacementValue sourceBound
    sourceAssignmentCode sourceAssignmentStep ->
  rawLt M input sourceBound ->
  forall sourceValue targetValue,
    RawTermEvaluationCertificate M input sourceValue
      sourceAssignmentCode sourceAssignmentStep ->
    RawTermEvaluationCertificate M output targetValue
      targetAssignmentCode targetAssignmentStep ->
    sourceValue = targetValue.
Proof.
  intros M hPA replacement liftedReplacement replacementValue
    sourceBound input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace)
    hreplacementShift hreplacement hprepend hinputBound
    sourceValue targetValue hsourceEvaluation htargetEvaluation.
  destruct htrace as
    (hsourceDefined & htargetDefined & hroot & hrootLookup & hrows).
  exact (raw_termOperationTrace_evaluation_values_agree M hPA
    (RawCodedTermOpeningVariableRow M
      (raw_zero M) liftedReplacement)
    sourceBound sourceCode sourceStep targetCode targetStep
    bound rootIndex input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsourceDefined htargetDefined hroot hrootLookup hrows
    (raw_termOpeningZeroVariableEvaluationCompatible_of_prepend M hPA
      replacement liftedReplacement replacementValue sourceBound
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      hreplacementShift hreplacement hprepend)
    sourceValue targetValue hinputBound
    hsourceEvaluation htargetEvaluation).
Qed.

(** ------------------------------------------------------------------
    Atomic formula rows.

    A public rank-zero certificate hides its term table.  The next view is
    the equality analogue of the Boolean views in the elimination module:
    it opens only the root closed step and returns complete public evaluator
    certificates for the two terms. *)
Lemma raw_rankZeroTruthCertificate_eq_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    code output assignmentCode assignmentStep left right,
  code = rawFormulaEqCode M left right ->
  RawRankZeroTruthCertificate M code output
    assignmentCode assignmentStep ->
  exists leftValue rightValue : M,
    RawTermEvaluationCertificate M left leftValue
      assignmentCode assignmentStep /\
    RawTermEvaluationCertificate M right rightValue
      assignmentCode assignmentStep /\
    RawEqualityTruth M output leftValue rightValue.
Proof.
  intros M hPA code output assignmentCode assignmentStep left right
    hcode hcertificate.
  destruct (raw_rankZeroTruthCertificate_root_closed_step M hPA
    code output assignmentCode assignmentStep hcertificate) as
    (supportCode & supportStep & truthCode & truthStep &
     actualLeft & leftValue & actualRight & rightValue & hrow).
  destruct hrow as [heq | [hbot | [himp | [hand | hor]]]].
  - destruct heq as [hactual [hleft [hright htruth]]].
    assert (hcodes : rawFormulaEqCode M actualLeft actualRight =
        rawFormulaEqCode M left right).
    { exact (eq_trans (eq_sym hactual) hcode). }
    unfold rawFormulaEqCode in hcodes.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcodes) as [_ [hleftCode hrightCode]].
    subst actualLeft. subst actualRight.
    exists leftValue, rightValue. tauto.
  - destruct hbot as [hactual _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym hactual) hcode).
  - destruct himp as [himp _]. destruct himp as [hactual _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      0 2 left right actualLeft actualRight
      (eq_trans (eq_sym hcode) hactual)). discriminate.
  - destruct hand as [hand _]. destruct hand as [hactual _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      0 3 left right actualLeft actualRight
      (eq_trans (eq_sym hcode) hactual)). discriminate.
  - destruct hor as [hor _]. destruct hor as [hactual _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      0 4 left right actualLeft actualRight
      (eq_trans (eq_sym hcode) hactual)). discriminate.
Qed.

Lemma raw_rankZeroTruthCertificate_bot_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    code output assignmentCode assignmentStep,
  code = rawFormulaBotCode M ->
  RawRankZeroTruthCertificate M code output
    assignmentCode assignmentStep ->
  output = raw_zero M.
Proof.
  intros M hPA code output assignmentCode assignmentStep hcode hcertificate.
  destruct (raw_rankZeroTruthCertificate_root_closed_step M hPA
    code output assignmentCode assignmentStep hcertificate) as
    (supportCode & supportStep & truthCode & truthStep &
     left & leftValue & right & rightValue & hrow).
  destruct hrow as [heq | [hbot | [himp | [hand | hor]]]].
  - destruct heq as [hactual _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym hcode) hactual).
  - exact (proj2 hbot).
  - destruct himp as [himp _]. destruct himp as [hactual _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 2) left right).
    exact (eq_trans (eq_sym hcode) hactual).
  - destruct hand as [hand _]. destruct hand as [hactual _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 3) left right).
    exact (eq_trans (eq_sym hcode) hactual).
  - destruct hor as [hor _]. destruct hor as [hactual _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 4) left right).
    exact (eq_trans (eq_sym hcode) hactual).
Qed.

Lemma raw_rankZeroTruthCertificate_unary_false : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (constructor : M -> M) tag code child output
    assignmentCode assignmentStep,
  (forall child', constructor child' =
      rawCodeList2 M (rawNumeralValue M tag) child') ->
  code = constructor child ->
  RawRankZeroTruthCertificate M code output
    assignmentCode assignmentStep -> False.
Proof.
  intros M hPA constructor tag code child output
    assignmentCode assignmentStep hconstructor hcode hcertificate.
  destruct (raw_rankZeroTruthCertificate_root_closed_step M hPA
    code output assignmentCode assignmentStep hcertificate) as
    (supportCode & supportStep & truthCode & truthStep &
     left & leftValue & right & rightValue & hrow).
  destruct hrow as [heq | [hbot | [himp | [hand | hor]]]].
  - destruct heq as [hactual _].
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M tag) child
      (rawNumeralValue M 0) left right).
    rewrite <- hconstructor. exact (eq_trans (eq_sym hcode) hactual).
  - destruct hbot as [hactual _].
    apply (raw_codeList1_neq_codeList2 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M tag) child).
    rewrite <- hconstructor. exact (eq_trans (eq_sym hactual) hcode).
  - destruct himp as [himp _]. destruct himp as [hactual _].
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M tag) child
      (rawNumeralValue M 2) left right).
    rewrite <- hconstructor. exact (eq_trans (eq_sym hcode) hactual).
  - destruct hand as [hand _]. destruct hand as [hactual _].
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M tag) child
      (rawNumeralValue M 3) left right).
    rewrite <- hconstructor. exact (eq_trans (eq_sym hcode) hactual).
  - destruct hor as [hor _]. destruct hor as [hactual _].
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M tag) child
      (rawNumeralValue M 4) left right).
    rewrite <- hconstructor. exact (eq_trans (eq_sym hcode) hactual).
Qed.

Corollary raw_rankZeroTruthCertificate_all_false : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    code child output assignmentCode assignmentStep,
  code = rawFormulaAllCode M child ->
  RawRankZeroTruthCertificate M code output
    assignmentCode assignmentStep -> False.
Proof.
  intros M hPA code child output assignmentCode assignmentStep.
  apply (raw_rankZeroTruthCertificate_unary_false M hPA
    (rawFormulaAllCode M) 5 code child output
    assignmentCode assignmentStep).
  intro child'. reflexivity.
Qed.

Corollary raw_rankZeroTruthCertificate_ex_false : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    code child output assignmentCode assignmentStep,
  code = rawFormulaExCode M child ->
  RawRankZeroTruthCertificate M code output
    assignmentCode assignmentStep -> False.
Proof.
  intros M hPA code child output assignmentCode assignmentStep.
  apply (raw_rankZeroTruthCertificate_unary_false M hPA
    (rawFormulaExCode M) 6 code child output
    assignmentCode assignmentStep).
  intro child'. reflexivity.
Qed.

Lemma raw_formulaEq_left_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  rawLt M left (rawFormulaEqCode M left right).
Proof.
  intros M hPA left right.
  change (rawLt M left
    (rawListCode M [rawNumeralValue M 0; left; right])).
  apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
Qed.

Lemma raw_formulaEq_right_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  rawLt M right (rawFormulaEqCode M left right).
Proof.
  intros M hPA left right.
  change (rawLt M right
    (rawListCode M [rawNumeralValue M 0; left; right])).
  apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
Qed.

(** The atomic Tarski law for formula shift.  Both truth certificates are
    already present, so evaluator transport only has to identify their two
    term values; functionality of the equality truth bit then identifies the
    root outputs. *)
Theorem raw_formulaShiftEqOperationRow_rankZero_outputs_agree : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount source target sourceOutput targetOutput
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaEqOperationRow M (RawCodedFormulaShiftAtom M)
    amount cutoff source target ->
  RawCodedFormulaShiftAssignmentRelation M cutoff amount source
    sourceAssignmentCode sourceAssignmentStep
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
    hassignments hsourceCertificate htargetCertificate.
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
    apply (raw_codedTermShift_evaluation_values_agree M hPA
      cutoff amount source sourceLeft targetLeft
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      hleftShift hassignments).
    - rewrite hsource. apply raw_formulaEq_left_lt. exact hPA.
    - exact hsourceLeft.
    - exact htargetLeft.
  }
  assert (hrightValue : sourceRightValue = targetRightValue).
  {
    apply (raw_codedTermShift_evaluation_values_agree M hPA
      cutoff amount source sourceRight targetRight
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      hrightShift hassignments).
    - rewrite hsource. apply raw_formulaEq_right_lt. exact hPA.
    - exact hsourceRight.
    - exact htargetRight.
  }
  subst targetLeftValue. subst targetRightValue.
  exact (raw_equalityTruth_functional M
    sourceLeftValue sourceRightValue sourceOutput targetOutput
    hsourceTruth htargetTruth).
Qed.

(** The root equality law for single substitution.  Each atomic operation
    first zero-shifts the replacement and then opens one term.  The two
    evaluator lemmas above match that exact trace decomposition. *)
Theorem raw_formulaSubstitutionEqOperationRow_zero_rankZero_outputs_agree :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    replacement source target sourceOutput targetOutput
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaEqOperationRow M (RawCodedFormulaSubstitutionAtom M)
    replacement (raw_zero M) source target ->
  RawCodedFormulaSubstitutionAssignmentRelation M replacement source
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawRankZeroTruthCertificate M source sourceOutput
    sourceAssignmentCode sourceAssignmentStep ->
  RawRankZeroTruthCertificate M target targetOutput
    targetAssignmentCode targetAssignmentStep ->
  sourceOutput = targetOutput.
Proof.
  intros M hPA replacement source target sourceOutput targetOutput
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (sourceLeft & targetLeft & sourceRight & targetRight &
     hsource & htarget &
     (liftedLeft & hleftLift & hleftOpen) &
     (liftedRight & hrightLift & hrightOpen))
    (replacementValue & hreplacement & hprepend)
    hsourceCertificate htargetCertificate.
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
    apply (raw_codedTermOpening_zero_evaluation_values_agree_of_prepend
      M hPA replacement liftedLeft replacementValue source
      sourceLeft targetLeft
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      hleftOpen hleftLift hreplacement hprepend).
    - rewrite hsource. apply raw_formulaEq_left_lt. exact hPA.
    - exact hsourceLeft.
    - exact htargetLeft.
  }
  assert (hrightValue : sourceRightValue = targetRightValue).
  {
    apply (raw_codedTermOpening_zero_evaluation_values_agree_of_prepend
      M hPA replacement liftedRight replacementValue source
      sourceRight targetRight
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      hrightOpen hrightLift hreplacement hprepend).
    - rewrite hsource. apply raw_formulaEq_right_lt. exact hPA.
    - exact hsourceRight.
    - exact htargetRight.
  }
  subst targetLeftValue. subst targetRightValue.
  exact (raw_equalityTruth_functional M
    sourceLeftValue sourceRightValue sourceOutput targetOutput
    hsourceTruth htargetTruth).
Qed.

(** ------------------------------------------------------------------
    Rank-zero formula-operation Tarski induction.

    Formula-operation traces are beta tables whose indices may be
    nonstandard.  Consequently the following recursion cannot be a Coq
    induction over syntax.  Its invariant is represented by a PA formula
    and discharged with model-internal induction, just as for the paired
    term evaluator above.  The source-code guard excludes unrelated rows in
    an otherwise valid operation table; the depth equality records that a
    rank-zero Boolean path never crosses a binder. *)

Definition operationTarskiAll6 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll body))))).

Definition formulaOperationRankZeroAgreementBelowTermAt
    (current cutoff sourceRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  operationTarskiAll6
    (pImp
      (Formula.ltTermAt (tVar 5) (liftTerm 6 current))
      (pImp
        (codedFormulaOperationTripleLookupTermAt
          (liftTerm 6 sourceCode) (liftTerm 6 sourceStep)
          (liftTerm 6 targetCode) (liftTerm 6 targetStep)
          (liftTerm 6 depthCode) (liftTerm 6 depthStep)
          (tVar 5) (tVar 4) (tVar 3) (tVar 2))
        (pImp
          (Formula.ltTermAt (tVar 4) (liftTerm 6 sourceRoot))
          (pImp
            (pEq (tVar 2) (liftTerm 6 cutoff))
            (pImp
              (rankZeroTruthCertificateTermAt
                (tVar 4) (tVar 1)
                (liftTerm 6 sourceAssignmentCode)
                (liftTerm 6 sourceAssignmentStep))
              (pImp
                (rankZeroTruthCertificateTermAt
                  (tVar 3) (tVar 0)
                  (liftTerm 6 targetAssignmentCode)
                  (liftTerm 6 targetAssignmentStep))
                (pEq (tVar 1) (tVar 0)))))))).

Definition RawFormulaOperationRankZeroAgreementBelow (M : RawPAModel)
    (current cutoff sourceRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  forall index input output depth sourceOutput targetOutput : M,
    rawLt M index current ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth ->
    rawLt M input sourceRoot ->
    depth = cutoff ->
    RawRankZeroTruthCertificate M input sourceOutput
      sourceAssignmentCode sourceAssignmentStep ->
    RawRankZeroTruthCertificate M output targetOutput
      targetAssignmentCode targetAssignmentStep ->
    sourceOutput = targetOutput.

Arguments RawFormulaOperationRankZeroAgreementBelow
  M current cutoff sourceRoot sourceCode sourceStep
    targetCode targetStep depthCode depthStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_operationTarski_eval_liftTerm_six : forall (M : RawPAModel)
    a b c d f g (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g e))))))
    (liftTerm 6 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 6) with (S (S (S (S (S (S index)))))) by lia.
  reflexivity.
Qed.

Lemma raw_sat_formulaOperationRankZeroAgreementBelowTermAt_iff : forall
    (M : RawPAModel) e current cutoff sourceRoot
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (formulaOperationRankZeroAgreementBelowTermAt
      current cutoff sourceRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawFormulaOperationRankZeroAgreementBelow M
    (raw_term_eval M e current) (raw_term_eval M e cutoff)
    (raw_term_eval M e sourceRoot)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold formulaOperationRankZeroAgreementBelowTermAt,
    operationTarskiAll6, RawFormulaOperationRankZeroAgreementBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaOperationTripleLookupTermAt_iff.
  setoid_rewrite raw_sat_rankZeroTruthCertificateTermAt_iff.
  repeat setoid_rewrite raw_operationTarski_eval_liftTerm_six.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawFormulaOperationAtomicRankZeroAgreement (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter cutoff sourceRoot : M)
    (sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  forall input output depth sourceOutput targetOutput : M,
    RawCodedFormulaEqOperationRow M atom
      parameter depth input output ->
    rawLt M input sourceRoot ->
    depth = cutoff ->
    RawRankZeroTruthCertificate M input sourceOutput
      sourceAssignmentCode sourceAssignmentStep ->
    RawRankZeroTruthCertificate M output targetOutput
      targetAssignmentCode targetAssignmentStep ->
    sourceOutput = targetOutput.

Arguments RawFormulaOperationAtomicRankZeroAgreement
  M atom parameter cutoff sourceRoot
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_formulaBinary_left_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag left right,
  rawLt M left (rawCodeList3 M tag left right).
Proof.
  intros M hPA tag left right. unfold rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
Qed.

Lemma raw_formulaBinary_right_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag left right,
  rawLt M right (rawCodeList3 M tag left right).
Proof.
  intros M hPA tag left right. unfold rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
Qed.

Lemma raw_formulaOperationRankZeroAgreementBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (atom : M -> M -> M -> M -> Prop)
    parameter cutoff sourceRoot sourceCode sourceStep
    targetCode targetStep depthCode depthStep bound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep current,
  RawCodedFormulaOperationRows M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound ->
  RawFormulaOperationAtomicRankZeroAgreement M atom
    parameter cutoff sourceRoot
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  rawLt M current bound ->
  RawFormulaOperationRankZeroAgreementBelow M current cutoff sourceRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFormulaOperationRankZeroAgreementBelow M (raw_succ M current)
    cutoff sourceRoot sourceCode sourceStep targetCode targetStep
    depthCode depthStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA atom parameter cutoff sourceRoot sourceCode sourceStep
    targetCode targetStep depthCode depthStep bound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep current
    hrows hatomic hcurrent hagree
    index input output depth sourceOutput targetOutput
    hindex hlookup hinputBound hdepth
    hsourceCertificate htargetCertificate.
  destruct (raw_lt_succ_cases M hPA index current hindex)
    as [hbelow | heq].
  - exact (hagree index input output depth sourceOutput targetOutput
      hbelow hlookup hinputBound hdepth
      hsourceCertificate htargetCertificate).
  - subst index.
    pose proof (hrows current input output depth hcurrent hlookup) as hrow.
    destruct hrow as
      [heqRow | [hbotRow | [himpRow | [handRow |
        [horRow | [hallRow | hexRow]]]]]].
    + exact (hatomic input output depth sourceOutput targetOutput
        heqRow hinputBound hdepth
        hsourceCertificate htargetCertificate).
    + destruct hbotRow as [hinput houtput].
      rewrite (raw_rankZeroTruthCertificate_bot_view M hPA
        input sourceOutput sourceAssignmentCode sourceAssignmentStep
        hinput hsourceCertificate).
      rewrite (raw_rankZeroTruthCertificate_bot_view M hPA
        output targetOutput targetAssignmentCode targetAssignmentStep
        houtput htargetCertificate).
      reflexivity.
    + destruct himpRow as
        (leftIndex & inputLeft & outputLeft & leftDepth &
         rightIndex & inputRight & outputRight & rightDepth &
         hleftIndex & hleftLookup & hleftDepth &
         hrightIndex & hrightLookup & hrightDepth & hinput & houtput).
      destruct (raw_rankZeroTruthCertificate_imp_view M hPA
        input sourceOutput sourceAssignmentCode sourceAssignmentStep
        inputLeft inputRight hinput hsourceCertificate) as
        (sourceLeftOutput & sourceRightOutput &
         hsourceLeft & hsourceRight & hsourceTruth).
      destruct (raw_rankZeroTruthCertificate_imp_view M hPA
        output targetOutput targetAssignmentCode targetAssignmentStep
        outputLeft outputRight houtput htargetCertificate) as
        (targetLeftOutput & targetRightOutput &
         htargetLeft & htargetRight & htargetTruth).
      assert (hleftOutput : sourceLeftOutput = targetLeftOutput).
      {
        apply (hagree leftIndex inputLeft outputLeft leftDepth
          sourceLeftOutput targetLeftOutput hleftIndex hleftLookup).
        - apply (raw_assignment_lt_trans M hPA inputLeft input sourceRoot).
          + rewrite hinput. apply raw_formulaBinary_left_lt. exact hPA.
          + exact hinputBound.
        - rewrite hleftDepth. exact hdepth.
        - exact hsourceLeft.
        - exact htargetLeft.
      }
      assert (hrightOutput : sourceRightOutput = targetRightOutput).
      {
        apply (hagree rightIndex inputRight outputRight rightDepth
          sourceRightOutput targetRightOutput hrightIndex hrightLookup).
        - apply (raw_assignment_lt_trans M hPA inputRight input sourceRoot).
          + rewrite hinput. apply raw_formulaBinary_right_lt. exact hPA.
          + exact hinputBound.
        - rewrite hrightDepth. exact hdepth.
        - exact hsourceRight.
        - exact htargetRight.
      }
      subst targetLeftOutput. subst targetRightOutput.
      exact (raw_impTruth_functional M hPA sourceLeftOutput sourceRightOutput
        sourceOutput targetOutput hsourceTruth htargetTruth).
    + destruct handRow as
        (leftIndex & inputLeft & outputLeft & leftDepth &
         rightIndex & inputRight & outputRight & rightDepth &
         hleftIndex & hleftLookup & hleftDepth &
         hrightIndex & hrightLookup & hrightDepth & hinput & houtput).
      destruct (raw_rankZeroTruthCertificate_and_view M hPA
        input sourceOutput sourceAssignmentCode sourceAssignmentStep
        inputLeft inputRight hinput hsourceCertificate) as
        (sourceLeftOutput & sourceRightOutput &
         hsourceLeft & hsourceRight & hsourceTruth).
      destruct (raw_rankZeroTruthCertificate_and_view M hPA
        output targetOutput targetAssignmentCode targetAssignmentStep
        outputLeft outputRight houtput htargetCertificate) as
        (targetLeftOutput & targetRightOutput &
         htargetLeft & htargetRight & htargetTruth).
      assert (hleftOutput : sourceLeftOutput = targetLeftOutput).
      {
        apply (hagree leftIndex inputLeft outputLeft leftDepth
          sourceLeftOutput targetLeftOutput hleftIndex hleftLookup).
        - apply (raw_assignment_lt_trans M hPA inputLeft input sourceRoot).
          + rewrite hinput. apply raw_formulaBinary_left_lt. exact hPA.
          + exact hinputBound.
        - rewrite hleftDepth. exact hdepth.
        - exact hsourceLeft.
        - exact htargetLeft.
      }
      assert (hrightOutput : sourceRightOutput = targetRightOutput).
      {
        apply (hagree rightIndex inputRight outputRight rightDepth
          sourceRightOutput targetRightOutput hrightIndex hrightLookup).
        - apply (raw_assignment_lt_trans M hPA inputRight input sourceRoot).
          + rewrite hinput. apply raw_formulaBinary_right_lt. exact hPA.
          + exact hinputBound.
        - rewrite hrightDepth. exact hdepth.
        - exact hsourceRight.
        - exact htargetRight.
      }
      subst targetLeftOutput. subst targetRightOutput.
      exact (raw_andTruth_functional M hPA sourceLeftOutput sourceRightOutput
        sourceOutput targetOutput hsourceTruth htargetTruth).
    + destruct horRow as
        (leftIndex & inputLeft & outputLeft & leftDepth &
         rightIndex & inputRight & outputRight & rightDepth &
         hleftIndex & hleftLookup & hleftDepth &
         hrightIndex & hrightLookup & hrightDepth & hinput & houtput).
      destruct (raw_rankZeroTruthCertificate_or_view M hPA
        input sourceOutput sourceAssignmentCode sourceAssignmentStep
        inputLeft inputRight hinput hsourceCertificate) as
        (sourceLeftOutput & sourceRightOutput &
         hsourceLeft & hsourceRight & hsourceTruth).
      destruct (raw_rankZeroTruthCertificate_or_view M hPA
        output targetOutput targetAssignmentCode targetAssignmentStep
        outputLeft outputRight houtput htargetCertificate) as
        (targetLeftOutput & targetRightOutput &
         htargetLeft & htargetRight & htargetTruth).
      assert (hleftOutput : sourceLeftOutput = targetLeftOutput).
      {
        apply (hagree leftIndex inputLeft outputLeft leftDepth
          sourceLeftOutput targetLeftOutput hleftIndex hleftLookup).
        - apply (raw_assignment_lt_trans M hPA inputLeft input sourceRoot).
          + rewrite hinput. apply raw_formulaBinary_left_lt. exact hPA.
          + exact hinputBound.
        - rewrite hleftDepth. exact hdepth.
        - exact hsourceLeft.
        - exact htargetLeft.
      }
      assert (hrightOutput : sourceRightOutput = targetRightOutput).
      {
        apply (hagree rightIndex inputRight outputRight rightDepth
          sourceRightOutput targetRightOutput hrightIndex hrightLookup).
        - apply (raw_assignment_lt_trans M hPA inputRight input sourceRoot).
          + rewrite hinput. apply raw_formulaBinary_right_lt. exact hPA.
          + exact hinputBound.
        - rewrite hrightDepth. exact hdepth.
        - exact hsourceRight.
        - exact htargetRight.
      }
      subst targetLeftOutput. subst targetRightOutput.
      exact (raw_orTruth_functional M hPA sourceLeftOutput sourceRightOutput
        sourceOutput targetOutput hsourceTruth htargetTruth).
    + destruct hallRow as
        (childIndex & inputChild & outputChild & childDepth &
         _ & _ & _ & hinput & _).
      exfalso. exact (raw_rankZeroTruthCertificate_all_false M hPA
        input inputChild sourceOutput
        sourceAssignmentCode sourceAssignmentStep
        hinput hsourceCertificate).
    + destruct hexRow as
        (childIndex & inputChild & outputChild & childDepth &
         _ & _ & _ & hinput & _).
      exfalso. exact (raw_rankZeroTruthCertificate_ex_false M hPA
        input inputChild sourceOutput
        sourceAssignmentCode sourceAssignmentStep
        hinput hsourceCertificate).
Qed.

Definition formulaOperationRankZeroAgreementThroughTermAt
    (current limit cutoff sourceRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  pImp (Formula.leTermAt current limit)
    (formulaOperationRankZeroAgreementBelowTermAt
      current cutoff sourceRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep).

Definition RawFormulaOperationRankZeroAgreementThrough (M : RawPAModel)
    (current limit cutoff sourceRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  rawLe M current limit ->
  RawFormulaOperationRankZeroAgreementBelow M current cutoff sourceRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.

Lemma raw_sat_formulaOperationRankZeroAgreementThroughTermAt_iff : forall
    (M : RawPAModel) e current limit cutoff sourceRoot
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (formulaOperationRankZeroAgreementThroughTermAt
      current limit cutoff sourceRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawFormulaOperationRankZeroAgreementThrough M
    (raw_term_eval M e current) (raw_term_eval M e limit)
    (raw_term_eval M e cutoff) (raw_term_eval M e sourceRoot)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold formulaOperationRankZeroAgreementThroughTermAt,
    RawFormulaOperationRankZeroAgreementThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_traversal,
    raw_sat_formulaOperationRankZeroAgreementBelowTermAt_iff.
  tauto.
Qed.

Theorem raw_formulaOperationRankZeroAgreementBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (atom : M -> M -> M -> M -> Prop)
    parameter cutoff sourceRoot sourceCode sourceStep
    targetCode targetStep depthCode depthStep bound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaOperationRows M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound ->
  RawFormulaOperationAtomicRankZeroAgreement M atom
    parameter cutoff sourceRoot
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFormulaOperationRankZeroAgreementBelow M bound cutoff sourceRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA atom parameter cutoff sourceRoot sourceCode sourceStep
    targetCode targetStep depthCode depthStep bound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hrows hatomic.
  set (parameterEnv := scons M bound (scons M cutoff
    (scons M sourceRoot (scons M sourceCode (scons M sourceStep
      (scons M targetCode (scons M targetStep
        (scons M depthCode (scons M depthStep
          (scons M sourceAssignmentCode (scons M sourceAssignmentStep
            (scons M targetAssignmentCode
              (scons M targetAssignmentStep
                (fun _ : nat => raw_zero M)))))))))))))).
  set (phi := formulaOperationRankZeroAgreementThroughTermAt
    (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
    (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11)
    (tVar 12) (tVar 13)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_formulaOperationRankZeroAgreementThroughTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11)
          (tVar 12) (tVar 13))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _. intros index input output depth sourceOutput targetOutput
        hindex.
      exfalso. exact (raw_not_lt_zero M hPA index hindex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_formulaOperationRankZeroAgreementThroughTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11)
          (tVar 12) (tVar 13)) hcurrent) as hcurrentRaw.
      apply (proj2
        (raw_sat_formulaOperationRankZeroAgreementThroughTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11)
          (tVar 12) (tVar 13))).
      unfold parameterEnv in hcurrentRaw |- *.
      cbn [raw_term_eval scons] in hcurrentRaw |- *.
      intro hsuccLe.
      assert (hcurrentLimit : rawLt M current bound).
      { exact (raw_lt_of_succ_le_traversal M hPA current bound hsuccLe). }
      exact (raw_formulaOperationRankZeroAgreementBelow_succ M hPA
        atom parameter cutoff sourceRoot sourceCode sourceStep
        targetCode targetStep depthCode depthStep bound
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep current
        hrows hatomic hcurrentLimit
        (hcurrentRaw (raw_lt_to_le M current bound hcurrentLimit))).
  }
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_formulaOperationRankZeroAgreementThroughTermAt_iff M
      (scons M bound parameterEnv)
      (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
      (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11)
      (tVar 12) (tVar 13)) (hall bound)) as hlimit.
  unfold parameterEnv in hlimit.
  cbn [raw_term_eval scons] in hlimit.
  exact (hlimit (raw_le_refl_traversal M hPA bound)).
Qed.

Theorem raw_formulaOperationTrace_rankZero_outputs_agree : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (atom : M -> M -> M -> M -> Prop)
    parameter cutoff source target
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaOperationTrace M atom parameter cutoff
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex source target ->
  RawFormulaOperationAtomicRankZeroAgreement M atom
    parameter cutoff (raw_succ M source)
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  forall sourceOutput targetOutput,
    RawRankZeroTruthCertificate M source sourceOutput
      sourceAssignmentCode sourceAssignmentStep ->
    RawRankZeroTruthCertificate M target targetOutput
      targetAssignmentCode targetAssignmentStep ->
    sourceOutput = targetOutput.
Proof.
  intros M hPA atom parameter cutoff source target
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (_ & _ & _ & hroot & hrootLookup & hrows)
    hatomic sourceOutput targetOutput hsource htarget.
  pose proof (raw_formulaOperationRankZeroAgreementBelow_all M hPA
    atom parameter cutoff (raw_succ M source)
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hrows hatomic) as hagree.
  exact (hagree rootIndex source target cutoff sourceOutput targetOutput
    hroot hrootLookup (raw_assignment_lt_self_succ M hPA source)
    eq_refl hsource htarget).
Qed.

Lemma raw_codedFormulaShiftAssignmentRelation_restrict : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount largeBound smallBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaShiftAssignmentRelation M cutoff amount largeBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  (forall index, rawLt M index smallBound ->
    rawLt M index largeBound) ->
  RawCodedFormulaShiftAssignmentRelation M cutoff amount smallBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA cutoff amount largeBound smallBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hrelation hinto
    inputIndex outputIndex value hinput.
  exact (hrelation inputIndex outputIndex value
    (hinto inputIndex hinput)).
Qed.

Lemma raw_codedFormulaSubstitutionAssignmentRelation_restrict : forall
    (M : RawPAModel) replacement largeBound smallBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaSubstitutionAssignmentRelation M replacement largeBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  (forall index, rawLt M index smallBound ->
    rawLt M index largeBound) ->
  RawCodedFormulaSubstitutionAssignmentRelation M replacement smallBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M replacement largeBound smallBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (replacementValue & hreplacement & [hhead htail]) hinto.
  exists replacementValue. split; [exact hreplacement |].
  split; [exact hhead |].
  intros index hindex value hlookup.
  exact (htail index (hinto index hindex) value hlookup).
Qed.

Lemma raw_operationInputBelowSuccRoot_into_root : forall
    (M : RawPAModel), RawPASatisfies M -> forall input root,
  rawLt M input (raw_succ M root) ->
  forall index, rawLt M index input -> rawLt M index root.
Proof.
  intros M hPA input root hinput index hindex.
  destruct (raw_lt_succ_cases M hPA input root hinput)
    as [hinputRoot | ->].
  - exact (raw_assignment_lt_trans M hPA index input root
      hindex hinputRoot).
  - exact hindex.
Qed.

Theorem raw_codedFormulaShift_rankZero_outputs_agree : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaShift M cutoff amount source target ->
  RawCodedFormulaShiftAssignmentRelation M cutoff amount source
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  forall sourceOutput targetOutput,
    RawRankZeroTruthCertificate M source sourceOutput
      sourceAssignmentCode sourceAssignmentStep ->
    RawRankZeroTruthCertificate M target targetOutput
      targetAssignmentCode targetAssignmentStep ->
    sourceOutput = targetOutput.
Proof.
  intros M hPA cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace)
    hassignments sourceOutput targetOutput hsource htarget.
  apply (raw_formulaOperationTrace_rankZero_outputs_agree M hPA
    (RawCodedFormulaShiftAtom M) amount cutoff source target
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    htrace).
  - intros input output depth inputOutput outputOutput
      heqRow hinput hdepth hinputCertificate houtputCertificate.
    subst depth.
    apply (raw_formulaShiftEqOperationRow_rankZero_outputs_agree M hPA
      cutoff amount input output inputOutput outputOutput
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep heqRow).
    + apply (raw_codedFormulaShiftAssignmentRelation_restrict M hPA
        cutoff amount source input
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep hassignments).
      exact (raw_operationInputBelowSuccRoot_into_root M hPA
        input source hinput).
    + exact hinputCertificate.
    + exact houtputCertificate.
  - exact hsource.
  - exact htarget.
Qed.

Theorem raw_codedFormulaSingleSubstitution_rankZero_outputs_agree : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaSingleSubstitution M replacement source target ->
  RawCodedFormulaSubstitutionAssignmentRelation M replacement source
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  forall sourceOutput targetOutput,
    RawRankZeroTruthCertificate M source sourceOutput
      sourceAssignmentCode sourceAssignmentStep ->
    RawRankZeroTruthCertificate M target targetOutput
      targetAssignmentCode targetAssignmentStep ->
    sourceOutput = targetOutput.
Proof.
  intros M hPA replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace)
    hassignments sourceOutput targetOutput hsource htarget.
  apply (raw_formulaOperationTrace_rankZero_outputs_agree M hPA
    (RawCodedFormulaSubstitutionAtom M) replacement (raw_zero M)
    source target sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound rootIndex
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep htrace).
  - intros input output depth inputOutput outputOutput
      heqRow hinput hdepth hinputCertificate houtputCertificate.
    subst depth.
    apply
      (raw_formulaSubstitutionEqOperationRow_zero_rankZero_outputs_agree
        M hPA replacement input output inputOutput outputOutput
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep heqRow).
    + apply (raw_codedFormulaSubstitutionAssignmentRelation_restrict M
        replacement source input
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep hassignments).
      exact (raw_operationInputBelowSuccRoot_into_root M hPA
        input source hinput).
    + exact hinputCertificate.
    + exact houtputCertificate.
  - exact hsource.
  - exact htarget.
Qed.

(** Once paired rank-zero outputs agree, level-zero fixed truth transports
    in both directions.  Totality is used only to obtain the missing
    certificate on the destination side; the agreement theorem forces its
    bit to be the requested zero or one. *)
Definition RawPairedRankZeroOutputsAgree (M : RawPAModel)
    (source target sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  forall sourceOutput targetOutput : M,
    RawRankZeroTruthCertificate M source sourceOutput
      sourceAssignmentCode sourceAssignmentStep ->
    RawRankZeroTruthCertificate M target targetOutput
      targetAssignmentCode targetAssignmentStep ->
    sourceOutput = targetOutput.

Theorem raw_fixedLevelTruthCertificateTransport_zero_of_outputs_agree :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawFixedLevelTruthAdmissible M 0
    source sourceAssignmentCode sourceAssignmentStep ->
  RawFixedLevelTruthAdmissible M 0
    target targetAssignmentCode targetAssignmentStep ->
  RawCodedFormulaRankAgreement M source target ->
  RawPairedRankZeroOutputsAgree M source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M 0 source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsourceAdmissible htargetAdmissible hranks hagree.
  pose proof (raw_fixedLevel_domains_iff_of_rankAgreement M hPA 0
    source target
    (raw_fixedLevelTruthAdmissible_wellFormed M 0 source
      sourceAssignmentCode sourceAssignmentStep hsourceAdmissible)
    (raw_fixedLevelTruthAdmissible_wellFormed M 0 target
      targetAssignmentCode targetAssignmentStep htargetAdmissible)
    hranks) as [hsigmaDomains hpiDomains].
  pose proof (raw_fixedLevelTruthAdmissible_zeroSyntaxRealizable M hPA
    source sourceAssignmentCode sourceAssignmentStep hsourceAdmissible)
    as hsourceSyntax.
  pose proof (raw_fixedLevelTruthAdmissible_zeroSyntaxRealizable M hPA
    target targetAssignmentCode targetAssignmentStep htargetAdmissible)
    as htargetSyntax.
  split.
  - split.
    + intro hsourceCertificate.
      destruct (proj1
        (raw_fixedLevelSigmaTruthCertificate_zero_iff M hPA
          source sourceAssignmentCode sourceAssignmentStep)
        hsourceCertificate) as [hsourceDomain hsourceTruth].
      destruct (raw_rankZeroTruthCertificate_exists_of_realizable_syntax
        M hPA target targetAssignmentCode targetAssignmentStep
        htargetSyntax) as [targetOutput htargetTruth].
      assert (houtput : rawNumeralValue M 1 = targetOutput).
      { exact (hagree (rawNumeralValue M 1) targetOutput
          hsourceTruth htargetTruth). }
      rewrite <- houtput in htargetTruth.
      apply (proj2 (raw_fixedLevelSigmaTruthCertificate_zero_iff M hPA
        target targetAssignmentCode targetAssignmentStep)).
      split; [exact (proj1 hsigmaDomains hsourceDomain) | exact htargetTruth].
    + intro htargetCertificate.
      destruct (proj1
        (raw_fixedLevelSigmaTruthCertificate_zero_iff M hPA
          target targetAssignmentCode targetAssignmentStep)
        htargetCertificate) as [htargetDomain htargetTruth].
      destruct (raw_rankZeroTruthCertificate_exists_of_realizable_syntax
        M hPA source sourceAssignmentCode sourceAssignmentStep
        hsourceSyntax) as [sourceOutput hsourceTruth].
      assert (houtput : sourceOutput = rawNumeralValue M 1).
      { exact (hagree sourceOutput (rawNumeralValue M 1)
          hsourceTruth htargetTruth). }
      rewrite houtput in hsourceTruth.
      apply (proj2 (raw_fixedLevelSigmaTruthCertificate_zero_iff M hPA
        source sourceAssignmentCode sourceAssignmentStep)).
      split; [exact (proj2 hsigmaDomains htargetDomain) | exact hsourceTruth].
  - split.
    + intro hsourceCertificate.
      destruct (proj1
        (raw_fixedLevelPiFalsityCertificate_zero_iff M hPA
          source sourceAssignmentCode sourceAssignmentStep)
        hsourceCertificate) as [hsourceDomain hsourceTruth].
      destruct (raw_rankZeroTruthCertificate_exists_of_realizable_syntax
        M hPA target targetAssignmentCode targetAssignmentStep
        htargetSyntax) as [targetOutput htargetTruth].
      assert (houtput : raw_zero M = targetOutput).
      { exact (hagree (raw_zero M) targetOutput
          hsourceTruth htargetTruth). }
      rewrite <- houtput in htargetTruth.
      apply (proj2 (raw_fixedLevelPiFalsityCertificate_zero_iff M hPA
        target targetAssignmentCode targetAssignmentStep)).
      split; [exact (proj1 hpiDomains hsourceDomain) | exact htargetTruth].
    + intro htargetCertificate.
      destruct (proj1
        (raw_fixedLevelPiFalsityCertificate_zero_iff M hPA
          target targetAssignmentCode targetAssignmentStep)
        htargetCertificate) as [htargetDomain htargetTruth].
      destruct (raw_rankZeroTruthCertificate_exists_of_realizable_syntax
        M hPA source sourceAssignmentCode sourceAssignmentStep
        hsourceSyntax) as [sourceOutput hsourceTruth].
      assert (houtput : sourceOutput = raw_zero M).
      { exact (hagree sourceOutput (raw_zero M)
          hsourceTruth htargetTruth). }
      rewrite houtput in hsourceTruth.
      apply (proj2 (raw_fixedLevelPiFalsityCertificate_zero_iff M hPA
        source sourceAssignmentCode sourceAssignmentStep)).
      split; [exact (proj2 hpiDomains htargetDomain) | exact hsourceTruth].
Qed.

Theorem raw_fixedLevelFormulaShiftTarskiStep_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawFixedLevelFormulaShiftTarskiStep M 0
    cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hready.
  destruct hready as
    [hoperation [hassignments [hsource [htarget hranks]]]].
  assert (htargetAdmissible : RawFixedLevelTruthAdmissible M 0
      target targetAssignmentCode targetAssignmentStep).
  {
    apply (raw_fixedLevelTruthAdmissible_transport_of_rankAgreement
      M hPA 0 source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep hranks hsource htarget).
  }
  apply (raw_fixedLevelTruthCertificateTransport_zero_of_outputs_agree
    M hPA source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsource htargetAdmissible hranks).
  intros sourceOutput targetOutput hsourceOutput htargetOutput.
  exact (raw_codedFormulaShift_rankZero_outputs_agree M hPA
    cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hoperation hassignments sourceOutput targetOutput
    hsourceOutput htargetOutput).
Qed.

Theorem raw_fixedLevelFormulaSubstitutionTarskiStep_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawFixedLevelFormulaSubstitutionTarskiStep M 0
    replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hready.
  destruct hready as
    [hoperation [hassignments [hsource [htarget hranks]]]].
  assert (htargetAdmissible : RawFixedLevelTruthAdmissible M 0
      target targetAssignmentCode targetAssignmentStep).
  {
    apply (raw_fixedLevelTruthAdmissible_transport_of_rankAgreement
      M hPA 0 source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep hranks hsource htarget).
  }
  apply (raw_fixedLevelTruthCertificateTransport_zero_of_outputs_agree
    M hPA source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsource htargetAdmissible hranks).
  intros sourceOutput targetOutput hsourceOutput htargetOutput.
  exact (raw_codedFormulaSingleSubstitution_rankZero_outputs_agree M hPA
    replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hoperation hassignments sourceOutput targetOutput
    hsourceOutput htargetOutput).
Qed.

(** The level-zero laws are themselves PA theorems.  [sealPA] supplies a
    closed sentence for raw-model completeness; universal elimination then
    recovers the displayed formula with its eight (respectively seven)
    parameters left free. *)
Definition fixedLevelFormulaShiftTarskiStepFormula_zero : formula :=
  fixedLevelFormulaShiftTarskiStepTermAt 0
    (tVar 0) (tVar 1) (tVar 2) (tVar 3)
    (tVar 4) (tVar 5) (tVar 6) (tVar 7).

Theorem fixedLevelFormulaShiftTarskiStepFormula_zero_raw_valid :
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e fixedLevelFormulaShiftTarskiStepFormula_zero.
Proof.
  intros M hPA e.
  unfold fixedLevelFormulaShiftTarskiStepFormula_zero.
  apply (proj2 (raw_sat_fixedLevelFormulaShiftTarskiStepTermAt_iff
    M e 0 (tVar 0) (tVar 1) (tVar 2) (tVar 3)
    (tVar 4) (tVar 5) (tVar 6) (tVar 7))).
  apply raw_fixedLevelFormulaShiftTarskiStep_zero. exact hPA.
Qed.

Definition fixedLevelFormulaShiftTarskiStepFormula_zero_closed : formula :=
  Formula.sealPA fixedLevelFormulaShiftTarskiStepFormula_zero.

Theorem fixedLevelFormulaShiftTarskiStepFormula_zero_closed_sentence :
  Formula.Sentence fixedLevelFormulaShiftTarskiStepFormula_zero_closed.
Proof.
  unfold fixedLevelFormulaShiftTarskiStepFormula_zero_closed.
  apply Formula.sealPA_sentence.
Qed.

Theorem fixedLevelFormulaShiftTarskiStepFormula_zero_closed_raw_valid :
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    fixedLevelFormulaShiftTarskiStepFormula_zero_closed.
Proof.
  intros M hPA e.
  unfold fixedLevelFormulaShiftTarskiStepFormula_zero_closed.
  apply (raw_formula_sat_sealPA_of_valid M). intro e'.
  exact (fixedLevelFormulaShiftTarskiStepFormula_zero_raw_valid M hPA e').
Qed.

Theorem PA_proves_fixedLevelFormulaShiftTarskiStepFormula_zero_closed :
  Formula.BProv Formula.Ax_s []
    fixedLevelFormulaShiftTarskiStepFormula_zero_closed.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact fixedLevelFormulaShiftTarskiStepFormula_zero_closed_sentence.
  - exact fixedLevelFormulaShiftTarskiStepFormula_zero_closed_raw_valid.
Qed.

Theorem PA_proves_fixedLevelFormulaShiftTarskiStepFormula_zero :
  Formula.BProv Formula.Ax_s []
    fixedLevelFormulaShiftTarskiStepFormula_zero.
Proof.
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s [] fixedLevelFormulaShiftTarskiStepFormula_zero
    (fun n => n)
    PA_proves_fixedLevelFormulaShiftTarskiStepFormula_zero_closed) as h.
  now rewrite Formula.rename_id in h.
Qed.

Definition fixedLevelFormulaSubstitutionTarskiStepFormula_zero : formula :=
  fixedLevelFormulaSubstitutionTarskiStepTermAt 0
    (tVar 0) (tVar 1) (tVar 2)
    (tVar 3) (tVar 4) (tVar 5) (tVar 6).

Theorem fixedLevelFormulaSubstitutionTarskiStepFormula_zero_raw_valid :
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    fixedLevelFormulaSubstitutionTarskiStepFormula_zero.
Proof.
  intros M hPA e.
  unfold fixedLevelFormulaSubstitutionTarskiStepFormula_zero.
  apply (proj2 (raw_sat_fixedLevelFormulaSubstitutionTarskiStepTermAt_iff
    M e 0 (tVar 0) (tVar 1) (tVar 2)
    (tVar 3) (tVar 4) (tVar 5) (tVar 6))).
  apply raw_fixedLevelFormulaSubstitutionTarskiStep_zero. exact hPA.
Qed.

Definition fixedLevelFormulaSubstitutionTarskiStepFormula_zero_closed :
    formula :=
  Formula.sealPA fixedLevelFormulaSubstitutionTarskiStepFormula_zero.

Theorem fixedLevelFormulaSubstitutionTarskiStepFormula_zero_closed_sentence :
  Formula.Sentence
    fixedLevelFormulaSubstitutionTarskiStepFormula_zero_closed.
Proof.
  unfold fixedLevelFormulaSubstitutionTarskiStepFormula_zero_closed.
  apply Formula.sealPA_sentence.
Qed.

Theorem
    fixedLevelFormulaSubstitutionTarskiStepFormula_zero_closed_raw_valid :
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    fixedLevelFormulaSubstitutionTarskiStepFormula_zero_closed.
Proof.
  intros M hPA e.
  unfold fixedLevelFormulaSubstitutionTarskiStepFormula_zero_closed.
  apply (raw_formula_sat_sealPA_of_valid M). intro e'.
  exact
    (fixedLevelFormulaSubstitutionTarskiStepFormula_zero_raw_valid M hPA e').
Qed.

Theorem
    PA_proves_fixedLevelFormulaSubstitutionTarskiStepFormula_zero_closed :
  Formula.BProv Formula.Ax_s []
    fixedLevelFormulaSubstitutionTarskiStepFormula_zero_closed.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact
      fixedLevelFormulaSubstitutionTarskiStepFormula_zero_closed_sentence.
  - exact
      fixedLevelFormulaSubstitutionTarskiStepFormula_zero_closed_raw_valid.
Qed.

Theorem PA_proves_fixedLevelFormulaSubstitutionTarskiStepFormula_zero :
  Formula.BProv Formula.Ax_s []
    fixedLevelFormulaSubstitutionTarskiStepFormula_zero.
Proof.
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s [] fixedLevelFormulaSubstitutionTarskiStepFormula_zero
    (fun n => n)
    PA_proves_fixedLevelFormulaSubstitutionTarskiStepFormula_zero_closed)
    as h.
  now rewrite Formula.rename_id in h.
Qed.

(** ------------------------------------------------------------------
    The positive-level binder invariant.

    The global assignment graph from the readiness package intentionally
    quantifies over every source index below the root code.  That graph is
    stronger than what is stable under beta prepend: a shifted *unused*
    index can lie beyond the target prepend bound, where the new beta table
    is unconstrained.  Truth transport needs only lookups belonging to the
    paired source/target terms.  The following local relation records exactly
    that condition, including both syntax-code bounds. *)
Definition RawCodedFormulaShiftAssignmentLocalCompatibility
    (M : RawPAModel)
    (cutoff amount sourceBound targetBound
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  forall inputIndex outputIndex sourceValue targetValue : M,
    rawLt M inputIndex sourceBound ->
    rawLt M outputIndex targetBound ->
    RawShiftedIndex M cutoff amount inputIndex outputIndex ->
    RawCodedAssignmentLookup M
      sourceAssignmentCode sourceAssignmentStep inputIndex sourceValue ->
    RawCodedAssignmentLookup M
      targetAssignmentCode targetAssignmentStep outputIndex targetValue ->
    sourceValue = targetValue.

Arguments RawCodedFormulaShiftAssignmentLocalCompatibility
  M cutoff amount sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_codedFormulaShiftAssignmentRelation_local : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaShiftAssignmentRelation M cutoff amount sourceBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawCodedFormulaShiftAssignmentLocalCompatibility M cutoff amount
    sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA cutoff amount sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hrelation
    inputIndex outputIndex sourceValue targetValue
    hinput _ hshift hsource htarget.
  pose proof (proj1
    (hrelation inputIndex outputIndex sourceValue hinput hshift) hsource)
    as htargetSourceValue.
  exact (raw_codedAssignmentLookup_functional M hPA
    targetAssignmentCode targetAssignmentStep outputIndex
    sourceValue targetValue htargetSourceValue htarget).
Qed.

Lemma raw_shiftedIndex_under_successors : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount inputIndex outputIndex,
  RawShiftedIndex M (raw_succ M cutoff) amount
    (raw_succ M inputIndex) outputIndex ->
  exists predecessorOutput : M,
    outputIndex = raw_succ M predecessorOutput /\
    RawShiftedIndex M cutoff amount inputIndex predecessorOutput.
Proof.
  intros M hPA cutoff amount inputIndex outputIndex
    [[hbelow houtput] | [habove houtput]].
  - assert (hinputBelow : rawLt M inputIndex cutoff).
    {
      destruct (raw_lt_succ_cases M hPA
        (raw_succ M inputIndex) cutoff hbelow) as [hstrict | hequal].
      - exact (raw_assignment_lt_trans M hPA inputIndex
          (raw_succ M inputIndex) cutoff
          (raw_assignment_lt_self_succ M hPA inputIndex) hstrict).
      - rewrite <- hequal.
        exact (raw_assignment_lt_self_succ M hPA inputIndex).
    }
    exists inputIndex. split; [exact houtput |].
    left. split; [exact hinputBelow | reflexivity].
  - assert (hinputAbove : rawLe M cutoff inputIndex).
    {
      destruct habove as [gap hgap]. exists gap.
      rewrite raw_succ_add_pair in hgap by exact hPA.
      exact (raw_succ_injective_syntax M hPA _ _ hgap).
    }
    exists (raw_add M inputIndex amount). split.
    + rewrite houtput. apply raw_succ_add_pair. exact hPA.
    + right. split; [exact hinputAbove | reflexivity].
Qed.

Lemma raw_shiftedIndex_successor_zero_output : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount outputIndex,
  RawShiftedIndex M (raw_succ M cutoff) amount
    (raw_zero M) outputIndex ->
  outputIndex = raw_zero M.
Proof.
  intros M hPA cutoff amount outputIndex
    [[_ houtput] | [himpossible _]].
  - exact houtput.
  - exfalso. exact (raw_succ_not_le_zero M hPA cutoff himpossible).
Qed.

(** Local compatibility is stable when both sides cross the same binder.
    Definedness of the old prefixes supplies canonical old values; prepend
    lifts those values, and beta functionality compares them with the values
    found in the new evaluator certificates. *)
Theorem raw_codedFormulaShiftAssignmentLocalCompatibility_prepend : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount sourceParentBound targetParentBound
    sourceChildBound targetChildBound witness
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    sourceChildAssignmentCode sourceChildAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep,
  RawCodedFormulaShiftAssignmentLocalCompatibility M cutoff amount
    sourceParentBound targetParentBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawCodedAssignmentDefinedThrough M
    sourceAssignmentCode sourceAssignmentStep sourceParentBound ->
  RawCodedAssignmentDefinedThrough M
    targetAssignmentCode targetAssignmentStep targetParentBound ->
  RawCodedAssignmentPrepend M
    sourceAssignmentCode sourceAssignmentStep witness sourceParentBound
    sourceChildAssignmentCode sourceChildAssignmentStep ->
  RawCodedAssignmentPrepend M
    targetAssignmentCode targetAssignmentStep witness targetParentBound
    targetChildAssignmentCode targetChildAssignmentStep ->
  rawLt M sourceChildBound sourceParentBound ->
  rawLt M targetChildBound targetParentBound ->
  RawCodedFormulaShiftAssignmentLocalCompatibility M
    (raw_succ M cutoff) amount sourceChildBound targetChildBound
    sourceChildAssignmentCode sourceChildAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep.
Proof.
  intros M hPA cutoff amount sourceParentBound targetParentBound
    sourceChildBound targetChildBound witness
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    sourceChildAssignmentCode sourceChildAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep
    hcompatibility hsourceDefined htargetDefined
    hsourcePrepend htargetPrepend
    hsourceChild htargetChild
    inputIndex outputIndex sourceValue targetValue
    hinputChild houtputChild hshift hsourceLookup htargetLookup.
  destruct (raw_assignment_zero_or_successor M hPA inputIndex)
    as [hzero | [predecessor hsuccessor]].
  - subst inputIndex.
    assert (houtputZero : outputIndex = raw_zero M).
    {
      exact (raw_shiftedIndex_successor_zero_output M hPA
        cutoff amount outputIndex hshift).
    }
    subst outputIndex.
    pose proof (proj1
      (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
        sourceAssignmentCode sourceAssignmentStep witness
        sourceParentBound
        sourceChildAssignmentCode sourceChildAssignmentStep
        sourceValue hsourcePrepend) hsourceLookup) as hsourceValue.
    pose proof (proj1
      (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
        targetAssignmentCode targetAssignmentStep witness
        targetParentBound
        targetChildAssignmentCode targetChildAssignmentStep
        targetValue htargetPrepend) htargetLookup) as htargetValue.
    now rewrite hsourceValue, htargetValue.
  - subst inputIndex.
    destruct (raw_shiftedIndex_under_successors M hPA
      cutoff amount predecessor outputIndex hshift) as
      (predecessorOutput & houtput & hpredecessorShift).
    subst outputIndex.
    assert (hpredecessorSource : rawLt M predecessor sourceParentBound).
    {
      apply (raw_assignment_lt_trans M hPA predecessor
        sourceChildBound sourceParentBound); [|exact hsourceChild].
      exact (raw_assignment_lt_trans M hPA predecessor
        (raw_succ M predecessor) sourceChildBound
        (raw_assignment_lt_self_succ M hPA predecessor) hinputChild).
    }
    assert (hpredecessorTarget :
        rawLt M predecessorOutput targetParentBound).
    {
      apply (raw_assignment_lt_trans M hPA predecessorOutput
        targetChildBound targetParentBound); [|exact htargetChild].
      exact (raw_assignment_lt_trans M hPA predecessorOutput
        (raw_succ M predecessorOutput) targetChildBound
        (raw_assignment_lt_self_succ M hPA predecessorOutput) houtputChild).
    }
    destruct (hsourceDefined predecessor hpredecessorSource)
      as [oldSourceValue holdSource].
    destruct (htargetDefined predecessorOutput hpredecessorTarget)
      as [oldTargetValue holdTarget].
    pose proof (raw_codedAssignmentPrepend_tail M
      sourceAssignmentCode sourceAssignmentStep witness sourceParentBound
      sourceChildAssignmentCode sourceChildAssignmentStep
      predecessor oldSourceValue hsourcePrepend
      hpredecessorSource holdSource) as hnewSource.
    pose proof (raw_codedAssignmentPrepend_tail M
      targetAssignmentCode targetAssignmentStep witness targetParentBound
      targetChildAssignmentCode targetChildAssignmentStep
      predecessorOutput oldTargetValue htargetPrepend
      hpredecessorTarget holdTarget) as hnewTarget.
    assert (hsourceValue : sourceValue = oldSourceValue).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        sourceChildAssignmentCode sourceChildAssignmentStep
        (raw_succ M predecessor) sourceValue oldSourceValue
        hsourceLookup hnewSource).
    }
    assert (htargetValue : targetValue = oldTargetValue).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        targetChildAssignmentCode targetChildAssignmentStep
        (raw_succ M predecessorOutput) targetValue oldTargetValue
        htargetLookup hnewTarget).
    }
    rewrite hsourceValue, htargetValue.
    exact (hcompatibility predecessor predecessorOutput
      oldSourceValue oldTargetValue
      hpredecessorSource hpredecessorTarget hpredecessorShift
      holdSource holdTarget).
Qed.

(** A two-sided version of the paired-term invariant.  The earlier theorem
    is convenient at the root, where the global assignment graph makes the
    target bound irrelevant.  Binder transport needs the target code bound
    explicitly, because prepend promises nothing about beta rows outside
    that bound. *)
Definition termOperationEvaluationAgreementBiBelowTermAt
    (current sourceBound targetBound sourceCode sourceStep
      targetCode targetStep sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  operationTarskiAll5
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 5 current))
      (pImp
        (codedTermOperationPairLookupTermAt
          (liftTerm 5 sourceCode) (liftTerm 5 sourceStep)
          (liftTerm 5 targetCode) (liftTerm 5 targetStep)
          (tVar 4) (tVar 3) (tVar 2))
        (pImp
          (Formula.ltTermAt (tVar 3) (liftTerm 5 sourceBound))
          (pImp
            (Formula.ltTermAt (tVar 2) (liftTerm 5 targetBound))
            (pImp
              (termEvaluationCertificateTermAt
                (tVar 3) (tVar 1)
                (liftTerm 5 sourceAssignmentCode)
                (liftTerm 5 sourceAssignmentStep))
              (pImp
                (termEvaluationCertificateTermAt
                  (tVar 2) (tVar 0)
                  (liftTerm 5 targetAssignmentCode)
                  (liftTerm 5 targetAssignmentStep))
                (pEq (tVar 1) (tVar 0)))))))).

Definition RawTermOperationEvaluationAgreementBiBelow (M : RawPAModel)
    (current sourceBound targetBound sourceCode sourceStep
      targetCode targetStep sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  forall index input output sourceValue targetValue : M,
    rawLt M index current ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep index input output ->
    rawLt M input sourceBound ->
    rawLt M output targetBound ->
    RawTermEvaluationCertificate M input sourceValue
      sourceAssignmentCode sourceAssignmentStep ->
    RawTermEvaluationCertificate M output targetValue
      targetAssignmentCode targetAssignmentStep ->
    sourceValue = targetValue.

Arguments RawTermOperationEvaluationAgreementBiBelow
  M current sourceBound targetBound sourceCode sourceStep
    targetCode targetStep sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_sat_termOperationEvaluationAgreementBiBelowTermAt_iff : forall
    (M : RawPAModel) e current sourceBound targetBound
      sourceCode sourceStep targetCode targetStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (termOperationEvaluationAgreementBiBelowTermAt
      current sourceBound targetBound sourceCode sourceStep
      targetCode targetStep sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawTermOperationEvaluationAgreementBiBelow M
    (raw_term_eval M e current)
    (raw_term_eval M e sourceBound) (raw_term_eval M e targetBound)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold termOperationEvaluationAgreementBiBelowTermAt,
    operationTarskiAll5, RawTermOperationEvaluationAgreementBiBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_termEvaluationCertificateTermAt_iff.
  repeat setoid_rewrite raw_operationTarski_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawTermOperationVariableEvaluationBiCompatible (M : RawPAModel)
    (variableRow : M -> M -> Prop)
    (sourceBound targetBound : M)
    (sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  forall input output sourceValue targetValue : M,
    variableRow input output ->
    rawLt M input sourceBound ->
    rawLt M output targetBound ->
    RawTermEvaluationCertificate M input sourceValue
      sourceAssignmentCode sourceAssignmentStep ->
    RawTermEvaluationCertificate M output targetValue
      targetAssignmentCode targetAssignmentStep ->
    sourceValue = targetValue.

Arguments RawTermOperationVariableEvaluationBiCompatible
  M variableRow sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_termOperationEvaluationAgreementBiBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (variableRow : M -> M -> Prop)
    sourceBound targetBound sourceCode sourceStep targetCode targetStep limit
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep current,
  RawCodedTermOperationRows M
    (RawCodedTermOperationTraversalRow M variableRow
      sourceCode sourceStep targetCode targetStep)
    sourceCode sourceStep targetCode targetStep limit ->
  RawTermOperationVariableEvaluationBiCompatible M variableRow
    sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  rawLt M current limit ->
  RawTermOperationEvaluationAgreementBiBelow M current
    sourceBound targetBound sourceCode sourceStep targetCode targetStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawTermOperationEvaluationAgreementBiBelow M (raw_succ M current)
    sourceBound targetBound sourceCode sourceStep targetCode targetStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA variableRow sourceBound targetBound
    sourceCode sourceStep targetCode targetStep limit
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep current
    hrows hvariable hcurrent hagree
    index input output sourceValue targetValue hindex hlookup
    hinputBound houtputBound hsourceEvaluation htargetEvaluation.
  destruct (raw_lt_succ_cases M hPA index current hindex)
    as [hbelow | heq].
  - exact (hagree index input output sourceValue targetValue
      hbelow hlookup hinputBound houtputBound
      hsourceEvaluation htargetEvaluation).
  - subst index.
    pose proof (hrows current input output hcurrent hlookup) as hrow.
    destruct hrow as
      [hvariableRow | [hzero | [hsucc | [hadd | hmul]]]].
    + exact (hvariable input output sourceValue targetValue
        hvariableRow hinputBound houtputBound
        hsourceEvaluation htargetEvaluation).
    + destruct hzero as [hinput houtput]. subst input. subst output.
      rewrite (raw_termEvaluationCertificate_zero_view M hPA
        sourceValue sourceAssignmentCode sourceAssignmentStep
        hsourceEvaluation).
      rewrite (raw_termEvaluationCertificate_zero_view M hPA
        targetValue targetAssignmentCode targetAssignmentStep
        htargetEvaluation).
      reflexivity.
    + destruct hsucc as
        (childIndex & inputChild & outputChild & hchildIndex &
         hchildLookup & hinput & houtput).
      subst input. subst output.
      destruct (raw_termEvaluationCertificate_succ_view M hPA
        inputChild sourceValue sourceAssignmentCode sourceAssignmentStep
        hsourceEvaluation) as
        (sourceChildValue & hsourceChild & hsourceValue).
      destruct (raw_termEvaluationCertificate_succ_view M hPA
        outputChild targetValue targetAssignmentCode targetAssignmentStep
        htargetEvaluation) as
        (targetChildValue & htargetChild & htargetValue).
      rewrite hsourceValue, htargetValue. f_equal.
      apply (hagree childIndex inputChild outputChild
        sourceChildValue targetChildValue hchildIndex hchildLookup).
      * apply (raw_assignment_lt_trans M hPA inputChild
          (rawTermSuccCode M inputChild) sourceBound); [|exact hinputBound].
        change (rawLt M inputChild
          (rawListCode M [rawNumeralValue M 2; inputChild])).
        apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
      * apply (raw_assignment_lt_trans M hPA outputChild
          (rawTermSuccCode M outputChild) targetBound); [|exact houtputBound].
        change (rawLt M outputChild
          (rawListCode M [rawNumeralValue M 2; outputChild])).
        apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
      * exact hsourceChild.
      * exact htargetChild.
    + destruct hadd as
        (leftIndex & inputLeft & outputLeft & rightIndex &
         inputRight & outputRight & hleftIndex & hleftLookup &
         hrightIndex & hrightLookup & hinput & houtput).
      subst input. subst output.
      destruct (raw_termEvaluationCertificate_add_view M hPA
        inputLeft inputRight sourceValue
        sourceAssignmentCode sourceAssignmentStep hsourceEvaluation) as
        (sourceLeftValue & sourceRightValue &
         hsourceLeft & hsourceRight & hsourceValue).
      destruct (raw_termEvaluationCertificate_add_view M hPA
        outputLeft outputRight targetValue
        targetAssignmentCode targetAssignmentStep htargetEvaluation) as
        (targetLeftValue & targetRightValue &
         htargetLeft & htargetRight & htargetValue).
      rewrite hsourceValue, htargetValue. f_equal.
      * apply (hagree leftIndex inputLeft outputLeft
          sourceLeftValue targetLeftValue hleftIndex hleftLookup).
        -- apply (raw_assignment_lt_trans M hPA inputLeft
            (rawTermAddCode M inputLeft inputRight) sourceBound);
             [|exact hinputBound].
           change (rawLt M inputLeft
             (rawListCode M
               [rawNumeralValue M 3; inputLeft; inputRight])).
           apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
        -- apply (raw_assignment_lt_trans M hPA outputLeft
            (rawTermAddCode M outputLeft outputRight) targetBound);
             [|exact houtputBound].
           change (rawLt M outputLeft
             (rawListCode M
               [rawNumeralValue M 3; outputLeft; outputRight])).
           apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
        -- exact hsourceLeft.
        -- exact htargetLeft.
      * apply (hagree rightIndex inputRight outputRight
          sourceRightValue targetRightValue hrightIndex hrightLookup).
        -- apply (raw_assignment_lt_trans M hPA inputRight
            (rawTermAddCode M inputLeft inputRight) sourceBound);
             [|exact hinputBound].
           change (rawLt M inputRight
             (rawListCode M
               [rawNumeralValue M 3; inputLeft; inputRight])).
           apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
        -- apply (raw_assignment_lt_trans M hPA outputRight
            (rawTermAddCode M outputLeft outputRight) targetBound);
             [|exact houtputBound].
           change (rawLt M outputRight
             (rawListCode M
               [rawNumeralValue M 3; outputLeft; outputRight])).
           apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
        -- exact hsourceRight.
        -- exact htargetRight.
    + destruct hmul as
        (leftIndex & inputLeft & outputLeft & rightIndex &
         inputRight & outputRight & hleftIndex & hleftLookup &
         hrightIndex & hrightLookup & hinput & houtput).
      subst input. subst output.
      destruct (raw_termEvaluationCertificate_mul_view M hPA
        inputLeft inputRight sourceValue
        sourceAssignmentCode sourceAssignmentStep hsourceEvaluation) as
        (sourceLeftValue & sourceRightValue &
         hsourceLeft & hsourceRight & hsourceValue).
      destruct (raw_termEvaluationCertificate_mul_view M hPA
        outputLeft outputRight targetValue
        targetAssignmentCode targetAssignmentStep htargetEvaluation) as
        (targetLeftValue & targetRightValue &
         htargetLeft & htargetRight & htargetValue).
      rewrite hsourceValue, htargetValue. f_equal.
      * apply (hagree leftIndex inputLeft outputLeft
          sourceLeftValue targetLeftValue hleftIndex hleftLookup).
        -- apply (raw_assignment_lt_trans M hPA inputLeft
            (rawTermMulCode M inputLeft inputRight) sourceBound);
             [|exact hinputBound].
           change (rawLt M inputLeft
             (rawListCode M
               [rawNumeralValue M 4; inputLeft; inputRight])).
           apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
        -- apply (raw_assignment_lt_trans M hPA outputLeft
            (rawTermMulCode M outputLeft outputRight) targetBound);
             [|exact houtputBound].
           change (rawLt M outputLeft
             (rawListCode M
               [rawNumeralValue M 4; outputLeft; outputRight])).
           apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
        -- exact hsourceLeft.
        -- exact htargetLeft.
      * apply (hagree rightIndex inputRight outputRight
          sourceRightValue targetRightValue hrightIndex hrightLookup).
        -- apply (raw_assignment_lt_trans M hPA inputRight
            (rawTermMulCode M inputLeft inputRight) sourceBound);
             [|exact hinputBound].
           change (rawLt M inputRight
             (rawListCode M
               [rawNumeralValue M 4; inputLeft; inputRight])).
           apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
        -- apply (raw_assignment_lt_trans M hPA outputRight
            (rawTermMulCode M outputLeft outputRight) targetBound);
             [|exact houtputBound].
           change (rawLt M outputRight
             (rawListCode M
               [rawNumeralValue M 4; outputLeft; outputRight])).
           apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
        -- exact hsourceRight.
        -- exact htargetRight.
Qed.

Definition termOperationEvaluationAgreementBiThroughTermAt
    (current limit sourceBound targetBound sourceCode sourceStep
      targetCode targetStep sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  pImp (Formula.leTermAt current limit)
    (termOperationEvaluationAgreementBiBelowTermAt
      current sourceBound targetBound sourceCode sourceStep
      targetCode targetStep sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep).

Definition RawTermOperationEvaluationAgreementBiThrough (M : RawPAModel)
    (current limit sourceBound targetBound sourceCode sourceStep
      targetCode targetStep sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  rawLe M current limit ->
  RawTermOperationEvaluationAgreementBiBelow M current
    sourceBound targetBound sourceCode sourceStep targetCode targetStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.

Lemma raw_sat_termOperationEvaluationAgreementBiThroughTermAt_iff : forall
    (M : RawPAModel) e current limit sourceBound targetBound
      sourceCode sourceStep targetCode targetStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (termOperationEvaluationAgreementBiThroughTermAt
      current limit sourceBound targetBound sourceCode sourceStep
      targetCode targetStep sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawTermOperationEvaluationAgreementBiThrough M
    (raw_term_eval M e current) (raw_term_eval M e limit)
    (raw_term_eval M e sourceBound) (raw_term_eval M e targetBound)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold termOperationEvaluationAgreementBiThroughTermAt,
    RawTermOperationEvaluationAgreementBiThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_traversal,
    raw_sat_termOperationEvaluationAgreementBiBelowTermAt_iff.
  tauto.
Qed.

Theorem raw_termOperationEvaluationAgreementBiBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (variableRow : M -> M -> Prop)
    sourceBound targetBound sourceCode sourceStep targetCode targetStep limit
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedTermOperationRows M
    (RawCodedTermOperationTraversalRow M variableRow
      sourceCode sourceStep targetCode targetStep)
    sourceCode sourceStep targetCode targetStep limit ->
  RawTermOperationVariableEvaluationBiCompatible M variableRow
    sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawTermOperationEvaluationAgreementBiBelow M limit
    sourceBound targetBound sourceCode sourceStep targetCode targetStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA variableRow sourceBound targetBound
    sourceCode sourceStep targetCode targetStep limit
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hrows hvariable.
  set (parameterEnv := scons M limit
    (scons M sourceBound (scons M targetBound
      (scons M sourceCode (scons M sourceStep
        (scons M targetCode (scons M targetStep
          (scons M sourceAssignmentCode (scons M sourceAssignmentStep
            (scons M targetAssignmentCode (scons M targetAssignmentStep
              (fun _ : nat => raw_zero M)))))))))))).
  set (phi := termOperationEvaluationAgreementBiThroughTermAt
    (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
    (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_termOperationEvaluationAgreementBiThroughTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _. intros index input output sourceValue targetValue hindex.
      exfalso. exact (raw_not_lt_zero M hPA index hindex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_termOperationEvaluationAgreementBiThroughTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11))
        hcurrent) as hcurrentRaw.
      apply (proj2
        (raw_sat_termOperationEvaluationAgreementBiThroughTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11))).
      unfold parameterEnv in hcurrentRaw |- *.
      cbn [raw_term_eval scons] in hcurrentRaw |- *.
      intro hsuccLe.
      assert (hcurrentLimit : rawLt M current limit).
      { exact (raw_lt_of_succ_le_traversal M hPA current limit hsuccLe). }
      exact (raw_termOperationEvaluationAgreementBiBelow_succ M hPA
        variableRow sourceBound targetBound
        sourceCode sourceStep targetCode targetStep limit
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep current
        hrows hvariable hcurrentLimit
        (hcurrentRaw (raw_lt_to_le M current limit hcurrentLimit))).
  }
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_termOperationEvaluationAgreementBiThroughTermAt_iff M
      (scons M limit parameterEnv)
      (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
      (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11))
    (hall limit)) as hlimit.
  unfold parameterEnv in hlimit.
  cbn [raw_term_eval scons] in hlimit.
  exact (hlimit (raw_le_refl_traversal M hPA limit)).
Qed.

Theorem raw_termOperationTrace_evaluation_values_agree_local : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (variableRow : M -> M -> Prop)
    sourceBound targetBound sourceCode sourceStep targetCode targetStep
      bound rootIndex input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound ->
  RawCodedAssignmentDefinedThrough M targetCode targetStep bound ->
  rawLt M rootIndex bound ->
  RawCodedTermOperationPairLookup M
    sourceCode sourceStep targetCode targetStep rootIndex input output ->
  RawCodedTermOperationRows M
    (RawCodedTermOperationTraversalRow M variableRow
      sourceCode sourceStep targetCode targetStep)
    sourceCode sourceStep targetCode targetStep bound ->
  RawTermOperationVariableEvaluationBiCompatible M variableRow
    sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  forall sourceValue targetValue,
    rawLt M input sourceBound ->
    rawLt M output targetBound ->
    RawTermEvaluationCertificate M input sourceValue
      sourceAssignmentCode sourceAssignmentStep ->
    RawTermEvaluationCertificate M output targetValue
      targetAssignmentCode targetAssignmentStep ->
    sourceValue = targetValue.
Proof.
  intros M hPA variableRow sourceBound targetBound
    sourceCode sourceStep targetCode targetStep bound rootIndex input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    _ _ hroot hlookup hrows hvariable
    sourceValue targetValue hinput houtput hsource htarget.
  pose proof (raw_termOperationEvaluationAgreementBiBelow_all M hPA
    variableRow sourceBound targetBound
    sourceCode sourceStep targetCode targetStep bound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hrows hvariable) as hagree.
  exact (hagree rootIndex input output sourceValue targetValue
    hroot hlookup hinput houtput hsource htarget).
Qed.

Lemma raw_termShiftVariableEvaluationBiCompatible_local : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaShiftAssignmentLocalCompatibility M cutoff amount
    sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawTermOperationVariableEvaluationBiCompatible M
    (RawCodedTermShiftVariableRow M cutoff amount)
    sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA cutoff amount sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hcompatibility
    input output sourceValue targetValue
    (inputIndex & outputIndex & hinput & houtput & hshift)
    hinputBound houtputBound hsourceEvaluation htargetEvaluation.
  subst input. subst output.
  pose proof (raw_termEvaluationCertificate_var_view M hPA
    inputIndex sourceValue sourceAssignmentCode sourceAssignmentStep
    hsourceEvaluation) as hsourceLookup.
  pose proof (raw_termEvaluationCertificate_var_view M hPA
    outputIndex targetValue targetAssignmentCode targetAssignmentStep
    htargetEvaluation) as htargetLookup.
  apply (hcompatibility inputIndex outputIndex sourceValue targetValue).
  - apply (raw_assignment_lt_trans M hPA inputIndex
      (rawTermVarCode M inputIndex) sourceBound); [|exact hinputBound].
    change (rawLt M inputIndex
      (rawListCode M [rawNumeralValue M 0; inputIndex])).
    apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
  - apply (raw_assignment_lt_trans M hPA outputIndex
      (rawTermVarCode M outputIndex) targetBound); [|exact houtputBound].
    change (rawLt M outputIndex
      (rawListCode M [rawNumeralValue M 0; outputIndex])).
    apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
  - exact hshift.
  - exact hsourceLookup.
  - exact htargetLookup.
Qed.

Theorem raw_codedTermShift_evaluation_values_agree_local : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount sourceBound targetBound input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedTermShift M cutoff amount input output ->
  RawCodedFormulaShiftAssignmentLocalCompatibility M cutoff amount
    sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  rawLt M input sourceBound ->
  rawLt M output targetBound ->
  forall sourceValue targetValue,
    RawTermEvaluationCertificate M input sourceValue
      sourceAssignmentCode sourceAssignmentStep ->
    RawTermEvaluationCertificate M output targetValue
      targetAssignmentCode targetAssignmentStep ->
    sourceValue = targetValue.
Proof.
  intros M hPA cutoff amount sourceBound targetBound input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace)
    hcompatibility hinput houtput
    sourceValue targetValue hsource htarget.
  destruct htrace as
    (hsourceDefined & htargetDefined & hroot & hlookup & hrows & _).
  exact (raw_termOperationTrace_evaluation_values_agree_local M hPA
    (RawCodedTermShiftVariableRow M cutoff amount)
    sourceBound targetBound sourceCode sourceStep targetCode targetStep
    bound rootIndex input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsourceDefined htargetDefined hroot hlookup hrows
    (raw_termShiftVariableEvaluationBiCompatible_local M hPA
      cutoff amount sourceBound targetBound
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep hcompatibility)
    sourceValue targetValue hinput houtput hsource htarget).
Qed.

End PABoundedRawCodedFixedLevelTruthOperationTarski.
