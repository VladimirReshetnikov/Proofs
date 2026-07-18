(**
  Syntax realization for targets of arbitrary coded term-shift traces.

  Term-operation tables are indexed by occurrences, whereas the evaluator's
  syntax certificate is indexed by numeric term codes.  In a nonstandard PA
  model those two indexing schemes cannot be related by external decoding.
  We instead use PA induction to beta-code the characteristic function of
  the target column.  The structural shift rows then prove that this support
  is closed under term constructors, including at nonstandard indices.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedProofDescent RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedTermEvaluationTraversal
  RawCodedTermEvaluationRealization RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality.

Import ListNotations.

Module PABoundedRawCodedTermShiftSyntaxRealization.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.

(** A target term occurs when it is stored at some row of the target column.
    This definition intentionally ignores the source column; structural
    validity is recovered later from the shift-row predicate. *)
Definition RawTermShiftTargetOccurrence (M : RawPAModel)
    (targetCode targetStep bound code : M) : Prop :=
  exists index : M,
    rawLt M index bound /\
    RawCodedAssignmentLookup M targetCode targetStep index code.

Arguments RawTermShiftTargetOccurrence
  M targetCode targetStep bound code : clear implicits.

Definition termShiftTargetOccurrenceTermAt
    (targetCode targetStep bound code : term) : formula :=
  pEx (pAnd
    (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
    (codedAssignmentLookupTermAt
      (liftTerm 1 targetCode) (liftTerm 1 targetStep)
      (tVar 0) (liftTerm 1 code))).

Lemma raw_sat_termShiftTargetOccurrenceTermAt_iff : forall
    (M : RawPAModel) e targetCode targetStep bound code,
  raw_formula_sat M e
    (termShiftTargetOccurrenceTermAt targetCode targetStep bound code) <->
  RawTermShiftTargetOccurrence M
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e bound) (raw_term_eval M e code).
Proof.
  intros. unfold termShiftTargetOccurrenceTermAt,
    RawTermShiftTargetOccurrence.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  split; intros [index [hindex hlookup]]; exists index; split.
  - rewrite raw_term_eval_liftTerm_one_traversal in hindex.
    exact hindex.
  - repeat rewrite raw_term_eval_liftTerm_one_traversal in hlookup.
    exact hlookup.
  - rewrite raw_term_eval_liftTerm_one_traversal.
    exact hindex.
  - repeat rewrite raw_term_eval_liftTerm_one_traversal.
    exact hlookup.
Qed.

(** A characteristic beta table for target occurrences below [current]. *)
Definition RawTermShiftTargetSupportPrefix (M : RawPAModel)
    (current targetCode targetStep bound supportCode supportStep : M)
    : Prop :=
  RawCodedAssignmentDefinedThrough M supportCode supportStep current /\
  forall code : M,
    rawLt M code current ->
    (rawTermCodeSupported M supportCode supportStep code <->
     RawTermShiftTargetOccurrence M targetCode targetStep bound code).

Arguments RawTermShiftTargetSupportPrefix
  M current targetCode targetStep bound supportCode supportStep
  : clear implicits.

Definition termShiftTargetSupportPrefixTermAt
    (current targetCode targetStep bound supportCode supportStep : term)
    : formula :=
  pAnd
    (codedAssignmentDefinedThroughTermAt supportCode supportStep current)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
        (pAnd
          (pImp
            (termCodeSupportedTermAt
              (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
            (termShiftTargetOccurrenceTermAt
              (liftTerm 1 targetCode) (liftTerm 1 targetStep)
              (liftTerm 1 bound) (tVar 0)))
          (pImp
            (termShiftTargetOccurrenceTermAt
              (liftTerm 1 targetCode) (liftTerm 1 targetStep)
              (liftTerm 1 bound) (tVar 0))
            (termCodeSupportedTermAt
              (liftTerm 1 supportCode) (liftTerm 1 supportStep)
              (tVar 0)))))).

Lemma raw_sat_termShiftTargetSupportPrefixTermAt_iff : forall
    (M : RawPAModel) e current targetCode targetStep bound
      supportCode supportStep,
  raw_formula_sat M e
    (termShiftTargetSupportPrefixTermAt current targetCode targetStep bound
      supportCode supportStep) <->
  RawTermShiftTargetSupportPrefix M
    (raw_term_eval M e current)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e bound)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros. unfold termShiftTargetSupportPrefixTermAt,
    RawTermShiftTargetSupportPrefix.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_termCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_termShiftTargetOccurrenceTermAt_iff.
  repeat setoid_rewrite raw_term_eval_liftTerm_one_traversal.
  cbn [raw_term_eval scons]. tauto.
Qed.

Definition RawTermShiftTargetSupportPrefixRealizable (M : RawPAModel)
    (current targetCode targetStep bound : M) : Prop :=
  exists supportCode supportStep : M,
    RawTermShiftTargetSupportPrefix M
      current targetCode targetStep bound supportCode supportStep.

Arguments RawTermShiftTargetSupportPrefixRealizable
  M current targetCode targetStep bound : clear implicits.

Definition termShiftTargetSupportPrefixRealizableTermAt
    (current targetCode targetStep bound : term) : formula :=
  pEx (pEx
    (termShiftTargetSupportPrefixTermAt
      (liftTerm 2 current) (liftTerm 2 targetCode)
      (liftTerm 2 targetStep) (liftTerm 2 bound)
      (tVar 1) (tVar 0))).

Lemma raw_sat_termShiftTargetSupportPrefixRealizableTermAt_iff : forall
    (M : RawPAModel) e current targetCode targetStep bound,
  raw_formula_sat M e
    (termShiftTargetSupportPrefixRealizableTermAt
      current targetCode targetStep bound) <->
  RawTermShiftTargetSupportPrefixRealizable M
    (raw_term_eval M e current)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e bound).
Proof.
  intros. unfold termShiftTargetSupportPrefixRealizableTermAt,
    RawTermShiftTargetSupportPrefixRealizable.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_termShiftTargetSupportPrefixTermAt_iff.
  repeat setoid_rewrite raw_term_eval_liftTerm_two_traversal.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_termShiftTargetSupportPrefix_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    targetCode targetStep bound,
  RawTermShiftTargetSupportPrefix M
    (raw_zero M) targetCode targetStep bound
    (raw_zero M) (raw_zero M).
Proof.
  intros M hPA targetCode targetStep bound. split.
  - exact (raw_codedAssignment_empty_defined M hPA).
  - intros code hcode. exfalso.
    exact (raw_not_lt_zero M hPA code hcode).
Qed.

Lemma raw_termShiftSyntax_zero_neq_one : forall
    (M : RawPAModel), RawPASatisfies M ->
  raw_zero M <> rawNumeralValue M 1.
Proof.
  intros M hPA heq.
  change (rawNumeralValue M 0 = rawNumeralValue M 1) in heq.
  apply (rawNumeralValue_injective M hPA 0 1) in heq.
  discriminate.
Qed.

(** One append installs the occurrence bit at [current].  The old segment
    is preserved extensionally using lookup functionality. *)
Lemma raw_termShiftTargetSupportPrefix_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    current targetCode targetStep bound oldSupportCode oldSupportStep,
  RawTermShiftTargetSupportPrefix M
    current targetCode targetStep bound oldSupportCode oldSupportStep ->
  exists newSupportCode newSupportStep : M,
    RawTermShiftTargetSupportPrefix M
      (raw_succ M current) targetCode targetStep bound
      newSupportCode newSupportStep.
Proof.
  intros M hPA current targetCode targetStep bound
    oldSupportCode oldSupportStep [holdDefined holdExact].
  destruct (classic (RawTermShiftTargetOccurrence M
    targetCode targetStep bound current)) as [hoccurs | hnotOccurs].
  - destruct (raw_codedAssignmentAppend_defined_exists M hPA
      oldSupportCode oldSupportStep current (rawNumeralValue M 1)
      holdDefined) as
      (newSupportCode & newSupportStep & hnewDefined & hpreserve & hnewValue).
    exists newSupportCode, newSupportStep. split; [exact hnewDefined |].
    intros code hcode.
    destruct (raw_lt_succ_cases M hPA code current hcode)
      as [hbefore | ->].
    + split.
      * intro hnewSupported.
        destruct (holdDefined code hbefore) as [oldValue holdValue].
        assert (hpreserved : RawCodedAssignmentLookup M
            newSupportCode newSupportStep code oldValue).
        { exact (hpreserve code oldValue hbefore holdValue). }
        assert (holdValueOne : oldValue = rawNumeralValue M 1).
        {
          apply (raw_codedAssignmentLookup_functional M hPA
            newSupportCode newSupportStep code oldValue
            (rawNumeralValue M 1)); assumption.
        }
        apply (proj1 (holdExact code hbefore)).
        unfold rawTermCodeSupported.
        rewrite <- holdValueOne. exact holdValue.
      * intro hoccurrence.
        unfold rawTermCodeSupported in *.
        exact (hpreserve code (rawNumeralValue M 1) hbefore
          (proj2 (holdExact code hbefore) hoccurrence)).
    + split; [intros _; exact hoccurs | intros _].
      unfold rawTermCodeSupported. exact hnewValue.
  - destruct (raw_codedAssignmentAppend_defined_exists M hPA
      oldSupportCode oldSupportStep current (raw_zero M)
      holdDefined) as
      (newSupportCode & newSupportStep & hnewDefined & hpreserve & hnewValue).
    exists newSupportCode, newSupportStep. split; [exact hnewDefined |].
    intros code hcode.
    destruct (raw_lt_succ_cases M hPA code current hcode)
      as [hbefore | ->].
    + split.
      * intro hnewSupported.
        destruct (holdDefined code hbefore) as [oldValue holdValue].
        assert (hpreserved : RawCodedAssignmentLookup M
            newSupportCode newSupportStep code oldValue).
        { exact (hpreserve code oldValue hbefore holdValue). }
        assert (holdValueOne : oldValue = rawNumeralValue M 1).
        {
          apply (raw_codedAssignmentLookup_functional M hPA
            newSupportCode newSupportStep code oldValue
            (rawNumeralValue M 1)); assumption.
        }
        apply (proj1 (holdExact code hbefore)).
        unfold rawTermCodeSupported.
        rewrite <- holdValueOne. exact holdValue.
      * intro hoccurrence.
        unfold rawTermCodeSupported in *.
        exact (hpreserve code (rawNumeralValue M 1) hbefore
          (proj2 (holdExact code hbefore) hoccurrence)).
    + split.
      * intro hnewSupported. exfalso.
        apply (raw_termShiftSyntax_zero_neq_one M hPA). symmetry.
        exact (raw_codedAssignmentLookup_functional M hPA
          newSupportCode newSupportStep current
          (rawNumeralValue M 1) (raw_zero M)
          hnewSupported hnewValue).
      * intro hoccurrence. exfalso. exact (hnotOccurs hoccurrence).
Qed.

(** This is an actual instance of PA induction, so [current] and the trace
    bound may both be nonstandard carrier elements. *)
Theorem raw_termShiftTargetSupportPrefix_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    targetCode targetStep bound current,
  RawTermShiftTargetSupportPrefixRealizable M
    current targetCode targetStep bound.
Proof.
  intros M hPA targetCode targetStep bound.
  set (parameterEnv := scons M targetCode
    (scons M targetStep (scons M bound
      (fun _ : nat => raw_zero M)))).
  set (phi := termShiftTargetSupportPrefixRealizableTermAt
    (tVar 0) (tVar 1) (tVar 2) (tVar 3)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_termShiftTargetSupportPrefixRealizableTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exists (raw_zero M), (raw_zero M).
      exact (raw_termShiftTargetSupportPrefix_zero M hPA
        targetCode targetStep bound).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_termShiftTargetSupportPrefixRealizableTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3)) hcurrentSat)
        as hcurrent.
      apply (proj2
        (raw_sat_termShiftTargetSupportPrefixRealizableTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      destruct hcurrent as [oldSupportCode [oldSupportStep hold]].
      exact (raw_termShiftTargetSupportPrefix_succ M hPA
        current targetCode targetStep bound
        oldSupportCode oldSupportStep hold).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_termShiftTargetSupportPrefixRealizableTermAt_iff M
      (scons M current parameterEnv)
      (tVar 0) (tVar 1) (tVar 2) (tVar 3)) (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

(** Constructor fields are strictly below their polynomial list codes. *)
Lemma raw_termShiftSyntax_var_index_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall index,
  rawLt M index (rawTermVarCode M index).
Proof.
  intros M hPA index. unfold rawTermVarCode, rawCodeList2.
  apply rawProofListCode_member_lt; [exact hPA |]. cbn. tauto.
Qed.

Lemma raw_termShiftSyntax_succ_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall child,
  rawLt M child (rawTermSuccCode M child).
Proof.
  intros M hPA child. unfold rawTermSuccCode, rawCodeList2.
  apply rawProofListCode_member_lt; [exact hPA |]. cbn. tauto.
Qed.

Lemma raw_termShiftSyntax_binary_left_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag left right,
  rawLt M left (rawCodeList3 M tag left right).
Proof.
  intros M hPA tag left right. unfold rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |]. cbn. tauto.
Qed.

Lemma raw_termShiftSyntax_binary_right_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag left right,
  rawLt M right (rawCodeList3 M tag left right).
Proof.
  intros M hPA tag left right. unfold rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |]. cbn. tauto.
Qed.

(** The target of a shift trace is syntactically realizable.  Notice that
    no standardness assumption is present: both the trace bound and every
    term code may be nonstandard elements of [M]. *)
Theorem raw_codedTermShiftTrace_target_syntax_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output assignmentCode assignmentStep enclosing,
  RawCodedTermShiftTrace M cutoff amount
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input output ->
  rawLt M output enclosing ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep enclosing ->
  RawTermSyntaxRealizable M output assignmentCode assignmentStep.
Proof.
  intros M hPA cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output assignmentCode assignmentStep enclosing
    (hsourceDefined & htargetDefined & hrootBelow & hrootLookup &
     hrows & hcutoff)
    houtputEnclosing hassignment.
  destruct (raw_termShiftTargetSupportPrefix_exists M hPA
    targetCode targetStep bound (raw_succ M output)) as
    (supportCode & supportStep & hsupport).
  destruct hsupport as [hsupportDefined hsupportExact].
  exists supportCode, supportStep.
  unfold RawTermSyntaxCertificateWithSupport.
  split.
  - split; [exact hsupportDefined |].
    intros code hcodeBound hsupported.
    pose proof (proj1 (hsupportExact code hcodeBound) hsupported)
      as hoccurrence.
    destruct hoccurrence as [index [hindexBound htargetLookup]].
    destruct (hsourceDefined index hindexBound)
      as [source hsourceLookup].
    pose proof (hrows index source code hindexBound
      (conj hsourceLookup htargetLookup)) as hrow.
    unfold RawCodedTermShiftTraversalRow,
      RawCodedTermOperationTraversalRow in hrow.
    destruct hrow as
      [hvariable | [hzero | [hsucc | [hadd | hmul]]]].
    + destruct hvariable as
        (inputIndex & outputIndex & hinput & houtput & hshifted).
      exists outputIndex, (raw_zero M). left. exact houtput.
    + exists (raw_zero M), (raw_zero M). right; left.
      exact (proj2 hzero).
    + destruct hsucc as
        (childIndex & inputChild & outputChild &
         hchildIndex & hchildLookup & hinput & houtput).
      assert (hchildCode : rawLt M outputChild code).
      {
        rewrite houtput. exact (raw_termShiftSyntax_succ_child_lt
          M hPA outputChild).
      }
      assert (hchildBound : rawLt M outputChild (raw_succ M output)).
      {
        exact (raw_assignment_lt_trans M hPA
          outputChild code (raw_succ M output) hchildCode hcodeBound).
      }
      exists outputChild, (raw_zero M). right; right; left.
      split; [exact houtput |]. split.
      * apply (proj2 (hsupportExact outputChild hchildBound)).
        exists childIndex. split.
        -- exact (raw_assignment_lt_trans M hPA
             childIndex index bound hchildIndex hindexBound).
        -- exact (proj2 hchildLookup).
      * exact hchildCode.
    + destruct hadd as
        (leftIndex & inputLeft & outputLeft &
         rightIndex & inputRight & outputRight &
         hleftIndex & hleftLookup & hrightIndex & hrightLookup &
         hinput & houtput).
      assert (hleftCode : rawLt M outputLeft code).
      {
        rewrite houtput. unfold rawTermAddCode.
        exact (raw_termShiftSyntax_binary_left_lt M hPA _ _ _).
      }
      assert (hrightCode : rawLt M outputRight code).
      {
        rewrite houtput. unfold rawTermAddCode.
        exact (raw_termShiftSyntax_binary_right_lt M hPA _ _ _).
      }
      assert (hleftBound : rawLt M outputLeft (raw_succ M output)).
      {
        exact (raw_assignment_lt_trans M hPA
          outputLeft code (raw_succ M output) hleftCode hcodeBound).
      }
      assert (hrightBound : rawLt M outputRight (raw_succ M output)).
      {
        exact (raw_assignment_lt_trans M hPA
          outputRight code (raw_succ M output) hrightCode hcodeBound).
      }
      exists outputLeft, outputRight. right; right; right; left.
      split; [exact houtput |]. repeat split.
      * apply (proj2 (hsupportExact outputLeft hleftBound)).
        exists leftIndex. split.
        -- exact (raw_assignment_lt_trans M hPA
             leftIndex index bound hleftIndex hindexBound).
        -- exact (proj2 hleftLookup).
      * apply (proj2 (hsupportExact outputRight hrightBound)).
        exists rightIndex. split.
        -- exact (raw_assignment_lt_trans M hPA
             rightIndex index bound hrightIndex hindexBound).
        -- exact (proj2 hrightLookup).
      * exact hleftCode.
      * exact hrightCode.
    + destruct hmul as
        (leftIndex & inputLeft & outputLeft &
         rightIndex & inputRight & outputRight &
         hleftIndex & hleftLookup & hrightIndex & hrightLookup &
         hinput & houtput).
      assert (hleftCode : rawLt M outputLeft code).
      {
        rewrite houtput. unfold rawTermMulCode.
        exact (raw_termShiftSyntax_binary_left_lt M hPA _ _ _).
      }
      assert (hrightCode : rawLt M outputRight code).
      {
        rewrite houtput. unfold rawTermMulCode.
        exact (raw_termShiftSyntax_binary_right_lt M hPA _ _ _).
      }
      assert (hleftBound : rawLt M outputLeft (raw_succ M output)).
      {
        exact (raw_assignment_lt_trans M hPA
          outputLeft code (raw_succ M output) hleftCode hcodeBound).
      }
      assert (hrightBound : rawLt M outputRight (raw_succ M output)).
      {
        exact (raw_assignment_lt_trans M hPA
          outputRight code (raw_succ M output) hrightCode hcodeBound).
      }
      exists outputLeft, outputRight. right; right; right; right.
      split; [exact houtput |]. repeat split.
      * apply (proj2 (hsupportExact outputLeft hleftBound)).
        exists leftIndex. split.
        -- exact (raw_assignment_lt_trans M hPA
             leftIndex index bound hleftIndex hindexBound).
        -- exact (proj2 hleftLookup).
      * apply (proj2 (hsupportExact outputRight hrightBound)).
        exists rightIndex. split.
        -- exact (raw_assignment_lt_trans M hPA
             rightIndex index bound hrightIndex hindexBound).
        -- exact (proj2 hrightLookup).
      * exact hleftCode.
      * exact hrightCode.
  - split.
    + intros code hcodeBound hsupported index hvariable.
      apply hassignment.
      assert (hindexCode : rawLt M index code).
      {
        rewrite hvariable.
        exact (raw_termShiftSyntax_var_index_lt M hPA index).
      }
      destruct (raw_lt_succ_cases M hPA code output hcodeBound)
        as [hcodeOutput | ->].
      * exact (raw_assignment_lt_trans M hPA index output enclosing
          (raw_assignment_lt_trans M hPA index code output
            hindexCode hcodeOutput)
          houtputEnclosing).
      * exact (raw_assignment_lt_trans M hPA
          index output enclosing hindexCode houtputEnclosing).
    + apply (proj2 (hsupportExact output
        (raw_assignment_lt_self_succ M hPA output))).
      exists rootIndex. split; [exact hrootBelow |].
      exact (proj2 hrootLookup).
Qed.

Corollary raw_codedTermShift_target_syntax_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount input output assignmentCode assignmentStep enclosing,
  RawCodedTermShift M cutoff amount input output ->
  rawLt M output enclosing ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep enclosing ->
  RawTermSyntaxRealizable M output assignmentCode assignmentStep.
Proof.
  intros M hPA cutoff amount input output assignmentCode assignmentStep
    enclosing
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace) houtput hassignment.
  exact (raw_codedTermShiftTrace_target_syntax_realizable M hPA
    cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output assignmentCode assignmentStep enclosing
    htrace houtput hassignment).
Qed.

End PABoundedRawCodedTermShiftSyntaxRealization.
