(**
  Functionality of the local rank-zero truth evaluator.

  This proof has two independent parts.  First, the zero/one truth tables are
  functional in every raw model of PA.  Second, polynomial constructor
  injectivity identifies a row's children and beta functionality identifies
  their recorded values.  Distinct ternary formula tags, and the unary-list
  arity of falsity, rule out all cross-constructor cases.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedSyntaxConstructorSeparation
  PolynomialPairInjectivity RawCodedAssignment
  RawCodedTermEvaluationStepFunctionality RawCodedRankZeroTruthStep.

Module PABoundedRawCodedRankZeroTruthStepFunctionality.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedTermEvaluationStepFunctionality.
Import PABoundedRawCodedRankZeroTruthStep.

(** ------------------------------------------------------------------
    Boolean truth-table functionality. *)

Lemma raw_zero_neq_truthOne : forall (M : RawPAModel),
  RawPASatisfies M -> raw_zero M <> rawTruthOne M.
Proof.
  intros M hPA heq.
  unfold rawTruthOne in heq.
  change (rawNumeralValue M 0 = rawNumeralValue M 1) in heq.
  apply (rawNumeralValue_injective M hPA 0 1) in heq.
  discriminate.
Qed.

Lemma raw_equalityTruth_functional : forall (M : RawPAModel),
  forall leftValue rightValue leftOutput rightOutput : M,
  RawEqualityTruth M leftOutput leftValue rightValue ->
  RawEqualityTruth M rightOutput leftValue rightValue ->
  leftOutput = rightOutput.
Proof.
  intros M leftValue rightValue leftOutput rightOutput
    [[heq houtLeft] | [hneq houtLeft]]
    [[heq' houtRight] | [hneq' houtRight]].
  - now rewrite houtLeft, houtRight.
  - exact (False_rect _ (hneq' heq)).
  - exact (False_rect _ (hneq heq')).
  - now rewrite houtLeft, houtRight.
Qed.

Lemma raw_impTruth_functional : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right leftOutput rightOutput : M,
  RawImpTruth M leftOutput left right ->
  RawImpTruth M rightOutput left right ->
  leftOutput = rightOutput.
Proof.
  intros M hPA left right leftOutput rightOutput hleft hright.
  destruct hleft as [_ [_ [_ hcaseLeft]]].
  destruct hright as [_ [_ [_ hcaseRight]]].
  destruct hcaseLeft as [[[hl1 hr0] houtLeft] | [htrueLeft houtLeft]];
  destruct hcaseRight as [[[hl1' hr0'] houtRight] | [htrueRight houtRight]].
  - now rewrite houtLeft, houtRight.
  - exfalso.
    destruct htrueRight as [hl0' | hr1'].
    + apply (raw_zero_neq_truthOne M hPA).
      exact (eq_trans (eq_sym hl0') hl1).
    + apply (raw_zero_neq_truthOne M hPA).
      exact (eq_trans (eq_sym hr0) hr1').
  - exfalso.
    destruct htrueLeft as [hl0 | hr1].
    + apply (raw_zero_neq_truthOne M hPA).
      exact (eq_trans (eq_sym hl0) hl1').
    + apply (raw_zero_neq_truthOne M hPA).
      exact (eq_trans (eq_sym hr0') hr1).
  - now rewrite houtLeft, houtRight.
Qed.

Lemma raw_andTruth_functional : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right leftOutput rightOutput : M,
  RawAndTruth M leftOutput left right ->
  RawAndTruth M rightOutput left right ->
  leftOutput = rightOutput.
Proof.
  intros M hPA left right leftOutput rightOutput hleft hright.
  destruct hleft as [_ [_ [_ hcaseLeft]]].
  destruct hright as [_ [_ [_ hcaseRight]]].
  destruct hcaseLeft as [[[hl1 hr1] houtLeft] | [hfalseLeft houtLeft]];
  destruct hcaseRight as [[[hl1' hr1'] houtRight] | [hfalseRight houtRight]].
  - now rewrite houtLeft, houtRight.
  - exfalso.
    destruct hfalseRight as [hl0' | hr0'].
    + apply (raw_zero_neq_truthOne M hPA).
      exact (eq_trans (eq_sym hl0') hl1).
    + apply (raw_zero_neq_truthOne M hPA).
      exact (eq_trans (eq_sym hr0') hr1).
  - exfalso.
    destruct hfalseLeft as [hl0 | hr0].
    + apply (raw_zero_neq_truthOne M hPA).
      exact (eq_trans (eq_sym hl0) hl1').
    + apply (raw_zero_neq_truthOne M hPA).
      exact (eq_trans (eq_sym hr0) hr1').
  - now rewrite houtLeft, houtRight.
Qed.

Lemma raw_orTruth_functional : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right leftOutput rightOutput : M,
  RawOrTruth M leftOutput left right ->
  RawOrTruth M rightOutput left right ->
  leftOutput = rightOutput.
Proof.
  intros M hPA left right leftOutput rightOutput hleft hright.
  destruct hleft as [_ [_ [_ hcaseLeft]]].
  destruct hright as [_ [_ [_ hcaseRight]]].
  destruct hcaseLeft as [[htrueLeft houtLeft] | [[hl0 hr0] houtLeft]];
  destruct hcaseRight as [[htrueRight houtRight] | [[hl0' hr0'] houtRight]].
  - now rewrite houtLeft, houtRight.
  - exfalso.
    destruct htrueLeft as [hl1 | hr1].
    + apply (raw_zero_neq_truthOne M hPA).
      exact (eq_trans (eq_sym hl0') hl1).
    + apply (raw_zero_neq_truthOne M hPA).
      exact (eq_trans (eq_sym hr0') hr1).
  - exfalso.
    destruct htrueRight as [hl1' | hr1'].
    + apply (raw_zero_neq_truthOne M hPA).
      exact (eq_trans (eq_sym hl0) hl1').
    + apply (raw_zero_neq_truthOne M hPA).
      exact (eq_trans (eq_sym hr0) hr1').
  - now rewrite houtLeft, houtRight.
Qed.

(** ------------------------------------------------------------------
    Constructor tag recovery. *)

Lemma raw_codeList3_numeral_tags_eq : forall (M : RawPAModel),
  RawPASatisfies M -> forall tagLeft tagRight a b c d,
  rawCodeList3 M (rawNumeralValue M tagLeft) a b =
  rawCodeList3 M (rawNumeralValue M tagRight) c d ->
  tagLeft = tagRight.
Proof.
  intros M hPA tagLeft tagRight a b c d heq.
  destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
    _ _ _ _ _ _ heq) as [htag _].
  exact (rawNumeralValue_injective M hPA tagLeft tagRight htag).
Qed.

(** ------------------------------------------------------------------
    Same-constructor row functionality. *)

Lemma raw_formulaEqTruthRows_value_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code termTableCode termTableStep
    l1 lv1 r1 rv1 l2 lv2 r2 rv2 leftOutput rightOutput : M,
  RawFormulaEqTruthRow M code leftOutput termTableCode termTableStep
    l1 lv1 r1 rv1 ->
  RawFormulaEqTruthRow M code rightOutput termTableCode termTableStep
    l2 lv2 r2 rv2 ->
  leftOutput = rightOutput.
Proof.
  intros M hPA code termTableCode termTableStep
    l1 lv1 r1 rv1 l2 lv2 r2 rv2 leftOutput rightOutput
    [hcode1 [hlookupL1 [hlookupR1 htruth1]]]
    [hcode2 [hlookupL2 [hlookupR2 htruth2]]].
  assert (hcodes : rawFormulaEqCode M l1 r1 = rawFormulaEqCode M l2 r2).
  { exact (eq_trans (eq_sym hcode1) hcode2). }
  unfold rawFormulaEqCode in hcodes.
  destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
    _ _ _ _ _ _ hcodes) as [_ [hl hr]].
  subst l2. subst r2.
  assert (hlv : lv1 = lv2).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      termTableCode termTableStep l1 lv1 lv2 hlookupL1 hlookupL2).
  }
  assert (hrv : rv1 = rv2).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      termTableCode termTableStep r1 rv1 rv2 hlookupR1 hlookupR2).
  }
  subst lv2. subst rv2.
  exact (raw_equalityTruth_functional M lv1 rv1
    leftOutput rightOutput htruth1 htruth2).
Qed.

Lemma raw_formulaImpTruthRows_value_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code truthTableCode truthTableStep
    l1 lv1 r1 rv1 l2 lv2 r2 rv2 leftOutput rightOutput : M,
  RawFormulaImpTruthRow M code leftOutput truthTableCode truthTableStep
    l1 lv1 r1 rv1 ->
  RawFormulaImpTruthRow M code rightOutput truthTableCode truthTableStep
    l2 lv2 r2 rv2 ->
  leftOutput = rightOutput.
Proof.
  intros M hPA code truthTableCode truthTableStep
    l1 lv1 r1 rv1 l2 lv2 r2 rv2 leftOutput rightOutput
    [hcode1 [hlookupL1 [hlookupR1 htruth1]]]
    [hcode2 [hlookupL2 [hlookupR2 htruth2]]].
  assert (hcodes : rawFormulaImpCode M l1 r1 = rawFormulaImpCode M l2 r2).
  { exact (eq_trans (eq_sym hcode1) hcode2). }
  unfold rawFormulaImpCode in hcodes.
  destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
    _ _ _ _ _ _ hcodes) as [_ [hl hr]].
  subst l2. subst r2.
  assert (hlv : lv1 = lv2).
  { eapply raw_codedAssignmentLookup_functional; eauto. }
  assert (hrv : rv1 = rv2).
  { eapply raw_codedAssignmentLookup_functional; eauto. }
  subst lv2. subst rv2.
  exact (raw_impTruth_functional M hPA lv1 rv1
    leftOutput rightOutput htruth1 htruth2).
Qed.

Lemma raw_formulaAndTruthRows_value_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code truthTableCode truthTableStep
    l1 lv1 r1 rv1 l2 lv2 r2 rv2 leftOutput rightOutput : M,
  RawFormulaAndTruthRow M code leftOutput truthTableCode truthTableStep
    l1 lv1 r1 rv1 ->
  RawFormulaAndTruthRow M code rightOutput truthTableCode truthTableStep
    l2 lv2 r2 rv2 ->
  leftOutput = rightOutput.
Proof.
  intros M hPA code truthTableCode truthTableStep
    l1 lv1 r1 rv1 l2 lv2 r2 rv2 leftOutput rightOutput
    [hcode1 [hlookupL1 [hlookupR1 htruth1]]]
    [hcode2 [hlookupL2 [hlookupR2 htruth2]]].
  assert (hcodes : rawFormulaAndCode M l1 r1 = rawFormulaAndCode M l2 r2).
  { exact (eq_trans (eq_sym hcode1) hcode2). }
  unfold rawFormulaAndCode in hcodes.
  destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
    _ _ _ _ _ _ hcodes) as [_ [hl hr]].
  subst l2. subst r2.
  assert (hlv : lv1 = lv2).
  { eapply raw_codedAssignmentLookup_functional; eauto. }
  assert (hrv : rv1 = rv2).
  { eapply raw_codedAssignmentLookup_functional; eauto. }
  subst lv2. subst rv2.
  exact (raw_andTruth_functional M hPA lv1 rv1
    leftOutput rightOutput htruth1 htruth2).
Qed.

Lemma raw_formulaOrTruthRows_value_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code truthTableCode truthTableStep
    l1 lv1 r1 rv1 l2 lv2 r2 rv2 leftOutput rightOutput : M,
  RawFormulaOrTruthRow M code leftOutput truthTableCode truthTableStep
    l1 lv1 r1 rv1 ->
  RawFormulaOrTruthRow M code rightOutput truthTableCode truthTableStep
    l2 lv2 r2 rv2 ->
  leftOutput = rightOutput.
Proof.
  intros M hPA code truthTableCode truthTableStep
    l1 lv1 r1 rv1 l2 lv2 r2 rv2 leftOutput rightOutput
    [hcode1 [hlookupL1 [hlookupR1 htruth1]]]
    [hcode2 [hlookupL2 [hlookupR2 htruth2]]].
  assert (hcodes : rawFormulaOrCode M l1 r1 = rawFormulaOrCode M l2 r2).
  { exact (eq_trans (eq_sym hcode1) hcode2). }
  unfold rawFormulaOrCode in hcodes.
  destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
    _ _ _ _ _ _ hcodes) as [_ [hl hr]].
  subst l2. subst r2.
  assert (hlv : lv1 = lv2).
  { eapply raw_codedAssignmentLookup_functional; eauto. }
  assert (hrv : rv1 = rv2).
  { eapply raw_codedAssignmentLookup_functional; eauto. }
  subst lv2. subst rv2.
  exact (raw_orTruth_functional M hPA lv1 rv1
    leftOutput rightOutput htruth1 htruth2).
Qed.

(** ------------------------------------------------------------------
    Full rank-zero step functionality. *)

Theorem raw_rankZeroTruthStep_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code termTableCode termTableStep truthTableCode truthTableStep
    leftOutput rightOutput,
  RawRankZeroTruthStep M code leftOutput
    termTableCode termTableStep truthTableCode truthTableStep ->
  RawRankZeroTruthStep M code rightOutput
    termTableCode termTableStep truthTableCode truthTableStep ->
  leftOutput = rightOutput.
Proof.
  intros M hPA code termTableCode termTableStep truthTableCode truthTableStep
    leftOutput rightOutput
    [l1 [lv1 [r1 [rv1 hleft]]]]
    [l2 [lv2 [r2 [rv2 hright]]]].
  destruct hleft as [heq1 | [hbot1 | [himp1 | [hand1 | hor1]]]];
  destruct hright as [heq2 | [hbot2 | [himp2 | [hand2 | hor2]]]].
  - exact (raw_formulaEqTruthRows_value_functional M hPA
      code termTableCode termTableStep l1 lv1 r1 rv1 l2 lv2 r2 rv2
      leftOutput rightOutput heq1 heq2).
  - destruct heq1 as [hc1 _]. destruct hbot2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 0) l1 r1).
    exact (eq_trans (eq_sym hc2) hc1).
  - destruct heq1 as [hc1 _]. destruct himp2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      0 2 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct heq1 as [hc1 _]. destruct hand2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      0 3 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct heq1 as [hc1 _]. destruct hor2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      0 4 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hbot1 as [hc1 _]. destruct heq2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 0) l2 r2).
    exact (eq_trans (eq_sym hc1) hc2).
  - destruct hbot1 as [_ hv1]. destruct hbot2 as [_ hv2].
    now rewrite hv1, hv2.
  - destruct hbot1 as [hc1 _]. destruct himp2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 2) l2 r2).
    exact (eq_trans (eq_sym hc1) hc2).
  - destruct hbot1 as [hc1 _]. destruct hand2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 3) l2 r2).
    exact (eq_trans (eq_sym hc1) hc2).
  - destruct hbot1 as [hc1 _]. destruct hor2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 4) l2 r2).
    exact (eq_trans (eq_sym hc1) hc2).
  - destruct himp1 as [hc1 _]. destruct heq2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      2 0 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct himp1 as [hc1 _]. destruct hbot2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 2) l1 r1).
    exact (eq_trans (eq_sym hc2) hc1).
  - exact (raw_formulaImpTruthRows_value_functional M hPA
      code truthTableCode truthTableStep l1 lv1 r1 rv1 l2 lv2 r2 rv2
      leftOutput rightOutput himp1 himp2).
  - destruct himp1 as [hc1 _]. destruct hand2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      2 3 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct himp1 as [hc1 _]. destruct hor2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      2 4 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hand1 as [hc1 _]. destruct heq2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      3 0 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hand1 as [hc1 _]. destruct hbot2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 3) l1 r1).
    exact (eq_trans (eq_sym hc2) hc1).
  - destruct hand1 as [hc1 _]. destruct himp2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      3 2 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - exact (raw_formulaAndTruthRows_value_functional M hPA
      code truthTableCode truthTableStep l1 lv1 r1 rv1 l2 lv2 r2 rv2
      leftOutput rightOutput hand1 hand2).
  - destruct hand1 as [hc1 _]. destruct hor2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      3 4 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hor1 as [hc1 _]. destruct heq2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      4 0 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hor1 as [hc1 _]. destruct hbot2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 4) l1 r1).
    exact (eq_trans (eq_sym hc2) hc1).
  - destruct hor1 as [hc1 _]. destruct himp2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      4 2 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hor1 as [hc1 _]. destruct hand2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      4 3 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - exact (raw_formulaOrTruthRows_value_functional M hPA
      code truthTableCode truthTableStep l1 lv1 r1 rv1 l2 lv2 r2 rv2
      leftOutput rightOutput hor1 hor2).
Qed.

Corollary raw_sat_rankZeroTruthStepTermAt_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code termTableCode termTableStep truthTableCode truthTableStep
    leftOutput rightOutput (e : nat -> M),
  raw_formula_sat M e
    (rankZeroTruthStepTermAt code leftOutput
      termTableCode termTableStep truthTableCode truthTableStep) ->
  raw_formula_sat M e
    (rankZeroTruthStepTermAt code rightOutput
      termTableCode termTableStep truthTableCode truthTableStep) ->
  raw_term_eval M e leftOutput = raw_term_eval M e rightOutput.
Proof.
  intros M hPA code termTableCode termTableStep truthTableCode truthTableStep
    leftOutput rightOutput e hleft hright.
  apply (raw_rankZeroTruthStep_functional M hPA
    (raw_term_eval M e code)
    (raw_term_eval M e termTableCode) (raw_term_eval M e termTableStep)
    (raw_term_eval M e truthTableCode) (raw_term_eval M e truthTableStep)).
  - apply (proj1 (raw_sat_rankZeroTruthStepTermAt_iff
      M e code leftOutput termTableCode termTableStep
      truthTableCode truthTableStep)). exact hleft.
  - apply (proj1 (raw_sat_rankZeroTruthStepTermAt_iff
      M e code rightOutput termTableCode termTableStep
      truthTableCode truthTableStep)). exact hright.
Qed.

End PABoundedRawCodedRankZeroTruthStepFunctionality.
