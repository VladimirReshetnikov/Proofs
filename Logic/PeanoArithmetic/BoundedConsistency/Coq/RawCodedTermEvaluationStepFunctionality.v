(**
  Functionality of one transparent coded-term evaluation row.

  [RawCodedTermEvaluationStep] permits existential constructor witnesses.  To
  use it in a model-internal beta traversal we must know that two rows for the
  same term code and the same assignment/table cannot propose different
  values.  This file supplies that theorem without a premise: polynomial-pair
  injectivity distinguishes list arities and recovers constructor fields,
  standard numeral injectivity distinguishes equal-arity tags, and beta
  functionality identifies the recursively looked-up values.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedSyntaxConstructorSeparation
  PolynomialPairInjectivity RawCodedAssignment
  RawCodedTermEvaluationStep.

Module PABoundedRawCodedTermEvaluationStepFunctionality.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedTermEvaluationStep.

(** ------------------------------------------------------------------
    Constructor separation. *)

Lemma raw_codeList1_neq_codeList3 : forall (M : RawPAModel),
  RawPASatisfies M -> RawListNodeInjective M -> forall a b c d,
  rawCodeList1 M a <> rawCodeList3 M b c d.
Proof.
  intros M hPA hnode a b c d heq.
  unfold rawCodeList1, rawCodeList3, rawListCode in heq.
  pose proof (proj2 (hnode a (raw_zero M) b
    (rawListNode M c (rawListNode M d (raw_zero M))) heq)) as hzero.
  exact (raw_zero_not_succ_syntax M hPA
    (rawPolynomialPair M c (rawListNode M d (raw_zero M))) hzero).
Qed.

Lemma raw_termVarCode_neq_termZeroCode : forall (M : RawPAModel),
  RawPASatisfies M -> forall index,
  rawTermVarCode M index <> rawTermZeroCode M.
Proof.
  intros M hPA index heq.
  unfold rawTermVarCode, rawTermZeroCode in heq.
  exact (raw_codeList1_neq_codeList2 M hPA
    (rawListNode_injective M hPA)
    (rawNumeralValue M 1) (rawNumeralValue M 0) index
    (eq_sym heq)).
Qed.

Lemma raw_termVarCode_neq_termSuccCode : forall (M : RawPAModel),
  RawPASatisfies M -> forall index child,
  rawTermVarCode M index <> rawTermSuccCode M child.
Proof.
  intros M hPA index child heq.
  unfold rawTermVarCode, rawTermSuccCode in heq.
  destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
    _ _ _ _ heq) as [htag _].
  apply (rawNumeralValue_injective M hPA 0 2) in htag.
  discriminate.
Qed.

Lemma raw_termVarCode_neq_termAddCode : forall (M : RawPAModel),
  RawPASatisfies M -> forall index left right,
  rawTermVarCode M index <> rawTermAddCode M left right.
Proof.
  intros M hPA index left right.
  unfold rawTermVarCode, rawTermAddCode.
  exact (raw_codeList2_neq_codeList3 M hPA
    (rawListNode_injective M hPA)
    (rawNumeralValue M 0) index
    (rawNumeralValue M 3) left right).
Qed.

Lemma raw_termVarCode_neq_termMulCode : forall (M : RawPAModel),
  RawPASatisfies M -> forall index left right,
  rawTermVarCode M index <> rawTermMulCode M left right.
Proof.
  intros M hPA index left right.
  unfold rawTermVarCode, rawTermMulCode.
  exact (raw_codeList2_neq_codeList3 M hPA
    (rawListNode_injective M hPA)
    (rawNumeralValue M 0) index
    (rawNumeralValue M 4) left right).
Qed.

Lemma raw_termZeroCode_neq_termSuccCode : forall (M : RawPAModel),
  RawPASatisfies M -> forall child,
  rawTermZeroCode M <> rawTermSuccCode M child.
Proof.
  intros M hPA child.
  unfold rawTermZeroCode, rawTermSuccCode.
  exact (raw_codeList1_neq_codeList2 M hPA
    (rawListNode_injective M hPA)
    (rawNumeralValue M 1) (rawNumeralValue M 2) child).
Qed.

Lemma raw_termZeroCode_neq_termAddCode : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right,
  rawTermZeroCode M <> rawTermAddCode M left right.
Proof.
  intros M hPA left right.
  unfold rawTermZeroCode, rawTermAddCode.
  exact (raw_codeList1_neq_codeList3 M hPA
    (rawListNode_injective M hPA)
    (rawNumeralValue M 1) (rawNumeralValue M 3) left right).
Qed.

Lemma raw_termZeroCode_neq_termMulCode : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right,
  rawTermZeroCode M <> rawTermMulCode M left right.
Proof.
  intros M hPA left right.
  unfold rawTermZeroCode, rawTermMulCode.
  exact (raw_codeList1_neq_codeList3 M hPA
    (rawListNode_injective M hPA)
    (rawNumeralValue M 1) (rawNumeralValue M 4) left right).
Qed.

Lemma raw_termSuccCode_neq_termAddCode : forall (M : RawPAModel),
  RawPASatisfies M -> forall child left right,
  rawTermSuccCode M child <> rawTermAddCode M left right.
Proof.
  intros M hPA child left right.
  unfold rawTermSuccCode, rawTermAddCode.
  exact (raw_codeList2_neq_codeList3 M hPA
    (rawListNode_injective M hPA)
    (rawNumeralValue M 2) child
    (rawNumeralValue M 3) left right).
Qed.

Lemma raw_termSuccCode_neq_termMulCode : forall (M : RawPAModel),
  RawPASatisfies M -> forall child left right,
  rawTermSuccCode M child <> rawTermMulCode M left right.
Proof.
  intros M hPA child left right.
  unfold rawTermSuccCode, rawTermMulCode.
  exact (raw_codeList2_neq_codeList3 M hPA
    (rawListNode_injective M hPA)
    (rawNumeralValue M 2) child
    (rawNumeralValue M 4) left right).
Qed.

Lemma raw_termAddCode_neq_termMulCode : forall (M : RawPAModel),
  RawPASatisfies M -> forall a b c d,
  rawTermAddCode M a b <> rawTermMulCode M c d.
Proof.
  intros M hPA a b c d heq.
  unfold rawTermAddCode, rawTermMulCode in heq.
  destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
    _ _ _ _ _ _ heq) as [htag _].
  apply (rawNumeralValue_injective M hPA 3 4) in htag.
  discriminate.
Qed.

(** ------------------------------------------------------------------
    Same-constructor rows remain functional even when their existential
    child witnesses were chosen independently. *)

Lemma raw_termVarEvaluationRows_value_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code assignmentCode assignmentStep
    indexLeft indexRight left right : M,
  RawTermVarEvaluationRow M
    code left assignmentCode assignmentStep indexLeft ->
  RawTermVarEvaluationRow M
    code right assignmentCode assignmentStep indexRight ->
  left = right.
Proof.
  intros M hPA code assignmentCode assignmentStep
    indexLeft indexRight left right
    [hcodeLeft hlookupLeft] [hcodeRight hlookupRight].
  assert (hcodes : rawTermVarCode M indexLeft =
      rawTermVarCode M indexRight).
  { exact (eq_trans (eq_sym hcodeLeft) hcodeRight). }
  unfold rawTermVarCode in hcodes.
  destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
    _ _ _ _ hcodes) as [_ hindex].
  subst indexRight.
  exact (raw_codedAssignmentLookup_functional M hPA
    assignmentCode assignmentStep indexLeft left right
    hlookupLeft hlookupRight).
Qed.

Lemma raw_termSuccEvaluationRows_value_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code tableCode tableStep
    childLeft childValueLeft childRight childValueRight left right : M,
  RawTermSuccEvaluationRow M
    code left tableCode tableStep childLeft childValueLeft ->
  RawTermSuccEvaluationRow M
    code right tableCode tableStep childRight childValueRight ->
  left = right.
Proof.
  intros M hPA code tableCode tableStep
    childLeft childValueLeft childRight childValueRight left right
    [hcodeLeft [hlookupLeft hvalueLeft]]
    [hcodeRight [hlookupRight hvalueRight]].
  assert (hcodes : rawTermSuccCode M childLeft =
      rawTermSuccCode M childRight).
  { exact (eq_trans (eq_sym hcodeLeft) hcodeRight). }
  unfold rawTermSuccCode in hcodes.
  destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
    _ _ _ _ hcodes) as [_ hchild].
  subst childRight.
  assert (hchildValue : childValueLeft = childValueRight).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      tableCode tableStep childLeft childValueLeft childValueRight
      hlookupLeft hlookupRight).
  }
  now rewrite hvalueLeft, hvalueRight, hchildValue.
Qed.

Lemma raw_termAddEvaluationRows_value_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code tableCode tableStep
    l1 lv1 r1 rv1 l2 lv2 r2 rv2 left right : M,
  RawTermAddEvaluationRow M
    code left tableCode tableStep l1 lv1 r1 rv1 ->
  RawTermAddEvaluationRow M
    code right tableCode tableStep l2 lv2 r2 rv2 ->
  left = right.
Proof.
  intros M hPA code tableCode tableStep
    l1 lv1 r1 rv1 l2 lv2 r2 rv2 left right
    [hcodeLeft [hlookupL1 [hlookupR1 hvalueLeft]]]
    [hcodeRight [hlookupL2 [hlookupR2 hvalueRight]]].
  assert (hcodes : rawTermAddCode M l1 r1 = rawTermAddCode M l2 r2).
  { exact (eq_trans (eq_sym hcodeLeft) hcodeRight). }
  unfold rawTermAddCode in hcodes.
  destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
    _ _ _ _ _ _ hcodes) as [_ [hl hr]].
  subst l2. subst r2.
  assert (hlv : lv1 = lv2).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      tableCode tableStep l1 lv1 lv2 hlookupL1 hlookupL2).
  }
  assert (hrv : rv1 = rv2).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      tableCode tableStep r1 rv1 rv2 hlookupR1 hlookupR2).
  }
  now rewrite hvalueLeft, hvalueRight, hlv, hrv.
Qed.

Lemma raw_termMulEvaluationRows_value_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code tableCode tableStep
    l1 lv1 r1 rv1 l2 lv2 r2 rv2 left right : M,
  RawTermMulEvaluationRow M
    code left tableCode tableStep l1 lv1 r1 rv1 ->
  RawTermMulEvaluationRow M
    code right tableCode tableStep l2 lv2 r2 rv2 ->
  left = right.
Proof.
  intros M hPA code tableCode tableStep
    l1 lv1 r1 rv1 l2 lv2 r2 rv2 left right
    [hcodeLeft [hlookupL1 [hlookupR1 hvalueLeft]]]
    [hcodeRight [hlookupL2 [hlookupR2 hvalueRight]]].
  assert (hcodes : rawTermMulCode M l1 r1 = rawTermMulCode M l2 r2).
  { exact (eq_trans (eq_sym hcodeLeft) hcodeRight). }
  unfold rawTermMulCode in hcodes.
  destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
    _ _ _ _ _ _ hcodes) as [_ [hl hr]].
  subst l2. subst r2.
  assert (hlv : lv1 = lv2).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      tableCode tableStep l1 lv1 lv2 hlookupL1 hlookupL2).
  }
  assert (hrv : rv1 = rv2).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      tableCode tableStep r1 rv1 rv2 hlookupR1 hlookupR2).
  }
  now rewrite hvalueLeft, hvalueRight, hlv, hrv.
Qed.

(** ------------------------------------------------------------------
    Full one-step functionality. *)

Theorem raw_termEvaluationStep_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code assignmentCode assignmentStep tableCode tableStep left right,
  RawTermEvaluationStep M
    code left assignmentCode assignmentStep tableCode tableStep ->
  RawTermEvaluationStep M
    code right assignmentCode assignmentStep tableCode tableStep ->
  left = right.
Proof.
  intros M hPA code assignmentCode assignmentStep tableCode tableStep
    left right
    [l1 [lv1 [r1 [rv1 hleft]]]]
    [l2 [lv2 [r2 [rv2 hright]]]].
  destruct hleft as [hvar1 | [hzero1 | [hsucc1 | [hadd1 | hmul1]]]];
  destruct hright as [hvar2 | [hzero2 | [hsucc2 | [hadd2 | hmul2]]]].
  - exact (raw_termVarEvaluationRows_value_functional M hPA
      code assignmentCode assignmentStep l1 l2 left right hvar1 hvar2).
  - destruct hvar1 as [hc1 _]. destruct hzero2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termZeroCode M hPA l1
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hvar1 as [hc1 _]. destruct hsucc2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termSuccCode M hPA l1 l2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hvar1 as [hc1 _]. destruct hadd2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termAddCode M hPA l1 l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hvar1 as [hc1 _]. destruct hmul2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termMulCode M hPA l1 l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hzero1 as [hc1 _]. destruct hvar2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termZeroCode M hPA l2
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hzero1 as [_ hv1]. destruct hzero2 as [_ hv2].
    now rewrite hv1, hv2.
  - destruct hzero1 as [hc1 _]. destruct hsucc2 as [hc2 _].
    exfalso. exact (raw_termZeroCode_neq_termSuccCode M hPA l2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hzero1 as [hc1 _]. destruct hadd2 as [hc2 _].
    exfalso. exact (raw_termZeroCode_neq_termAddCode M hPA l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hzero1 as [hc1 _]. destruct hmul2 as [hc2 _].
    exfalso. exact (raw_termZeroCode_neq_termMulCode M hPA l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hsucc1 as [hc1 _]. destruct hvar2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termSuccCode M hPA l2 l1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hsucc1 as [hc1 _]. destruct hzero2 as [hc2 _].
    exfalso. exact (raw_termZeroCode_neq_termSuccCode M hPA l1
      (eq_trans (eq_sym hc2) hc1)).
  - exact (raw_termSuccEvaluationRows_value_functional M hPA
      code tableCode tableStep l1 lv1 l2 lv2 left right hsucc1 hsucc2).
  - destruct hsucc1 as [hc1 _]. destruct hadd2 as [hc2 _].
    exfalso. exact (raw_termSuccCode_neq_termAddCode M hPA l1 l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hsucc1 as [hc1 _]. destruct hmul2 as [hc2 _].
    exfalso. exact (raw_termSuccCode_neq_termMulCode M hPA l1 l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hadd1 as [hc1 _]. destruct hvar2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termAddCode M hPA l2 l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hadd1 as [hc1 _]. destruct hzero2 as [hc2 _].
    exfalso. exact (raw_termZeroCode_neq_termAddCode M hPA l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hadd1 as [hc1 _]. destruct hsucc2 as [hc2 _].
    exfalso. exact (raw_termSuccCode_neq_termAddCode M hPA l2 l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - exact (raw_termAddEvaluationRows_value_functional M hPA
      code tableCode tableStep l1 lv1 r1 rv1 l2 lv2 r2 rv2
      left right hadd1 hadd2).
  - destruct hadd1 as [hc1 _]. destruct hmul2 as [hc2 _].
    exfalso. exact (raw_termAddCode_neq_termMulCode M hPA l1 r1 l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hmul1 as [hc1 _]. destruct hvar2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termMulCode M hPA l2 l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hmul1 as [hc1 _]. destruct hzero2 as [hc2 _].
    exfalso. exact (raw_termZeroCode_neq_termMulCode M hPA l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hmul1 as [hc1 _]. destruct hsucc2 as [hc2 _].
    exfalso. exact (raw_termSuccCode_neq_termMulCode M hPA l2 l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hmul1 as [hc1 _]. destruct hadd2 as [hc2 _].
    exfalso. exact (raw_termAddCode_neq_termMulCode M hPA l2 r2 l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - exact (raw_termMulEvaluationRows_value_functional M hPA
      code tableCode tableStep l1 lv1 r1 rv1 l2 lv2 r2 rv2
      left right hmul1 hmul2).
Qed.

Corollary raw_sat_termEvaluationStepTermAt_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code assignmentCode assignmentStep tableCode tableStep
    left right (e : nat -> M),
  raw_formula_sat M e
    (termEvaluationStepTermAt
      code left assignmentCode assignmentStep tableCode tableStep) ->
  raw_formula_sat M e
    (termEvaluationStepTermAt
      code right assignmentCode assignmentStep tableCode tableStep) ->
  raw_term_eval M e left = raw_term_eval M e right.
Proof.
  intros M hPA code assignmentCode assignmentStep tableCode tableStep
    left right e hleft hright.
  apply (raw_termEvaluationStep_functional M hPA
    (raw_term_eval M e code)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)
    (raw_term_eval M e tableCode)
    (raw_term_eval M e tableStep)).
  - apply (proj1 (raw_sat_termEvaluationStepTermAt_iff
      M e code left assignmentCode assignmentStep tableCode tableStep)).
    exact hleft.
  - apply (proj1 (raw_sat_termEvaluationStepTermAt_iff
      M e code right assignmentCode assignmentStep tableCode tableStep)).
    exact hright.
Qed.

End PABoundedRawCodedTermEvaluationStepFunctionality.
