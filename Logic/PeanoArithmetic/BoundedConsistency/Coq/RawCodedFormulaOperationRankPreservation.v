(**
  Arbitrary-model rank preservation for coded formula operations.

  Operation tables preserve the outer constructor in every row.  Their
  bounds may be nonstandard, so rank agreement cannot be proved by Rocq
  recursion over decoded syntax.  The invariant below is a PA formula and
  is propagated by model-internal induction over the operation table.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedProofDescent
  RawCodedTermEvaluationTraversal RawCodedFormulaRankStepFunctionality
  RawCodedFormulaRankTraversal RawCodedFormulaRankRealization
  RawCodedFormulaRankTotality RawCodedFormulaOperations
  RawCodedFormulaOperationQuotedRankSound
  RawCodedFixedLevelTruthOperationTransport.

Import ListNotations.

Module PABoundedRawCodedFormulaOperationRankPreservation.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedFormulaRankStepFunctionality.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankRealization.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationQuotedRankSound.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.

Lemma raw_formulaOperation_binary_left_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag left right,
  rawLt M left (rawCodeList3 M tag left right).
Proof.
  intros M hPA tag left right. unfold rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
Qed.

Lemma raw_formulaOperation_binary_right_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag left right,
  rawLt M right (rawCodeList3 M tag left right).
Proof.
  intros M hPA tag left right. unfold rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
Qed.

Lemma raw_formulaOperation_unary_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag child,
  rawLt M child (rawCodeList2 M tag child).
Proof.
  intros M hPA tag child. unfold rawCodeList2.
  apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
Qed.

(** Constructor-local rank laws. *)

Lemma raw_formulaOperation_eq_rankAgreement : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    sourceLeft sourceRight targetLeft targetRight,
  RawCodedFormulaRankAgreement M
    (rawFormulaEqCode M sourceLeft sourceRight)
    (rawFormulaEqCode M targetLeft targetRight).
Proof.
  intros M hPA sourceLeft sourceRight targetLeft targetRight
    sourceSigma sourcePi targetSigma targetPi hsource htarget.
  pose proof (raw_codedFormulaRank_shape_evidence
    polynomialPairInjectivityProof M hPA
    (rawShapeEq sourceLeft sourceRight) sourceSigma sourcePi hsource)
    as hsourceZero.
  pose proof (raw_codedFormulaRank_shape_evidence
    polynomialPairInjectivityProof M hPA
    (rawShapeEq targetLeft targetRight) targetSigma targetPi htarget)
    as htargetZero.
  exact (raw_formulaRankZero_functional M
    targetSigma targetPi sourceSigma sourcePi htargetZero hsourceZero).
Qed.

Lemma raw_formulaOperation_bot_rankAgreement : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaRankAgreement M
    (rawFormulaBotCode M) (rawFormulaBotCode M).
Proof.
  intros M hPA sourceSigma sourcePi targetSigma targetPi hsource htarget.
  pose proof (raw_codedFormulaRank_shape_evidence
    polynomialPairInjectivityProof M hPA rawShapeBot
    sourceSigma sourcePi hsource) as hsourceZero.
  pose proof (raw_codedFormulaRank_shape_evidence
    polynomialPairInjectivityProof M hPA rawShapeBot
    targetSigma targetPi htarget) as htargetZero.
  exact (raw_formulaRankZero_functional M
    targetSigma targetPi sourceSigma sourcePi htargetZero hsourceZero).
Qed.

Lemma raw_formulaOperation_imp_rankAgreement : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    sourceLeft sourceRight targetLeft targetRight,
  RawCodedFormulaRankAgreement M sourceLeft targetLeft ->
  RawCodedFormulaRankAgreement M sourceRight targetRight ->
  RawCodedFormulaRankAgreement M
    (rawFormulaImpCode M sourceLeft sourceRight)
    (rawFormulaImpCode M targetLeft targetRight).
Proof.
  intros M hPA sourceLeft sourceRight targetLeft targetRight
    hleft hright sourceSigma sourcePi targetSigma targetPi hsource htarget.
  pose proof (raw_codedFormulaRank_shape_evidence
    polynomialPairInjectivityProof M hPA
    (rawShapeImp sourceLeft sourceRight) sourceSigma sourcePi hsource)
    as hsourceEvidence.
  pose proof (raw_codedFormulaRank_shape_evidence
    polynomialPairInjectivityProof M hPA
    (rawShapeImp targetLeft targetRight) targetSigma targetPi htarget)
    as htargetEvidence.
  cbn [RawCodedFormulaShapeRankEvidence] in
    hsourceEvidence, htargetEvidence.
  destruct hsourceEvidence as
    (sourceLeftSigma & sourceLeftPi & sourceRightSigma & sourceRightPi &
     hsourceLeft & hsourceRight & hsourceRelation).
  destruct htargetEvidence as
    (targetLeftSigma & targetLeftPi & targetRightSigma & targetRightPi &
     htargetLeft & htargetRight & htargetRelation).
  destruct (hleft sourceLeftSigma sourceLeftPi targetLeftSigma targetLeftPi
    hsourceLeft htargetLeft) as [htargetLeftSigma htargetLeftPi].
  destruct (hright sourceRightSigma sourceRightPi
    targetRightSigma targetRightPi hsourceRight htargetRight)
    as [htargetRightSigma htargetRightPi].
  subst targetLeftSigma. subst targetLeftPi.
  subst targetRightSigma. subst targetRightPi.
  exact (raw_formulaRankImp_functional M hPA
    targetSigma targetPi sourceSigma sourcePi
    sourceLeftSigma sourceLeftPi sourceRightSigma sourceRightPi
    htargetRelation hsourceRelation).
Qed.

Lemma raw_formulaOperation_andOr_rankAgreement : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    sourceLeft sourceRight targetLeft targetRight
    (sourceConstructor targetConstructor : M -> M -> M),
  (forall left right,
    sourceConstructor left right = rawFormulaAndCode M left right \/
    sourceConstructor left right = rawFormulaOrCode M left right) ->
  (forall left right,
    targetConstructor left right = rawFormulaAndCode M left right \/
    targetConstructor left right = rawFormulaOrCode M left right) ->
  RawCodedFormulaRankAgreement M sourceLeft targetLeft ->
  RawCodedFormulaRankAgreement M sourceRight targetRight ->
  RawCodedFormulaRankAgreement M
    (sourceConstructor sourceLeft sourceRight)
    (targetConstructor targetLeft targetRight).
Proof.
  intros M hPA sourceLeft sourceRight targetLeft targetRight
    sourceConstructor targetConstructor hsourceConstructor htargetConstructor
    hleft hright.
  destruct (hsourceConstructor sourceLeft sourceRight) as [hsource | hsource];
    destruct (htargetConstructor targetLeft targetRight) as [htarget | htarget];
    rewrite hsource, htarget.
  all: intros sourceSigma sourcePi targetSigma targetPi
    hsourceRank htargetRank.
  all: first
    [pose proof (raw_codedFormulaRank_shape_evidence
      polynomialPairInjectivityProof M hPA
      (rawShapeAnd sourceLeft sourceRight)
      sourceSigma sourcePi hsourceRank) as hsourceEvidence
    |pose proof (raw_codedFormulaRank_shape_evidence
      polynomialPairInjectivityProof M hPA
      (rawShapeOr sourceLeft sourceRight)
      sourceSigma sourcePi hsourceRank) as hsourceEvidence].
  all: first
    [pose proof (raw_codedFormulaRank_shape_evidence
      polynomialPairInjectivityProof M hPA
      (rawShapeAnd targetLeft targetRight)
      targetSigma targetPi htargetRank) as htargetEvidence
    |pose proof (raw_codedFormulaRank_shape_evidence
      polynomialPairInjectivityProof M hPA
      (rawShapeOr targetLeft targetRight)
      targetSigma targetPi htargetRank) as htargetEvidence].
  all: cbn [RawCodedFormulaShapeRankEvidence] in
    hsourceEvidence, htargetEvidence.
  all: destruct hsourceEvidence as
    (sourceLeftSigma & sourceLeftPi & sourceRightSigma & sourceRightPi &
     hsourceLeft & hsourceRight & hsourceRelation).
  all: destruct htargetEvidence as
    (targetLeftSigma & targetLeftPi & targetRightSigma & targetRightPi &
     htargetLeft & htargetRight & htargetRelation).
  all: destruct (hleft sourceLeftSigma sourceLeftPi
    targetLeftSigma targetLeftPi hsourceLeft htargetLeft)
    as [htargetLeftSigma htargetLeftPi].
  all: destruct (hright sourceRightSigma sourceRightPi
    targetRightSigma targetRightPi hsourceRight htargetRight)
    as [htargetRightSigma htargetRightPi].
  all: subst targetLeftSigma; subst targetLeftPi;
    subst targetRightSigma; subst targetRightPi.
  all: exact (raw_formulaRankAndOr_functional M hPA
    targetSigma targetPi sourceSigma sourcePi
    sourceLeftSigma sourceLeftPi sourceRightSigma sourceRightPi
    htargetRelation hsourceRelation).
Qed.

Lemma raw_formulaOperation_and_rankAgreement : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    sourceLeft sourceRight targetLeft targetRight,
  RawCodedFormulaRankAgreement M sourceLeft targetLeft ->
  RawCodedFormulaRankAgreement M sourceRight targetRight ->
  RawCodedFormulaRankAgreement M
    (rawFormulaAndCode M sourceLeft sourceRight)
    (rawFormulaAndCode M targetLeft targetRight).
Proof.
  intros. eapply raw_formulaOperation_andOr_rankAgreement;
    try eassumption; intros; now left.
Qed.

Lemma raw_formulaOperation_or_rankAgreement : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    sourceLeft sourceRight targetLeft targetRight,
  RawCodedFormulaRankAgreement M sourceLeft targetLeft ->
  RawCodedFormulaRankAgreement M sourceRight targetRight ->
  RawCodedFormulaRankAgreement M
    (rawFormulaOrCode M sourceLeft sourceRight)
    (rawFormulaOrCode M targetLeft targetRight).
Proof.
  intros. eapply raw_formulaOperation_andOr_rankAgreement;
    try eassumption; intros; now right.
Qed.

Lemma raw_formulaOperation_all_rankAgreement : forall
    (M : RawPAModel), RawPASatisfies M -> forall sourceChild targetChild,
  RawCodedFormulaRankAgreement M sourceChild targetChild ->
  RawCodedFormulaRankAgreement M
    (rawFormulaAllCode M sourceChild) (rawFormulaAllCode M targetChild).
Proof.
  intros M hPA sourceChild targetChild hchild
    sourceSigma sourcePi targetSigma targetPi hsource htarget.
  pose proof (raw_codedFormulaRank_shape_evidence
    polynomialPairInjectivityProof M hPA (rawShapeAll sourceChild)
    sourceSigma sourcePi hsource) as hsourceEvidence.
  pose proof (raw_codedFormulaRank_shape_evidence
    polynomialPairInjectivityProof M hPA (rawShapeAll targetChild)
    targetSigma targetPi htarget) as htargetEvidence.
  cbn [RawCodedFormulaShapeRankEvidence] in
    hsourceEvidence, htargetEvidence.
  destruct hsourceEvidence as
    (sourceChildSigma & sourceChildPi & hsourceChild & hsourceRelation).
  destruct htargetEvidence as
    (targetChildSigma & targetChildPi & htargetChild & htargetRelation).
  destruct (hchild sourceChildSigma sourceChildPi
    targetChildSigma targetChildPi hsourceChild htargetChild)
    as [htargetChildSigma htargetChildPi].
  subst targetChildSigma. subst targetChildPi.
  exact (raw_formulaRankAll_functional M hPA
    targetSigma targetPi sourceSigma sourcePi
    sourceChildSigma sourceChildPi htargetRelation hsourceRelation).
Qed.

Lemma raw_formulaOperation_ex_rankAgreement : forall
    (M : RawPAModel), RawPASatisfies M -> forall sourceChild targetChild,
  RawCodedFormulaRankAgreement M sourceChild targetChild ->
  RawCodedFormulaRankAgreement M
    (rawFormulaExCode M sourceChild) (rawFormulaExCode M targetChild).
Proof.
  intros M hPA sourceChild targetChild hchild
    sourceSigma sourcePi targetSigma targetPi hsource htarget.
  pose proof (raw_codedFormulaRank_shape_evidence
    polynomialPairInjectivityProof M hPA (rawShapeEx sourceChild)
    sourceSigma sourcePi hsource) as hsourceEvidence.
  pose proof (raw_codedFormulaRank_shape_evidence
    polynomialPairInjectivityProof M hPA (rawShapeEx targetChild)
    targetSigma targetPi htarget) as htargetEvidence.
  cbn [RawCodedFormulaShapeRankEvidence] in
    hsourceEvidence, htargetEvidence.
  destruct hsourceEvidence as
    (sourceChildSigma & sourceChildPi & hsourceChild & hsourceRelation).
  destruct htargetEvidence as
    (targetChildSigma & targetChildPi & htargetChild & htargetRelation).
  destruct (hchild sourceChildSigma sourceChildPi
    targetChildSigma targetChildPi hsourceChild htargetChild)
    as [htargetChildSigma htargetChildPi].
  subst targetChildSigma. subst targetChildPi.
  exact (raw_formulaRankEx_functional M hPA
    targetSigma targetPi sourceSigma sourcePi
    sourceChildSigma sourceChildPi htargetRelation hsourceRelation).
Qed.

(** Represented operation-table invariant. *)
Definition operationRankPreservationAll4 (body : formula) : formula :=
  pAll (pAll (pAll (pAll body))).

Definition formulaOperationRankAgreementBelowTermAt
    (current sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep : term) : formula :=
  operationRankPreservationAll4
    (pImp
      (Formula.ltTermAt (tVar 3) (liftTerm 4 current))
      (pImp
        (codedFormulaOperationTripleLookupTermAt
          (liftTerm 4 sourceCode) (liftTerm 4 sourceStep)
          (liftTerm 4 targetCode) (liftTerm 4 targetStep)
          (liftTerm 4 depthCode) (liftTerm 4 depthStep)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))
        (pImp
          (Formula.ltTermAt (tVar 2) (liftTerm 4 sourceRoot))
          (pImp
            (Formula.ltTermAt (tVar 1) (liftTerm 4 targetRoot))
            (codedFormulaRankAgreementTermAt (tVar 2) (tVar 1)))))).

Definition RawFormulaOperationRankAgreementBelow (M : RawPAModel)
    (current sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep : M) : Prop :=
  forall index input output depth : M,
    rawLt M index current ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth ->
    rawLt M input sourceRoot ->
    rawLt M output targetRoot ->
    RawCodedFormulaRankAgreement M input output.

Arguments RawFormulaOperationRankAgreementBelow
  M current sourceRoot targetRoot sourceCode sourceStep
    targetCode targetStep depthCode depthStep : clear implicits.

Lemma raw_operationRankPreservation_eval_liftTerm_four : forall
    (M : RawPAModel) a b c d (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b (scons M c (scons M d e))))
    (liftTerm 4 t) = raw_term_eval M e t.
Proof.
  intros M a b c d e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 4) with (S (S (S (S index)))) by lia. reflexivity.
Qed.

Lemma raw_sat_formulaOperationRankAgreementBelowTermAt_iff : forall
    (M : RawPAModel) e current sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep,
  raw_formula_sat M e
    (formulaOperationRankAgreementBelowTermAt
      current sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep) <->
  RawFormulaOperationRankAgreementBelow M
    (raw_term_eval M e current)
    (raw_term_eval M e sourceRoot) (raw_term_eval M e targetRoot)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep).
Proof.
  intros. unfold formulaOperationRankAgreementBelowTermAt,
    operationRankPreservationAll4, RawFormulaOperationRankAgreementBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaOperationTripleLookupTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaRankAgreementTermAt_iff.
  repeat setoid_rewrite raw_operationRankPreservation_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_formulaOperationRankAgreementBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    atom parameter sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound current,
  RawCodedFormulaOperationRows M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound ->
  rawLt M current bound ->
  RawFormulaOperationRankAgreementBelow M current sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep ->
  RawFormulaOperationRankAgreementBelow M (raw_succ M current)
    sourceRoot targetRoot sourceCode sourceStep targetCode targetStep
    depthCode depthStep.
Proof.
  intros M hPA atom parameter sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound current hrows hcurrent hagree
    index input output depth hindex hlookup hinputRoot houtputRoot.
  destruct (raw_lt_succ_cases M hPA index current hindex)
    as [hbelow | hequal].
  - exact (hagree index input output depth hbelow hlookup
      hinputRoot houtputRoot).
  - subst index.
    pose proof (hrows current input output depth hcurrent hlookup) as hrow.
    destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
    + destruct heq as
        (sourceLeft & targetLeft & sourceRight & targetRight &
         hinput & houtput & _ & _).
      subst input. subst output.
      apply raw_formulaOperation_eq_rankAgreement. exact hPA.
    + destruct hbot as [hinput houtput].
      subst input. subst output.
      apply raw_formulaOperation_bot_rankAgreement. exact hPA.
    + destruct himp as
        (leftIndex & sourceLeft & targetLeft & leftDepth &
         rightIndex & sourceRight & targetRight & rightDepth &
         hleftIndex & hleftLookup & _ &
         hrightIndex & hrightLookup & _ & hinput & houtput).
      subst input. subst output.
      apply raw_formulaOperation_imp_rankAgreement; [exact hPA | |].
      * exact (hagree leftIndex sourceLeft targetLeft leftDepth
          hleftIndex hleftLookup
          (raw_assignment_lt_trans M hPA sourceLeft
            (rawFormulaImpCode M sourceLeft sourceRight) sourceRoot
            (raw_formulaOperation_binary_left_lt M hPA _
              sourceLeft sourceRight)
            hinputRoot)
          (raw_assignment_lt_trans M hPA targetLeft
            (rawFormulaImpCode M targetLeft targetRight) targetRoot
            (raw_formulaOperation_binary_left_lt M hPA _
              targetLeft targetRight)
            houtputRoot)).
      * exact (hagree rightIndex sourceRight targetRight rightDepth
          hrightIndex hrightLookup
          (raw_assignment_lt_trans M hPA sourceRight
            (rawFormulaImpCode M sourceLeft sourceRight) sourceRoot
            (raw_formulaOperation_binary_right_lt M hPA _
              sourceLeft sourceRight)
            hinputRoot)
          (raw_assignment_lt_trans M hPA targetRight
            (rawFormulaImpCode M targetLeft targetRight) targetRoot
            (raw_formulaOperation_binary_right_lt M hPA _
              targetLeft targetRight)
            houtputRoot)).
    + destruct hand as
        (leftIndex & sourceLeft & targetLeft & leftDepth &
         rightIndex & sourceRight & targetRight & rightDepth &
         hleftIndex & hleftLookup & _ &
         hrightIndex & hrightLookup & _ & hinput & houtput).
      subst input. subst output.
      apply raw_formulaOperation_and_rankAgreement; [exact hPA | |].
      * exact (hagree leftIndex sourceLeft targetLeft leftDepth
          hleftIndex hleftLookup
          (raw_assignment_lt_trans M hPA sourceLeft
            (rawFormulaAndCode M sourceLeft sourceRight) sourceRoot
            (raw_formulaOperation_binary_left_lt M hPA _
              sourceLeft sourceRight)
            hinputRoot)
          (raw_assignment_lt_trans M hPA targetLeft
            (rawFormulaAndCode M targetLeft targetRight) targetRoot
            (raw_formulaOperation_binary_left_lt M hPA _
              targetLeft targetRight)
            houtputRoot)).
      * exact (hagree rightIndex sourceRight targetRight rightDepth
          hrightIndex hrightLookup
          (raw_assignment_lt_trans M hPA sourceRight
            (rawFormulaAndCode M sourceLeft sourceRight) sourceRoot
            (raw_formulaOperation_binary_right_lt M hPA _
              sourceLeft sourceRight)
            hinputRoot)
          (raw_assignment_lt_trans M hPA targetRight
            (rawFormulaAndCode M targetLeft targetRight) targetRoot
            (raw_formulaOperation_binary_right_lt M hPA _
              targetLeft targetRight)
            houtputRoot)).
    + destruct hor as
        (leftIndex & sourceLeft & targetLeft & leftDepth &
         rightIndex & sourceRight & targetRight & rightDepth &
         hleftIndex & hleftLookup & _ &
         hrightIndex & hrightLookup & _ & hinput & houtput).
      subst input. subst output.
      apply raw_formulaOperation_or_rankAgreement; [exact hPA | |].
      * exact (hagree leftIndex sourceLeft targetLeft leftDepth
          hleftIndex hleftLookup
          (raw_assignment_lt_trans M hPA sourceLeft
            (rawFormulaOrCode M sourceLeft sourceRight) sourceRoot
            (raw_formulaOperation_binary_left_lt M hPA _
              sourceLeft sourceRight)
            hinputRoot)
          (raw_assignment_lt_trans M hPA targetLeft
            (rawFormulaOrCode M targetLeft targetRight) targetRoot
            (raw_formulaOperation_binary_left_lt M hPA _
              targetLeft targetRight)
            houtputRoot)).
      * exact (hagree rightIndex sourceRight targetRight rightDepth
          hrightIndex hrightLookup
          (raw_assignment_lt_trans M hPA sourceRight
            (rawFormulaOrCode M sourceLeft sourceRight) sourceRoot
            (raw_formulaOperation_binary_right_lt M hPA _
              sourceLeft sourceRight)
            hinputRoot)
          (raw_assignment_lt_trans M hPA targetRight
            (rawFormulaOrCode M targetLeft targetRight) targetRoot
            (raw_formulaOperation_binary_right_lt M hPA _
              targetLeft targetRight)
            houtputRoot)).
    + destruct hall as
        (childIndex & sourceChild & targetChild & childDepth &
         hchildIndex & hchildLookup & _ & hinput & houtput).
      subst input. subst output.
      apply raw_formulaOperation_all_rankAgreement; [exact hPA |].
      exact (hagree childIndex sourceChild targetChild childDepth
        hchildIndex hchildLookup
        (raw_assignment_lt_trans M hPA sourceChild
          (rawFormulaAllCode M sourceChild) sourceRoot
          (raw_formulaOperation_unary_child_lt M hPA _ sourceChild)
          hinputRoot)
        (raw_assignment_lt_trans M hPA targetChild
          (rawFormulaAllCode M targetChild) targetRoot
          (raw_formulaOperation_unary_child_lt M hPA _ targetChild)
          houtputRoot)).
    + destruct hex as
        (childIndex & sourceChild & targetChild & childDepth &
         hchildIndex & hchildLookup & _ & hinput & houtput).
      subst input. subst output.
      apply raw_formulaOperation_ex_rankAgreement; [exact hPA |].
      exact (hagree childIndex sourceChild targetChild childDepth
        hchildIndex hchildLookup
        (raw_assignment_lt_trans M hPA sourceChild
          (rawFormulaExCode M sourceChild) sourceRoot
          (raw_formulaOperation_unary_child_lt M hPA _ sourceChild)
          hinputRoot)
        (raw_assignment_lt_trans M hPA targetChild
          (rawFormulaExCode M targetChild) targetRoot
          (raw_formulaOperation_unary_child_lt M hPA _ targetChild)
          houtputRoot)).
Qed.

Definition formulaOperationRankAgreementThroughTermAt
    (current limit sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep : term) : formula :=
  pImp (Formula.leTermAt current limit)
    (formulaOperationRankAgreementBelowTermAt
      current sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep).

Definition RawFormulaOperationRankAgreementThrough (M : RawPAModel)
    (current limit sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep : M) : Prop :=
  rawLe M current limit ->
  RawFormulaOperationRankAgreementBelow M current sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep.

Lemma raw_sat_formulaOperationRankAgreementThroughTermAt_iff : forall
    (M : RawPAModel) e current limit sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep,
  raw_formula_sat M e
    (formulaOperationRankAgreementThroughTermAt
      current limit sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep) <->
  RawFormulaOperationRankAgreementThrough M
    (raw_term_eval M e current) (raw_term_eval M e limit)
    (raw_term_eval M e sourceRoot) (raw_term_eval M e targetRoot)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep).
Proof.
  intros. unfold formulaOperationRankAgreementThroughTermAt,
    RawFormulaOperationRankAgreementThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_traversal,
    raw_sat_formulaOperationRankAgreementBelowTermAt_iff.
  tauto.
Qed.

Theorem raw_formulaOperationRankAgreementBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall atom parameter
    sourceRoot targetRoot sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound,
  RawCodedFormulaOperationRows M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound ->
  RawFormulaOperationRankAgreementBelow M bound sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep.
Proof.
  intros M hPA atom parameter sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound hrows.
  set (parameterEnv := scons M bound
    (scons M sourceRoot (scons M targetRoot
      (scons M sourceCode (scons M sourceStep
        (scons M targetCode (scons M targetStep
          (scons M depthCode (scons M depthStep
            (fun _ : nat => raw_zero M)))))))))).
  set (phi := formulaOperationRankAgreementThroughTermAt
    (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4)
    (tVar 5) (tVar 6) (tVar 7) (tVar 8) (tVar 9)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_formulaOperationRankAgreementThroughTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7) (tVar 8) (tVar 9))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _ index input output depth hindex.
      exfalso. exact (raw_not_lt_zero M hPA index hindex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_formulaOperationRankAgreementThroughTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7) (tVar 8) (tVar 9)) hcurrent)
        as hcurrentRaw.
      apply (proj2
        (raw_sat_formulaOperationRankAgreementThroughTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7) (tVar 8) (tVar 9))).
      unfold parameterEnv in hcurrentRaw |- *.
      cbn [raw_term_eval scons] in hcurrentRaw |- *.
      intro hsuccLe.
      assert (hcurrentBound : rawLt M current bound).
      { exact (raw_lt_of_succ_le_traversal M hPA current bound hsuccLe). }
      exact (raw_formulaOperationRankAgreementBelow_succ M hPA
        atom parameter sourceRoot targetRoot
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound current hrows hcurrentBound
        (hcurrentRaw (raw_lt_to_le M current bound hcurrentBound))).
  }
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_formulaOperationRankAgreementThroughTermAt_iff M
      (scons M bound parameterEnv)
      (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4)
      (tVar 5) (tVar 6) (tVar 7) (tVar 8) (tVar 9))
    (hall bound)) as hbound.
  unfold parameterEnv in hbound. cbn [raw_term_eval scons] in hbound.
  exact (hbound (raw_le_refl_traversal M hPA bound)).
Qed.

Theorem raw_formulaOperationTrace_rankAgreement_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    atom parameter rootDepth source target
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex,
  RawCodedFormulaOperationTrace M atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex source target ->
  RawCodedFormulaRankAgreement M source target.
Proof.
  intros M hPA atom parameter rootDepth source target
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex (_ & _ & _ & hroot & hrootLookup & hrows).
  pose proof (raw_formulaOperationRankAgreementBelow_all M hPA
    atom parameter (raw_succ M source) (raw_succ M target)
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound hrows) as hall.
  exact (hall rootIndex source target rootDepth
    hroot hrootLookup
    (raw_assignment_lt_self_succ M hPA source)
    (raw_assignment_lt_self_succ M hPA target)).
Qed.

Theorem raw_codedFormulaOperation_rank_preserving_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall atom,
  RawCodedFormulaOperationRankPreserving M atom.
Proof.
  intros M hPA atom parameter rootDepth input output
    sigma pi outputSigma outputPi
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace)
    hinputRank houtputRank.
  exact (raw_formulaOperationTrace_rankAgreement_all M hPA
    atom parameter rootDepth input output
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex htrace
    sigma pi outputSigma outputPi hinputRank houtputRank).
Qed.

Theorem raw_codedFormulaShift_rank_preserving_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaShiftRankPreserving M.
Proof.
  intros M hPA.
  apply raw_codedFormulaShift_rank_preserving_of_generic.
  apply raw_codedFormulaOperation_rank_preserving_all. exact hPA.
Qed.

Theorem raw_codedFormulaSingleSubstitution_rank_preserving_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaSingleSubstitutionRankPreserving M.
Proof.
  intros M hPA.
  apply raw_codedFormulaSingleSubstitution_rank_preserving_of_generic.
  apply raw_codedFormulaOperation_rank_preserving_all. exact hPA.
Qed.

Corollary raw_codedFormulaShift_rankAgreement_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount source target,
  RawCodedFormulaShift M cutoff amount source target ->
  RawCodedFormulaRankAgreement M source target.
Proof.
  intros M hPA cutoff amount source target hoperation.
  exact (raw_codedFormulaShift_rankAgreement M
    (raw_codedFormulaShift_rank_preserving_all M hPA)
    cutoff amount source target hoperation).
Qed.

Corollary raw_codedFormulaSingleSubstitution_rankAgreement_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement source target,
  RawCodedFormulaSingleSubstitution M replacement source target ->
  RawCodedFormulaRankAgreement M source target.
Proof.
  intros M hPA replacement source target hoperation.
  exact (raw_codedFormulaSingleSubstitution_rankAgreement M
    (raw_codedFormulaSingleSubstitution_rank_preserving_all M hPA)
    replacement source target hoperation).
Qed.

End PABoundedRawCodedFormulaOperationRankPreservation.
