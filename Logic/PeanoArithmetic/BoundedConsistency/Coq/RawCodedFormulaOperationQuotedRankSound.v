(**
  Formula operations preserve the hierarchy rank of a standard source.

  An operation trace may contain nonstandard term payloads and need not be
  the canonical trace constructed by the standard-realization development.
  Nevertheless, every row preserves the outer formula constructor.  This
  file records that constructor-skeleton invariant and uses ordinary
  structural induction on the quoted source formula.  Consequently every
  output of an arbitrary trace rooted at a standard quotation has exactly
  the quoted source's sigma/pi ranks.
*)

From Stdlib Require Import List Arith Lia Program.Equality.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedSyntax PolynomialPairInjectivity RawCodedAssignment
  RawCodedSyntaxConstructors RawCodedSyntaxConstructorSeparation
  RawCodedFormulaRankStep RawCodedFormulaRankStepFunctionality
  RawCodedFormulaRankTraversal RawCodedFormulaRankRealization
  RawCodedFormulaRankTotality RawCodedFormulaOperations
  RawCodedContextBounds.

Module PABoundedRawCodedFormulaOperationQuotedRankSound.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedConsistency.
Import PABoundedCodedSyntax.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankStepFunctionality.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankRealization.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextBounds.

(** The indexed relation deliberately forgets transformed atomic terms and
    depth equations.  It retains exactly the child lookup rows needed to
    re-root an operation trace during the meta-level structural induction. *)
Inductive RawCodedFormulaOperationShapeRow
    (M : RawPAModel) (atom : M -> M -> M -> M -> Prop)
    (parameter sourceCode sourceStep targetCode targetStep
      depthCode depthStep index depth : M)
    : RawCodedFormulaShape M -> RawCodedFormulaShape M -> Prop :=
| rawOperationShapeEq : forall inputLeft outputLeft inputRight outputRight,
    RawCodedFormulaOperationShapeRow M atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index depth
      (rawShapeEq inputLeft inputRight)
      (rawShapeEq outputLeft outputRight)
| rawOperationShapeBot :
    RawCodedFormulaOperationShapeRow M atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index depth rawShapeBot rawShapeBot
| rawOperationShapeImp : forall
      leftIndex inputLeft outputLeft leftDepth
      rightIndex inputRight outputRight rightDepth,
    rawLt M leftIndex index ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      leftIndex inputLeft outputLeft leftDepth ->
    rawLt M rightIndex index ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      rightIndex inputRight outputRight rightDepth ->
    RawCodedFormulaOperationShapeRow M atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index depth
      (rawShapeImp inputLeft inputRight)
      (rawShapeImp outputLeft outputRight)
| rawOperationShapeAnd : forall
      leftIndex inputLeft outputLeft leftDepth
      rightIndex inputRight outputRight rightDepth,
    rawLt M leftIndex index ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      leftIndex inputLeft outputLeft leftDepth ->
    rawLt M rightIndex index ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      rightIndex inputRight outputRight rightDepth ->
    RawCodedFormulaOperationShapeRow M atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index depth
      (rawShapeAnd inputLeft inputRight)
      (rawShapeAnd outputLeft outputRight)
| rawOperationShapeOr : forall
      leftIndex inputLeft outputLeft leftDepth
      rightIndex inputRight outputRight rightDepth,
    rawLt M leftIndex index ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      leftIndex inputLeft outputLeft leftDepth ->
    rawLt M rightIndex index ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      rightIndex inputRight outputRight rightDepth ->
    RawCodedFormulaOperationShapeRow M atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index depth
      (rawShapeOr inputLeft inputRight)
      (rawShapeOr outputLeft outputRight)
| rawOperationShapeAll : forall
      childIndex inputChild outputChild childDepth,
    rawLt M childIndex index ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      childIndex inputChild outputChild childDepth ->
    RawCodedFormulaOperationShapeRow M atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index depth
      (rawShapeAll inputChild) (rawShapeAll outputChild)
| rawOperationShapeEx : forall
      childIndex inputChild outputChild childDepth,
    rawLt M childIndex index ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      childIndex inputChild outputChild childDepth ->
    RawCodedFormulaOperationShapeRow M atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index depth
      (rawShapeEx inputChild) (rawShapeEx outputChild).

Arguments RawCodedFormulaOperationShapeRow
  M atom parameter sourceCode sourceStep targetCode targetStep
  depthCode depthStep index depth sourceShape targetShape : clear implicits.

Lemma raw_formulaOperationTraversalRow_shapes : forall
    (M : RawPAModel) atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth,
  RawCodedFormulaOperationTraversalRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth ->
  exists sourceShape targetShape,
    input = rawCodedFormulaShapeCode M sourceShape /\
    output = rawCodedFormulaShapeCode M targetShape /\
    RawCodedFormulaOperationShapeRow M atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index depth sourceShape targetShape.
Proof.
  intros M atom parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth hrow.
  destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - destruct heq as
      (inputLeft & outputLeft & inputRight & outputRight &
       hinput & houtput & _ & _).
    exists (rawShapeEq inputLeft inputRight),
      (rawShapeEq outputLeft outputRight).
    split; [exact hinput |]. split; [exact houtput |].
    constructor.
  - exists rawShapeBot, rawShapeBot.
    split; [exact (proj1 hbot) |].
    split; [exact (proj2 hbot) | constructor].
  - destruct himp as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       hinput & houtput).
    exists (rawShapeImp inputLeft inputRight),
      (rawShapeImp outputLeft outputRight).
    split; [exact hinput |]. split; [exact houtput |].
    apply rawOperationShapeImp with
      (leftIndex := leftIndex) (leftDepth := leftDepth)
      (rightIndex := rightIndex) (rightDepth := rightDepth);
      assumption.
  - destruct hand as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       hinput & houtput).
    exists (rawShapeAnd inputLeft inputRight),
      (rawShapeAnd outputLeft outputRight).
    split; [exact hinput |]. split; [exact houtput |].
    apply rawOperationShapeAnd with
      (leftIndex := leftIndex) (leftDepth := leftDepth)
      (rightIndex := rightIndex) (rightDepth := rightDepth);
      assumption.
  - destruct hor as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       hinput & houtput).
    exists (rawShapeOr inputLeft inputRight),
      (rawShapeOr outputLeft outputRight).
    split; [exact hinput |]. split; [exact houtput |].
    apply rawOperationShapeOr with
      (leftIndex := leftIndex) (leftDepth := leftDepth)
      (rightIndex := rightIndex) (rightDepth := rightDepth);
      assumption.
  - destruct hall as
      (childIndex & inputChild & outputChild & childDepth &
       hchildIndex & hchildLookup & _ & hinput & houtput).
    exists (rawShapeAll inputChild), (rawShapeAll outputChild).
    split; [exact hinput |]. split; [exact houtput |].
    apply rawOperationShapeAll with
      (childIndex := childIndex) (childDepth := childDepth);
      assumption.
  - destruct hex as
      (childIndex & inputChild & outputChild & childDepth &
       hchildIndex & hchildLookup & _ & hinput & houtput).
    exists (rawShapeEx inputChild), (rawShapeEx outputChild).
    split; [exact hinput |]. split; [exact houtput |].
    apply rawOperationShapeEx with
      (childIndex := childIndex) (childDepth := childDepth);
      assumption.
Qed.

(** Typed inversion lemmas keep the main rank proof independent of names
    generated by [inversion] for the seven indexed constructors. *)
Section OperationShapeInversion.

Context {M : RawPAModel} {atom : M -> M -> M -> M -> Prop}
  {parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep index depth : M}.

Lemma raw_operationShapeEq_inv : forall inputLeft inputRight targetShape,
  RawCodedFormulaOperationShapeRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index depth (rawShapeEq inputLeft inputRight) targetShape ->
  exists outputLeft outputRight,
    targetShape = rawShapeEq outputLeft outputRight.
Proof. intros inputLeft inputRight targetShape h; dependent destruction h; eauto. Qed.

Lemma raw_operationShapeBot_inv : forall targetShape,
  RawCodedFormulaOperationShapeRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index depth rawShapeBot targetShape ->
  targetShape = rawShapeBot.
Proof. intros targetShape h; dependent destruction h; reflexivity. Qed.

Lemma raw_operationShapeImp_inv : forall inputLeft inputRight targetShape,
  RawCodedFormulaOperationShapeRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index depth (rawShapeImp inputLeft inputRight) targetShape ->
  exists leftIndex outputLeft leftDepth
      rightIndex outputRight rightDepth,
    targetShape = rawShapeImp outputLeft outputRight /\
    rawLt M leftIndex index /\
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      leftIndex inputLeft outputLeft leftDepth /\
    rawLt M rightIndex index /\
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      rightIndex inputRight outputRight rightDepth.
Proof.
  intros inputLeft inputRight targetShape h. dependent destruction h.
  exists leftIndex, outputLeft, leftDepth,
    rightIndex, outputRight, rightDepth.
  split; [reflexivity |]. split; [assumption |].
  split; [assumption |]. split; assumption.
Qed.

Lemma raw_operationShapeAnd_inv : forall inputLeft inputRight targetShape,
  RawCodedFormulaOperationShapeRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index depth (rawShapeAnd inputLeft inputRight) targetShape ->
  exists leftIndex outputLeft leftDepth
      rightIndex outputRight rightDepth,
    targetShape = rawShapeAnd outputLeft outputRight /\
    rawLt M leftIndex index /\
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      leftIndex inputLeft outputLeft leftDepth /\
    rawLt M rightIndex index /\
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      rightIndex inputRight outputRight rightDepth.
Proof.
  intros inputLeft inputRight targetShape h. dependent destruction h.
  exists leftIndex, outputLeft, leftDepth,
    rightIndex, outputRight, rightDepth.
  split; [reflexivity |]. split; [assumption |].
  split; [assumption |]. split; assumption.
Qed.

Lemma raw_operationShapeOr_inv : forall inputLeft inputRight targetShape,
  RawCodedFormulaOperationShapeRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index depth (rawShapeOr inputLeft inputRight) targetShape ->
  exists leftIndex outputLeft leftDepth
      rightIndex outputRight rightDepth,
    targetShape = rawShapeOr outputLeft outputRight /\
    rawLt M leftIndex index /\
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      leftIndex inputLeft outputLeft leftDepth /\
    rawLt M rightIndex index /\
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      rightIndex inputRight outputRight rightDepth.
Proof.
  intros inputLeft inputRight targetShape h. dependent destruction h.
  exists leftIndex, outputLeft, leftDepth,
    rightIndex, outputRight, rightDepth.
  split; [reflexivity |]. split; [assumption |].
  split; [assumption |]. split; assumption.
Qed.

Lemma raw_operationShapeAll_inv : forall inputChild targetShape,
  RawCodedFormulaOperationShapeRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index depth (rawShapeAll inputChild) targetShape ->
  exists childIndex outputChild childDepth,
    targetShape = rawShapeAll outputChild /\
    rawLt M childIndex index /\
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      childIndex inputChild outputChild childDepth.
Proof.
  intros inputChild targetShape h. dependent destruction h.
  exists childIndex, outputChild, childDepth.
  split; [reflexivity |]. split; assumption.
Qed.

Lemma raw_operationShapeEx_inv : forall inputChild targetShape,
  RawCodedFormulaOperationShapeRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index depth (rawShapeEx inputChild) targetShape ->
  exists childIndex outputChild childDepth,
    targetShape = rawShapeEx outputChild /\
    rawLt M childIndex index /\
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      childIndex inputChild outputChild childDepth.
Proof.
  intros inputChild targetShape h. dependent destruction h.
  exists childIndex, outputChild, childDepth.
  split; [reflexivity |]. split; assumption.
Qed.

End OperationShapeInversion.

(** A traversal rooted at a known constructor shape yields standalone rank
    certificates for that constructor's children.  Restricting the original
    traversal at each child row is essential: no decoding of carrier values
    or reconstruction of a second traversal is involved. *)
Definition RawCodedFormulaShapeRankEvidence (M : RawPAModel)
    (shape : RawCodedFormulaShape M) (sigma pi : M) : Prop :=
  match shape with
  | rawShapeEq _ _ => RawFormulaRankZero M sigma pi
  | rawShapeBot => RawFormulaRankZero M sigma pi
  | rawShapeImp leftChild rightChild =>
      exists leftSigma leftPi rightSigma rightPi,
        RawCodedFormulaRank M leftChild leftSigma leftPi /\
        RawCodedFormulaRank M rightChild rightSigma rightPi /\
        RawFormulaRankImp M sigma pi
          leftSigma leftPi rightSigma rightPi
  | rawShapeAnd leftChild rightChild =>
      exists leftSigma leftPi rightSigma rightPi,
        RawCodedFormulaRank M leftChild leftSigma leftPi /\
        RawCodedFormulaRank M rightChild rightSigma rightPi /\
        RawFormulaRankAndOr M sigma pi
          leftSigma leftPi rightSigma rightPi
  | rawShapeOr leftChild rightChild =>
      exists leftSigma leftPi rightSigma rightPi,
        RawCodedFormulaRank M leftChild leftSigma leftPi /\
        RawCodedFormulaRank M rightChild rightSigma rightPi /\
        RawFormulaRankAndOr M sigma pi
          leftSigma leftPi rightSigma rightPi
  | rawShapeAll child =>
      exists childSigma childPi,
        RawCodedFormulaRank M child childSigma childPi /\
        RawFormulaRankAll M sigma pi childSigma childPi
  | rawShapeEx child =>
      exists childSigma childPi,
        RawCodedFormulaRank M child childSigma childPi /\
        RawFormulaRankEx M sigma pi childSigma childPi
  end.

Arguments RawCodedFormulaShapeRankEvidence M shape sigma pi
  : clear implicits.

Theorem raw_codedFormulaRank_shape_evidence :
  PolynomialPairInjectivityProof ->
  forall (M : RawPAModel), RawPASatisfies M ->
  forall shape sigma pi,
  RawCodedFormulaRank M (rawCodedFormulaShapeCode M shape) sigma pi ->
  RawCodedFormulaShapeRankEvidence M shape sigma pi.
Proof.
  intros hpairProof M hPA shape sigma pi
    (formulaCode & formulaStep & sigmaCode & sigmaStep &
     piCode & piStep & bound & rootIndex & htraversal).
  pose proof (raw_codedFormulaRankTraversal_root_row M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex (rawCodedFormulaShapeCode M shape)
    sigma pi htraversal) as hrootRow.
  apply raw_codedFormulaRankTraversalRow_shape_iff in hrootRow.
  destruct hrootRow as [rowShape [hrowCode hshapeRank]].
  assert (hrowShape : rowShape = shape).
  {
    apply (rawCodedFormulaShapeCode_injective hpairProof M hPA).
    symmetry. exact hrowCode.
  }
  subst rowShape.
  pose proof htraversal as htraversalFacts.
  destruct htraversalFacts as [_ [_ [_ [hrootBound _]]]].
  destruct shape as
      [leftChild rightChild | | leftChild rightChild |
       leftChild rightChild | leftChild rightChild | child | child];
    cbn [RawCodedFormulaShapeRankEvidence
      RawCodedFormulaShapeRankRow] in hshapeRank |- *.
  - exact hshapeRank.
  - exact hshapeRank.
  - destruct hshapeRank as
      (leftIndex & leftSigma & leftPi & rightIndex & rightSigma & rightPi &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup & hrank).
    assert (hleftBound : rawLt M leftIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        leftIndex rootIndex bound hleftIndex hrootBound).
    assert (hrightBound : rawLt M rightIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        rightIndex rootIndex bound hrightIndex hrootBound).
    exists leftSigma, leftPi, rightSigma, rightPi.
    split.
    + exact (raw_codedFormulaRank_of_traversal_row M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawFormulaImpCode M leftChild rightChild) sigma pi
        htraversal leftIndex leftChild leftSigma leftPi
        hleftBound hleftLookup).
    + split.
      * exact (raw_codedFormulaRank_of_traversal_row M hPA
          formulaCode formulaStep sigmaCode sigmaStep piCode piStep
          bound rootIndex (rawFormulaImpCode M leftChild rightChild) sigma pi
          htraversal rightIndex rightChild rightSigma rightPi
          hrightBound hrightLookup).
      * exact hrank.
  - destruct hshapeRank as
      (leftIndex & leftSigma & leftPi & rightIndex & rightSigma & rightPi &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup & hrank).
    assert (hleftBound : rawLt M leftIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        leftIndex rootIndex bound hleftIndex hrootBound).
    assert (hrightBound : rawLt M rightIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        rightIndex rootIndex bound hrightIndex hrootBound).
    exists leftSigma, leftPi, rightSigma, rightPi.
    split.
    + exact (raw_codedFormulaRank_of_traversal_row M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawFormulaAndCode M leftChild rightChild) sigma pi
        htraversal leftIndex leftChild leftSigma leftPi
        hleftBound hleftLookup).
    + split.
      * exact (raw_codedFormulaRank_of_traversal_row M hPA
          formulaCode formulaStep sigmaCode sigmaStep piCode piStep
          bound rootIndex (rawFormulaAndCode M leftChild rightChild) sigma pi
          htraversal rightIndex rightChild rightSigma rightPi
          hrightBound hrightLookup).
      * exact hrank.
  - destruct hshapeRank as
      (leftIndex & leftSigma & leftPi & rightIndex & rightSigma & rightPi &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup & hrank).
    assert (hleftBound : rawLt M leftIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        leftIndex rootIndex bound hleftIndex hrootBound).
    assert (hrightBound : rawLt M rightIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        rightIndex rootIndex bound hrightIndex hrootBound).
    exists leftSigma, leftPi, rightSigma, rightPi.
    split.
    + exact (raw_codedFormulaRank_of_traversal_row M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawFormulaOrCode M leftChild rightChild) sigma pi
        htraversal leftIndex leftChild leftSigma leftPi
        hleftBound hleftLookup).
    + split.
      * exact (raw_codedFormulaRank_of_traversal_row M hPA
          formulaCode formulaStep sigmaCode sigmaStep piCode piStep
          bound rootIndex (rawFormulaOrCode M leftChild rightChild) sigma pi
          htraversal rightIndex rightChild rightSigma rightPi
          hrightBound hrightLookup).
      * exact hrank.
  - destruct hshapeRank as
      (childIndex & childSigma & childPi &
       hchildIndex & hchildLookup & hrank).
    assert (hchildBound : rawLt M childIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        childIndex rootIndex bound hchildIndex hrootBound).
    exists childSigma, childPi. split.
    + exact (raw_codedFormulaRank_of_traversal_row M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawFormulaAllCode M child) sigma pi
        htraversal childIndex child childSigma childPi
        hchildBound hchildLookup).
    + exact hrank.
  - destruct hshapeRank as
      (childIndex & childSigma & childPi &
       hchildIndex & hchildLookup & hrank).
    assert (hchildBound : rawLt M childIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        childIndex rootIndex bound hchildIndex hrootBound).
    exists childSigma, childPi. split.
    + exact (raw_codedFormulaRank_of_traversal_row M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawFormulaExCode M child) sigma pi
        htraversal childIndex child childSigma childPi
        hchildBound hchildLookup).
    + exact hrank.
Qed.

(** Any advertised child row can serve as the root of the same operation
    tables.  The only new global fact is that the child index is below the
    table bound, obtained by transitivity through the old root. *)
Lemma raw_formulaOperationTrace_reroot : forall (M : RawPAModel),
  RawPASatisfies M -> forall atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output,
  RawCodedFormulaOperationTrace M atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output ->
  forall childIndex childInput childOutput childDepth,
  rawLt M childIndex rootIndex ->
  RawCodedFormulaOperationTripleLookup M
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    childIndex childInput childOutput childDepth ->
  RawCodedFormulaOperation M atom parameter childDepth
    childInput childOutput.
Proof.
  intros M hPA atom parameter rootDepth sourceCode sourceStep
    targetCode targetStep depthCode depthStep bound rootIndex input output
    htrace childIndex childInput childOutput childDepth
    hchildIndex hchildLookup.
  destruct htrace as
    (hsourceDefined & htargetDefined & hdepthDefined & hrootBelow &
     hrootLookup & hrows).
  exists sourceCode, sourceStep, targetCode, targetStep,
    depthCode, depthStep, bound, childIndex.
  split; [exact hsourceDefined |].
  split; [exact htargetDefined |].
  split; [exact hdepthDefined |].
  split.
  - exact (raw_assignment_lt_trans M hPA
      childIndex rootIndex bound hchildIndex hrootBelow).
  - split; [exact hchildLookup | exact hrows].
Qed.

(** The main cross-trace theorem.  Its source is standard, but its output and
    all three operation tables may be nonstandard.  Only the finite external
    formula is recursed over. *)
Theorem raw_codedFormulaOperation_quoted_rank_sound :
  PolynomialPairInjectivityProof ->
  forall (M : RawPAModel), RawPASatisfies M ->
  forall phi atom parameter rootDepth output sigma pi,
  RawCodedFormulaOperation M atom parameter rootDepth
    (rawQuotedFormulaCode M phi) output ->
  RawCodedFormulaRank M output sigma pi ->
  sigma = rawNumeralValue M (sigmaRank phi) /\
  pi = rawNumeralValue M (piRank phi).
Proof.
  intros hpairProof M hPA phi.
  induction phi as
      [leftTerm rightTerm
      | (* bottom *)
      | leftFormula IHleft rightFormula IHright
      | leftFormula IHleft rightFormula IHright
      | leftFormula IHleft rightFormula IHright
      | child IHchild
      | child IHchild];
    intros atom parameter rootDepth output sigma pi
      (sourceCode & sourceStep & targetCode & targetStep &
       depthCode & depthStep & bound & rootIndex & htrace) hrank.
  all: pose proof htrace as htraceFacts.
  all: destruct htraceFacts as
      (hsourceDefined & htargetDefined & hdepthDefined & hrootBelow &
       hrootLookup & hrows).
  all: pose proof (hrows rootIndex _ _ _ hrootBelow hrootLookup)
      as hoperationRow.
  all: destruct (raw_formulaOperationTraversalRow_shapes M atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      rootIndex _ _ rootDepth hoperationRow) as
      (sourceShape & targetShape & hsourceCode & htargetCode & hshapeRow).
  all: match goal with
  | |- _ = rawNumeralValue _ (sigmaRank ?currentFormula) /\ _ =>
      assert (hsourceShape :
        sourceShape = rawQuotedFormulaShape M currentFormula) by
        (apply (rawCodedFormulaShapeCode_injective hpairProof M hPA);
         rewrite rawQuotedFormulaShape_code;
         symmetry; exact hsourceCode)
  end.
  all: subst sourceShape.
  all: assert (htargetRank :
      RawCodedFormulaRank M
        (rawCodedFormulaShapeCode M targetShape) sigma pi) by
      (rewrite <- htargetCode; exact hrank).
  all: pose proof (raw_codedFormulaRank_shape_evidence
      hpairProof M hPA targetShape sigma pi htargetRank) as hevidence.
  - destruct (raw_operationShapeEq_inv
      (rawQuotedTermCode M leftTerm) (rawQuotedTermCode M rightTerm)
      targetShape hshapeRow) as
      (outputLeft & outputRight & htargetShape).
    subst targetShape.
    exact hevidence.
  - pose proof (raw_operationShapeBot_inv targetShape hshapeRow)
      as htargetShape.
    subst targetShape.
    exact hevidence.
  - destruct (raw_operationShapeImp_inv
      (rawQuotedFormulaCode M leftFormula)
      (rawQuotedFormulaCode M rightFormula) targetShape hshapeRow) as
      (leftIndex & outputLeft & leftDepth &
       rightIndex & outputRight & rightDepth &
       htargetShape & hleftIndex & hleftLookup &
       hrightIndex & hrightLookup).
    subst targetShape.
    cbn [RawCodedFormulaShapeRankEvidence] in hevidence.
    destruct hevidence as
      (leftSigma & leftPi & rightSigma & rightPi &
       hleftRank & hrightRank & hrankRelation).
    pose proof (raw_formulaOperationTrace_reroot M hPA
      atom parameter rootDepth sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound rootIndex
      (rawQuotedFormulaCode M (pImp leftFormula rightFormula)) output
      htrace leftIndex (rawQuotedFormulaCode M leftFormula)
      outputLeft leftDepth hleftIndex hleftLookup) as hleftOperation.
    pose proof (raw_formulaOperationTrace_reroot M hPA
      atom parameter rootDepth sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound rootIndex
      (rawQuotedFormulaCode M (pImp leftFormula rightFormula)) output
      htrace rightIndex (rawQuotedFormulaCode M rightFormula)
      outputRight rightDepth hrightIndex hrightLookup) as hrightOperation.
    destruct (IHleft atom parameter leftDepth outputLeft
      leftSigma leftPi hleftOperation hleftRank) as
      [hleftSigma hleftPi].
    destruct (IHright atom parameter rightDepth outputRight
      rightSigma rightPi hrightOperation hrightRank) as
      [hrightSigma hrightPi].
    rewrite hleftSigma, hleftPi, hrightSigma, hrightPi in hrankRelation.
    exact (raw_formulaRankImp_functional M hPA
      sigma pi
      (rawNumeralValue M
        (Nat.max (piRank leftFormula) (sigmaRank rightFormula)))
      (rawNumeralValue M
        (Nat.max (sigmaRank leftFormula) (piRank rightFormula)))
      (rawNumeralValue M (sigmaRank leftFormula))
      (rawNumeralValue M (piRank leftFormula))
      (rawNumeralValue M (sigmaRank rightFormula))
      (rawNumeralValue M (piRank rightFormula))
      hrankRelation
      (raw_formulaRankImp_numerals M hPA
        (sigmaRank leftFormula) (piRank leftFormula)
        (sigmaRank rightFormula) (piRank rightFormula))).
  - destruct (raw_operationShapeAnd_inv
      (rawQuotedFormulaCode M leftFormula)
      (rawQuotedFormulaCode M rightFormula) targetShape hshapeRow) as
      (leftIndex & outputLeft & leftDepth &
       rightIndex & outputRight & rightDepth &
       htargetShape & hleftIndex & hleftLookup &
       hrightIndex & hrightLookup).
    subst targetShape.
    cbn [RawCodedFormulaShapeRankEvidence] in hevidence.
    destruct hevidence as
      (leftSigma & leftPi & rightSigma & rightPi &
       hleftRank & hrightRank & hrankRelation).
    pose proof (raw_formulaOperationTrace_reroot M hPA
      atom parameter rootDepth sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound rootIndex
      (rawQuotedFormulaCode M (pAnd leftFormula rightFormula)) output
      htrace leftIndex (rawQuotedFormulaCode M leftFormula)
      outputLeft leftDepth hleftIndex hleftLookup) as hleftOperation.
    pose proof (raw_formulaOperationTrace_reroot M hPA
      atom parameter rootDepth sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound rootIndex
      (rawQuotedFormulaCode M (pAnd leftFormula rightFormula)) output
      htrace rightIndex (rawQuotedFormulaCode M rightFormula)
      outputRight rightDepth hrightIndex hrightLookup) as hrightOperation.
    destruct (IHleft atom parameter leftDepth outputLeft
      leftSigma leftPi hleftOperation hleftRank) as
      [hleftSigma hleftPi].
    destruct (IHright atom parameter rightDepth outputRight
      rightSigma rightPi hrightOperation hrightRank) as
      [hrightSigma hrightPi].
    rewrite hleftSigma, hleftPi, hrightSigma, hrightPi in hrankRelation.
    exact (raw_formulaRankAndOr_functional M hPA
      sigma pi
      (rawNumeralValue M
        (Nat.max (sigmaRank leftFormula) (sigmaRank rightFormula)))
      (rawNumeralValue M
        (Nat.max (piRank leftFormula) (piRank rightFormula)))
      (rawNumeralValue M (sigmaRank leftFormula))
      (rawNumeralValue M (piRank leftFormula))
      (rawNumeralValue M (sigmaRank rightFormula))
      (rawNumeralValue M (piRank rightFormula))
      hrankRelation
      (raw_formulaRankAndOr_numerals M hPA
        (sigmaRank leftFormula) (piRank leftFormula)
        (sigmaRank rightFormula) (piRank rightFormula))).
  - destruct (raw_operationShapeOr_inv
      (rawQuotedFormulaCode M leftFormula)
      (rawQuotedFormulaCode M rightFormula) targetShape hshapeRow) as
      (leftIndex & outputLeft & leftDepth &
       rightIndex & outputRight & rightDepth &
       htargetShape & hleftIndex & hleftLookup &
       hrightIndex & hrightLookup).
    subst targetShape.
    cbn [RawCodedFormulaShapeRankEvidence] in hevidence.
    destruct hevidence as
      (leftSigma & leftPi & rightSigma & rightPi &
       hleftRank & hrightRank & hrankRelation).
    pose proof (raw_formulaOperationTrace_reroot M hPA
      atom parameter rootDepth sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound rootIndex
      (rawQuotedFormulaCode M (pOr leftFormula rightFormula)) output
      htrace leftIndex (rawQuotedFormulaCode M leftFormula)
      outputLeft leftDepth hleftIndex hleftLookup) as hleftOperation.
    pose proof (raw_formulaOperationTrace_reroot M hPA
      atom parameter rootDepth sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound rootIndex
      (rawQuotedFormulaCode M (pOr leftFormula rightFormula)) output
      htrace rightIndex (rawQuotedFormulaCode M rightFormula)
      outputRight rightDepth hrightIndex hrightLookup) as hrightOperation.
    destruct (IHleft atom parameter leftDepth outputLeft
      leftSigma leftPi hleftOperation hleftRank) as
      [hleftSigma hleftPi].
    destruct (IHright atom parameter rightDepth outputRight
      rightSigma rightPi hrightOperation hrightRank) as
      [hrightSigma hrightPi].
    rewrite hleftSigma, hleftPi, hrightSigma, hrightPi in hrankRelation.
    exact (raw_formulaRankAndOr_functional M hPA
      sigma pi
      (rawNumeralValue M
        (Nat.max (sigmaRank leftFormula) (sigmaRank rightFormula)))
      (rawNumeralValue M
        (Nat.max (piRank leftFormula) (piRank rightFormula)))
      (rawNumeralValue M (sigmaRank leftFormula))
      (rawNumeralValue M (piRank leftFormula))
      (rawNumeralValue M (sigmaRank rightFormula))
      (rawNumeralValue M (piRank rightFormula))
      hrankRelation
      (raw_formulaRankAndOr_numerals M hPA
        (sigmaRank leftFormula) (piRank leftFormula)
        (sigmaRank rightFormula) (piRank rightFormula))).
  - destruct (raw_operationShapeAll_inv
      (rawQuotedFormulaCode M child) targetShape hshapeRow) as
      (childIndex & outputChild & childDepth &
       htargetShape & hchildIndex & hchildLookup).
    subst targetShape.
    cbn [RawCodedFormulaShapeRankEvidence] in hevidence.
    destruct hevidence as
      (childSigma & childPi & hchildRank & hrankRelation).
    pose proof (raw_formulaOperationTrace_reroot M hPA
      atom parameter rootDepth sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound rootIndex
      (rawQuotedFormulaCode M (pAll child)) output
      htrace childIndex (rawQuotedFormulaCode M child)
      outputChild childDepth hchildIndex hchildLookup) as hchildOperation.
    destruct (IHchild atom parameter childDepth outputChild
      childSigma childPi hchildOperation hchildRank) as
      [hchildSigma hchildPi].
    rewrite hchildSigma, hchildPi in hrankRelation.
    exact (raw_formulaRankAll_functional M hPA
      sigma pi
      (rawNumeralValue M (S (Nat.max 1 (piRank child))))
      (rawNumeralValue M (Nat.max 1 (piRank child)))
      (rawNumeralValue M (sigmaRank child))
      (rawNumeralValue M (piRank child))
      hrankRelation
      (raw_formulaRankAll_numerals M hPA
        (sigmaRank child) (piRank child))).
  - destruct (raw_operationShapeEx_inv
      (rawQuotedFormulaCode M child) targetShape hshapeRow) as
      (childIndex & outputChild & childDepth &
       htargetShape & hchildIndex & hchildLookup).
    subst targetShape.
    cbn [RawCodedFormulaShapeRankEvidence] in hevidence.
    destruct hevidence as
      (childSigma & childPi & hchildRank & hrankRelation).
    pose proof (raw_formulaOperationTrace_reroot M hPA
      atom parameter rootDepth sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound rootIndex
      (rawQuotedFormulaCode M (pEx child)) output
      htrace childIndex (rawQuotedFormulaCode M child)
      outputChild childDepth hchildIndex hchildLookup) as hchildOperation.
    destruct (IHchild atom parameter childDepth outputChild
      childSigma childPi hchildOperation hchildRank) as
      [hchildSigma hchildPi].
    rewrite hchildSigma, hchildPi in hrankRelation.
    exact (raw_formulaRankEx_functional M hPA
      sigma pi
      (rawNumeralValue M (Nat.max 1 (sigmaRank child)))
      (rawNumeralValue M (S (Nat.max 1 (sigmaRank child))))
      (rawNumeralValue M (sigmaRank child))
      (rawNumeralValue M (piRank child))
      hrankRelation
      (raw_formulaRankEx_numerals M hPA
        (sigmaRank child) (piRank child))).
Qed.

(** Operation target tables are also honest syntax traversals.  This is used
    after rank soundness to obtain an output-rank certificate by totality. *)
Lemma raw_formulaOperationTraversalRow_target_syntax : forall
    (M : RawPAModel) atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth,
  RawCodedFormulaOperationTraversalRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth ->
  RawCodedFormulaSyntaxTraversalRow M
    targetCode targetStep index output.
Proof.
  intros M atom parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth hrow.
  unfold RawCodedFormulaOperationTraversalRow in hrow.
  unfold RawCodedFormulaSyntaxTraversalRow.
  destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - left. destruct heq as
      (inputLeft & outputLeft & inputRight & outputRight &
       _ & houtput & _ & _).
    exists outputLeft, outputRight. exact houtput.
  - right; left. exact (proj2 hbot).
  - right; right; left.
    destruct himp as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       _ & houtput).
    exists leftIndex, outputLeft, rightIndex, outputRight.
    split; [exact hleftIndex |].
    split; [exact (proj1 (proj2 hleftLookup)) |].
    split; [exact hrightIndex |].
    split; [exact (proj1 (proj2 hrightLookup)) | exact houtput].
  - right; right; right; left.
    destruct hand as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       _ & houtput).
    exists leftIndex, outputLeft, rightIndex, outputRight.
    split; [exact hleftIndex |].
    split; [exact (proj1 (proj2 hleftLookup)) |].
    split; [exact hrightIndex |].
    split; [exact (proj1 (proj2 hrightLookup)) | exact houtput].
  - right; right; right; right; left.
    destruct hor as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       _ & houtput).
    exists leftIndex, outputLeft, rightIndex, outputRight.
    split; [exact hleftIndex |].
    split; [exact (proj1 (proj2 hleftLookup)) |].
    split; [exact hrightIndex |].
    split; [exact (proj1 (proj2 hrightLookup)) | exact houtput].
  - right; right; right; right; right; left.
    destruct hall as
      (childIndex & inputChild & outputChild & childDepth &
       hchildIndex & hchildLookup & _ & _ & houtput).
    exists childIndex, outputChild.
    split; [exact hchildIndex |].
    split; [exact (proj1 (proj2 hchildLookup)) | exact houtput].
  - right; right; right; right; right; right.
    destruct hex as
      (childIndex & inputChild & outputChild & childDepth &
       hchildIndex & hchildLookup & _ & _ & houtput).
    exists childIndex, outputChild.
    split; [exact hchildIndex |].
    split; [exact (proj1 (proj2 hchildLookup)) | exact houtput].
Qed.

Lemma raw_formulaOperationTrace_target_syntax : forall
    (M : RawPAModel) atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output,
  RawCodedFormulaOperationTrace M atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output ->
  RawCodedFormulaSyntaxTraversal M
    targetCode targetStep bound rootIndex output.
Proof.
  intros M atom parameter rootDepth sourceCode sourceStep targetCode
    targetStep depthCode depthStep bound rootIndex input output
    (hsourceDefined & htargetDefined & hdepthDefined & hrootBelow &
     hrootLookup & hrows).
  split; [exact htargetDefined |].
  split; [exact hrootBelow |].
  split; [exact (proj1 (proj2 hrootLookup)) |].
  intros index code hindexBelow htargetLookup.
  destruct (hsourceDefined index hindexBelow) as [source hsourceLookup].
  destruct (hdepthDefined index hindexBelow) as [depth hdepthLookup].
  apply (raw_formulaOperationTraversalRow_target_syntax M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index source code depth).
  apply hrows; [exact hindexBelow |].
  split; [exact hsourceLookup |]. split; assumption.
Qed.

Theorem raw_codedFormulaOperation_quoted_rank :
  PolynomialPairInjectivityProof ->
  forall (M : RawPAModel), RawPASatisfies M ->
  forall phi atom parameter rootDepth output,
  RawCodedFormulaOperation M atom parameter rootDepth
    (rawQuotedFormulaCode M phi) output ->
  RawCodedFormulaRank M output
    (rawNumeralValue M (sigmaRank phi))
    (rawNumeralValue M (piRank phi)).
Proof.
  intros hpairProof M hPA phi atom parameter rootDepth output hoperation.
  pose proof hoperation as hoperationSound.
  destruct hoperation as
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace).
  assert (hwellformed : RawCodedWellFormedFormula M output).
  {
    exists targetCode, targetStep, bound, rootIndex.
    exact (raw_formulaOperationTrace_target_syntax M atom parameter
      rootDepth sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound rootIndex
      (rawQuotedFormulaCode M phi) output htrace).
  }
  destruct (raw_codedWellFormedFormula_rank_exists M hPA output hwellformed)
    as (sigma & pi & hrank).
  destruct (raw_codedFormulaOperation_quoted_rank_sound
    hpairProof M hPA phi atom parameter rootDepth output sigma pi
    hoperationSound hrank) as [hsigma hpi].
  subst sigma. subst pi. exact hrank.
Qed.

Corollary raw_codedFormulaOperation_quoted_quantifier_bounded :
  PolynomialPairInjectivityProof ->
  forall (M : RawPAModel), RawPASatisfies M ->
  forall level phi atom parameter rootDepth output,
  quantifierGroups phi <= level ->
  RawCodedFormulaOperation M atom parameter rootDepth
    (rawQuotedFormulaCode M phi) output ->
  RawFormulaQuantifierBounded M level output.
Proof.
  intros hpairProof M hPA level phi atom parameter rootDepth output
    hbounded hoperation.
  pose proof (raw_codedFormulaOperation_quoted_rank
    hpairProof M hPA phi atom parameter rootDepth output hoperation) as hrank.
  unfold RawFormulaQuantifierBounded.
  unfold quantifierGroups in hbounded.
  destruct (Nat.le_ge_cases (sigmaRank phi) (piRank phi)) as
      [hsigmaPi | hpiSigma].
  - left. exists (rawNumeralValue M (sigmaRank phi)),
      (rawNumeralValue M (piRank phi)).
    split; [exact hrank |].
    apply rawLe_numerals_of_le; [exact hPA |].
    rewrite Nat.min_l in hbounded by exact hsigmaPi. exact hbounded.
  - right. exists (rawNumeralValue M (sigmaRank phi)),
      (rawNumeralValue M (piRank phi)).
    split; [exact hrank |].
    apply rawLe_numerals_of_le; [exact hPA |].
    rewrite Nat.min_r in hbounded by exact hpiSigma. exact hbounded.
Qed.

End PABoundedRawCodedFormulaOperationQuotedRankSound.
