(**
  Compositional constructors for diagonal formula-operation traces.

  [RawCodedFormulaDiagonalOperation] deliberately retains one shared formula
  table.  This is exactly what unary constructors need, but a binary
  constructor must first splice two possibly nonstandard tables.  The copy
  state below performs that splice by PA-definable induction over the second
  table's (possibly nonstandard) bound.  No formula code is decoded in the
  metatheory.

  The generic results are then specialized to capture-avoiding substitution.
  In particular, the final all-depth constructors are the syntax lemmas used
  to assemble the closed dynamic-soundness induction body.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity
  RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedAssignmentTotality
  RawCodedProofDescent
  RawCodedFormulaRankStep RawCodedFormulaRankTraversal
  RawCodedFormulaRankTotality
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthReindexing
  RawCodedPAAxiomContextSelfShift
  RawCodedFormulaDiagonalOperation
  RawCodedUniversalClosureDiagonalSubstitution.

Module PABoundedRawCodedFormulaDiagonalOperationComposition.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthReindexing.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedFormulaDiagonalOperation.
Import PABoundedRawCodedUniversalClosureDiagonalSubstitution.

(** ------------------------------------------------------------------
    Offset transport.

    The target table starts with an existing prefix of length [offset].  A
    source row at [index] is therefore copied to [offset + index].  The
    underlying pair-table embedding already transports the formula and depth
    lookups; the only work here is rebuilding the seven formula-row cases.
*)

Definition RawDiagonalFormulaOperationOffsetEmbedding (M : RawPAModel)
    (offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep : M)
    : Prop :=
  RawTermShiftPairOffsetEmbedding M offset current
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep.

Arguments RawDiagonalFormulaOperationOffsetEmbedding M offset current
  sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
  targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
  : clear implicits.

Definition diagonalFormulaOperationOffsetEmbeddingTermAt
    (offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
      : term) : formula :=
  termShiftPairOffsetEmbeddingTermAt offset current
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep.

Lemma raw_sat_diagonalFormulaOperationOffsetEmbeddingTermAt_iff : forall
    (M : RawPAModel) e offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep,
  raw_formula_sat M e
    (diagonalFormulaOperationOffsetEmbeddingTermAt offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep)
  <->
  RawDiagonalFormulaOperationOffsetEmbedding M
    (raw_term_eval M e offset) (raw_term_eval M e current)
    (raw_term_eval M e sourceFormulaCode)
    (raw_term_eval M e sourceFormulaStep)
    (raw_term_eval M e sourceDepthCode)
    (raw_term_eval M e sourceDepthStep)
    (raw_term_eval M e targetFormulaCode)
    (raw_term_eval M e targetFormulaStep)
    (raw_term_eval M e targetDepthCode)
    (raw_term_eval M e targetDepthStep).
Proof.
  intros. apply raw_sat_termShiftPairOffsetEmbeddingTermAt_iff.
Qed.

Lemma raw_diagonalFormulaOperationTriple_offset : forall
    (M : RawPAModel) offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
      index input output depth,
  RawDiagonalFormulaOperationOffsetEmbedding M offset current
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep ->
  rawLt M index current ->
  RawCodedFormulaOperationTripleLookup M
    sourceFormulaCode sourceFormulaStep
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    index input output depth ->
  RawCodedFormulaOperationTripleLookup M
    targetFormulaCode targetFormulaStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
    (raw_add M offset index) input output depth.
Proof.
  intros M offset current
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
    index input output depth hembed hindex
    [hinput [houtput hdepth]].
  pose proof (hembed index input depth hindex (conj hinput hdepth))
    as [hnewInput hnewDepth].
  pose proof (hembed index output depth hindex (conj houtput hdepth))
    as [hnewOutput _].
  repeat split; assumption.
Qed.

Lemma raw_diagonalFormulaOperationTraversalRow_offset : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
      input depth,
  RawDiagonalFormulaOperationOffsetEmbedding M offset current
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep ->
  RawDiagonalFormulaOperationTraversalRow M atom parameter
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    current input depth ->
  RawDiagonalFormulaOperationTraversalRow M atom parameter
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
    (raw_add M offset current) input depth.
Proof.
  intros M hPA atom parameter offset current
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
    input depth hembed hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - left. exact heq.
  - right. left. exact hbot.
  - right. right. left.
    destruct himp as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleft & hleftLookup & hleftDepth & hright & hrightLookup &
       hrightDepth & hinput & houtput).
    exists (raw_add M offset leftIndex), inputLeft, outputLeft, leftDepth,
      (raw_add M offset rightIndex), inputRight, outputRight, rightDepth.
    split.
    + exact (raw_lt_add_left_fixedTruth M hPA offset
        leftIndex current hleft).
    + split.
      * exact (raw_diagonalFormulaOperationTriple_offset M offset current
          sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
          targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
          leftIndex inputLeft outputLeft leftDepth hembed hleft hleftLookup).
      * split; [exact hleftDepth |]. split.
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             rightIndex current hright).
        -- split.
           ++ exact (raw_diagonalFormulaOperationTriple_offset M
                offset current sourceFormulaCode sourceFormulaStep
                sourceDepthCode sourceDepthStep targetFormulaCode
                targetFormulaStep targetDepthCode targetDepthStep
                rightIndex inputRight outputRight rightDepth
                hembed hright hrightLookup).
           ++ repeat split; assumption.
  - right. right. right. left.
    destruct hand as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleft & hleftLookup & hleftDepth & hright & hrightLookup &
       hrightDepth & hinput & houtput).
    exists (raw_add M offset leftIndex), inputLeft, outputLeft, leftDepth,
      (raw_add M offset rightIndex), inputRight, outputRight, rightDepth.
    split.
    + exact (raw_lt_add_left_fixedTruth M hPA offset
        leftIndex current hleft).
    + split.
      * exact (raw_diagonalFormulaOperationTriple_offset M offset current
          sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
          targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
          leftIndex inputLeft outputLeft leftDepth hembed hleft hleftLookup).
      * split; [exact hleftDepth |]. split.
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             rightIndex current hright).
        -- split.
           ++ exact (raw_diagonalFormulaOperationTriple_offset M
                offset current sourceFormulaCode sourceFormulaStep
                sourceDepthCode sourceDepthStep targetFormulaCode
                targetFormulaStep targetDepthCode targetDepthStep
                rightIndex inputRight outputRight rightDepth
                hembed hright hrightLookup).
           ++ repeat split; assumption.
  - right. right. right. right. left.
    destruct hor as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleft & hleftLookup & hleftDepth & hright & hrightLookup &
       hrightDepth & hinput & houtput).
    exists (raw_add M offset leftIndex), inputLeft, outputLeft, leftDepth,
      (raw_add M offset rightIndex), inputRight, outputRight, rightDepth.
    split.
    + exact (raw_lt_add_left_fixedTruth M hPA offset
        leftIndex current hleft).
    + split.
      * exact (raw_diagonalFormulaOperationTriple_offset M offset current
          sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
          targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
          leftIndex inputLeft outputLeft leftDepth hembed hleft hleftLookup).
      * split; [exact hleftDepth |]. split.
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             rightIndex current hright).
        -- split.
           ++ exact (raw_diagonalFormulaOperationTriple_offset M
                offset current sourceFormulaCode sourceFormulaStep
                sourceDepthCode sourceDepthStep targetFormulaCode
                targetFormulaStep targetDepthCode targetDepthStep
                rightIndex inputRight outputRight rightDepth
                hembed hright hrightLookup).
           ++ repeat split; assumption.
  - right. right. right. right. right. left.
    destruct hall as
      (childIndex & inputChild & outputChild & childDepth &
       hchild & hchildLookup & hchildDepth & hinput & houtput).
    exists (raw_add M offset childIndex), inputChild, outputChild, childDepth.
    split.
    + exact (raw_lt_add_left_fixedTruth M hPA offset
        childIndex current hchild).
    + split.
      * exact (raw_diagonalFormulaOperationTriple_offset M offset current
          sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
          targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
          childIndex inputChild outputChild childDepth
          hembed hchild hchildLookup).
      * repeat split; assumption.
  - right. right. right. right. right. right.
    destruct hex as
      (childIndex & inputChild & outputChild & childDepth &
       hchild & hchildLookup & hchildDepth & hinput & houtput).
    exists (raw_add M offset childIndex), inputChild, outputChild, childDepth.
    split.
    + exact (raw_lt_add_left_fixedTruth M hPA offset
        childIndex current hchild).
    + split.
      * exact (raw_diagonalFormulaOperationTriple_offset M offset current
          sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
          targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
          childIndex inputChild outputChild childDepth
          hembed hchild hchildLookup).
      * repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    A represented copy state.

    The implication guard is important: definable induction ranges over all
    carrier elements, whereas a source trace has rows only below its bound.
    At the terminal state [current = sourceBound], the target bundle is the
    concatenation of the initial prefix and the complete source bundle.
*)

Definition RawDiagonalFormulaOperationCopyState (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound offset initialRootIndex initialInput initialDepth current : M)
    : Prop :=
  rawLe M current sourceBound ->
  exists targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep,
    RawDiagonalFormulaOperationBundle M atom parameter
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
      (raw_add M offset current) /\
    RawDiagonalFormulaOperationLookup M
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
      initialRootIndex initialInput initialDepth /\
    RawDiagonalFormulaOperationOffsetEmbedding M offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep.

Arguments RawDiagonalFormulaOperationCopyState M atom parameter
  sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
  sourceBound offset initialRootIndex initialInput initialDepth current
  : clear implicits.

Definition diagonalFormulaOperationCopyStateTermAt
    (atom : term -> term -> term -> term -> formula)
    (parameter
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound offset initialRootIndex initialInput initialDepth current
      : term) : formula :=
  pImp
    (Formula.leTermAt current sourceBound)
    (operationEx4
      (operationAnd3
        (diagonalFormulaOperationBundleTermAt atom
          (liftTerm 4 parameter)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)
          (tAdd (liftTerm 4 offset) (liftTerm 4 current)))
        (diagonalFormulaOperationLookupTermAt
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)
          (liftTerm 4 initialRootIndex)
          (liftTerm 4 initialInput) (liftTerm 4 initialDepth))
        (diagonalFormulaOperationOffsetEmbeddingTermAt
          (liftTerm 4 offset) (liftTerm 4 current)
          (liftTerm 4 sourceFormulaCode) (liftTerm 4 sourceFormulaStep)
          (liftTerm 4 sourceDepthCode) (liftTerm 4 sourceDepthStep)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)))).

Lemma raw_sat_diagonalFormulaOperationCopyStateTermAt_iff : forall
    (M : RawPAModel) e
    (atom : term -> term -> term -> term -> formula)
    (rawAtom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atom parameter depth input output) <->
    rawAtom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound offset initialRootIndex initialInput initialDepth current,
  raw_formula_sat M e
    (diagonalFormulaOperationCopyStateTermAt atom parameter
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound offset initialRootIndex initialInput initialDepth current)
  <->
  RawDiagonalFormulaOperationCopyState M rawAtom
    (raw_term_eval M e parameter)
    (raw_term_eval M e sourceFormulaCode)
    (raw_term_eval M e sourceFormulaStep)
    (raw_term_eval M e sourceDepthCode)
    (raw_term_eval M e sourceDepthStep)
    (raw_term_eval M e sourceBound) (raw_term_eval M e offset)
    (raw_term_eval M e initialRootIndex)
    (raw_term_eval M e initialInput) (raw_term_eval M e initialDepth)
    (raw_term_eval M e current).
Proof.
  intros M e atom rawAtom hatom.
  intros. unfold diagonalFormulaOperationCopyStateTermAt, operationEx4,
    operationAnd3, RawDiagonalFormulaOperationCopyState.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank.
  setoid_rewrite (raw_sat_diagonalFormulaOperationBundleTermAt_iff
    M _ atom rawAtom hatom).
  setoid_rewrite raw_sat_diagonalFormulaOperationLookupTermAt_iff.
  setoid_rewrite
    raw_sat_diagonalFormulaOperationOffsetEmbeddingTermAt_iff.
  cbn [raw_term_eval scons].
  split; intros h hle;
    destruct (h hle) as
      (targetFormulaCode & targetFormulaStep & targetDepthCode &
       targetDepthStep & hresult);
    exists targetFormulaCode, targetFormulaStep,
      targetDepthCode, targetDepthStep.
  - repeat rewrite (raw_rankTraversal_eval_liftTerm_four M
      targetDepthStep targetDepthCode targetFormulaStep targetFormulaCode e)
      in hresult.
    exact hresult.
  - repeat rewrite (raw_rankTraversal_eval_liftTerm_four M
      targetDepthStep targetDepthCode targetFormulaStep targetFormulaCode e).
    exact hresult.
Qed.

Lemma raw_diagonalFormulaOperationOffsetEmbedding_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall offset
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep,
  RawDiagonalFormulaOperationOffsetEmbedding M offset (raw_zero M)
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep.
Proof.
  intros M hPA offset
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep.
  exact (raw_termShiftPairOffsetEmbedding_zero M hPA offset
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep).
Qed.

Lemma raw_diagonalFormulaOperationCopyState_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound offset
      initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
      initialRootIndex initialInput initialDepth,
  RawDiagonalFormulaOperationBundle M atom parameter
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
    offset ->
  RawDiagonalFormulaOperationLookup M
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
    initialRootIndex initialInput initialDepth ->
  RawDiagonalFormulaOperationCopyState M atom parameter
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound offset initialRootIndex initialInput initialDepth
    (raw_zero M).
Proof.
  intros M hPA atom parameter
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound offset
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
    initialRootIndex initialInput initialDepth
    hinitialBundle hinitialRoot _.
  exists initialFormulaCode, initialFormulaStep,
    initialDepthCode, initialDepthStep.
  rewrite raw_assignmentTotality_add_zero_right by exact hPA.
  split; [exact hinitialBundle |]. split; [exact hinitialRoot |].
  exact (raw_diagonalFormulaOperationOffsetEmbedding_zero M hPA offset
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep).
Qed.

Lemma raw_diagonalFormulaOperationCopyState_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound sourceRootIndex sourceInput sourceRootDepth
      offset initialRootIndex initialInput initialDepth current,
  RawDiagonalFormulaOperationTrace M atom parameter sourceRootDepth
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound sourceRootIndex sourceInput ->
  rawLt M initialRootIndex offset ->
  RawDiagonalFormulaOperationCopyState M atom parameter
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound offset initialRootIndex initialInput initialDepth current ->
  RawDiagonalFormulaOperationCopyState M atom parameter
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound offset initialRootIndex initialInput initialDepth
    (raw_succ M current).
Proof.
  intros M hPA atom parameter
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound sourceRootIndex sourceInput sourceRootDepth
    offset initialRootIndex initialInput initialDepth current
    hsource hinitialBelow hcurrent hsuccLe.
  destruct hsource as
    [[hsourceFormulaDefined [hsourceDepthDefined hsourceRows]]
      [hsourceBelow hsourceRoot]].
  assert (hcurrentBelow : rawLt M current sourceBound).
  { exact (raw_rank_lt_of_succ_le M hPA current sourceBound hsuccLe). }
  assert (hcurrentLe : rawLe M current sourceBound).
  { exact (raw_lt_to_le M current sourceBound hcurrentBelow). }
  destruct (hcurrent hcurrentLe) as
    (targetFormulaCode & targetFormulaStep & targetDepthCode &
     targetDepthStep & htargetBundle & hinitialRoot & hembed).
  destruct (hsourceFormulaDefined current hcurrentBelow)
    as [rowInput hrowInput].
  destruct (hsourceDepthDefined current hcurrentBelow)
    as [rowDepth hrowDepth].
  assert (hsourceLookup : RawDiagonalFormulaOperationLookup M
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      current rowInput rowDepth).
  { split; assumption. }
  pose proof (hsourceRows current rowInput rowDepth
    hcurrentBelow hsourceLookup) as hsourceRow.
  pose proof (raw_diagonalFormulaOperationTraversalRow_offset M hPA
    atom parameter offset current
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
    rowInput rowDepth hembed hsourceRow) as htargetRow.
  destruct (raw_diagonalFormulaOperationBundle_append M hPA atom parameter
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
    (raw_add M offset current) rowInput rowDepth
    htargetBundle htargetRow)
    as (newFormulaCode & newFormulaStep & newDepthCode & newDepthStep &
        hnewBundle & hprefix & hnewRoot).
  exists newFormulaCode, newFormulaStep, newDepthCode, newDepthStep.
  split.
  - rewrite raw_add_succ by exact hPA. exact hnewBundle.
  - split.
    + apply (raw_diagonalFormulaOperationLookup_prefix_extend M
        (raw_add M offset current)
        targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        initialRootIndex initialInput initialDepth hprefix).
      * exact (raw_lt_le_trans_pair M hPA
          initialRootIndex offset (raw_add M offset current)
          hinitialBelow (raw_proof_left_le_sum M offset current)).
      * exact hinitialRoot.
    + intros index input depth hindex hlookup.
      destruct (raw_lt_succ_cases M hPA index current hindex)
        as [hindexOld | ->].
      * apply (raw_diagonalFormulaOperationLookup_prefix_extend M
          (raw_add M offset current)
          targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
          newFormulaCode newFormulaStep newDepthCode newDepthStep
          (raw_add M offset index) input depth hprefix).
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             index current hindexOld).
        -- exact (hembed index input depth hindexOld hlookup).
      * destruct hlookup as [hlookupInput hlookupDepth].
        assert (hinputEq : input = rowInput).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            sourceFormulaCode sourceFormulaStep current input rowInput
            hlookupInput hrowInput).
        }
        assert (hdepthEq : depth = rowDepth).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            sourceDepthCode sourceDepthStep current depth rowDepth
            hlookupDepth hrowDepth).
        }
        subst input. subst depth. exact hnewRoot.
Qed.

Theorem raw_diagonalFormulaOperationCopyState_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atomFormula : term -> term -> term -> term -> formula)
      (atom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atomFormula parameter depth input output) <->
    atom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound sourceRootIndex sourceInput sourceRootDepth
      offset
      initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
      initialRootIndex initialInput initialDepth,
  RawDiagonalFormulaOperationTrace M atom parameter sourceRootDepth
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound sourceRootIndex sourceInput ->
  RawDiagonalFormulaOperationBundle M atom parameter
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
    offset ->
  rawLt M initialRootIndex offset ->
  RawDiagonalFormulaOperationLookup M
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
    initialRootIndex initialInput initialDepth ->
  forall current,
  RawDiagonalFormulaOperationCopyState M atom parameter
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound offset initialRootIndex initialInput initialDepth current.
Proof.
  intros M hPA atomFormula atom hatom parameter
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound sourceRootIndex sourceInput sourceRootDepth
    offset
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
    initialRootIndex initialInput initialDepth
    hsource hinitialBundle hinitialBelow hinitialRoot.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => parameter
    | 1 => sourceFormulaCode
    | 2 => sourceFormulaStep
    | 3 => sourceDepthCode
    | 4 => sourceDepthStep
    | 5 => sourceBound
    | 6 => offset
    | 7 => initialRootIndex
    | 8 => initialInput
    | _ => initialDepth
    end).
  set (phi := diagonalFormulaOperationCopyStateTermAt atomFormula
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
    (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_diagonalFormulaOperationCopyStateTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          atomFormula atom hatom
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_diagonalFormulaOperationCopyState_zero M hPA
        atom parameter
        sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
        sourceBound offset
        initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
        initialRootIndex initialInput initialDepth
        hinitialBundle hinitialRoot).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_diagonalFormulaOperationCopyStateTermAt_iff M
          (scons M current parameterEnv)
          atomFormula atom hatom
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_diagonalFormulaOperationCopyStateTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          atomFormula atom hatom
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_diagonalFormulaOperationCopyState_succ M hPA
        atom parameter
        sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
        sourceBound sourceRootIndex sourceInput sourceRootDepth
        offset initialRootIndex initialInput initialDepth current
        hsource hinitialBelow hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_diagonalFormulaOperationCopyStateTermAt_iff M
      (scons M current parameterEnv)
      atomFormula atom hatom
      (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
      (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 0))
    (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

Theorem raw_diagonalFormulaOperationTraces_concatenate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atomFormula : term -> term -> term -> term -> formula)
      (atom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atomFormula parameter depth input output) <->
    atom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter rootDepth
      firstFormulaCode firstFormulaStep firstDepthCode firstDepthStep
      firstBound firstRootIndex firstInput
      secondFormulaCode secondFormulaStep secondDepthCode secondDepthStep
      secondBound secondRootIndex secondInput,
  RawDiagonalFormulaOperationTrace M atom parameter rootDepth
    firstFormulaCode firstFormulaStep firstDepthCode firstDepthStep
    firstBound firstRootIndex firstInput ->
  RawDiagonalFormulaOperationTrace M atom parameter rootDepth
    secondFormulaCode secondFormulaStep secondDepthCode secondDepthStep
    secondBound secondRootIndex secondInput ->
  exists newFormulaCode newFormulaStep newDepthCode newDepthStep : M,
    RawDiagonalFormulaOperationTrace M atom parameter rootDepth
      newFormulaCode newFormulaStep newDepthCode newDepthStep
      (raw_add M firstBound secondBound)
      (raw_add M firstBound secondRootIndex) secondInput /\
    RawDiagonalFormulaOperationLookup M
      newFormulaCode newFormulaStep newDepthCode newDepthStep
      firstRootIndex firstInput rootDepth.
Proof.
  intros M hPA atomFormula atom hatom parameter rootDepth
    firstFormulaCode firstFormulaStep firstDepthCode firstDepthStep
    firstBound firstRootIndex firstInput
    secondFormulaCode secondFormulaStep secondDepthCode secondDepthStep
    secondBound secondRootIndex secondInput hfirst hsecond.
  destruct hfirst as [hfirstBundle [hfirstBelow hfirstRoot]].
  pose proof (raw_diagonalFormulaOperationCopyState_all M hPA
    atomFormula atom hatom parameter
    secondFormulaCode secondFormulaStep secondDepthCode secondDepthStep
    secondBound secondRootIndex secondInput rootDepth
    firstBound
    firstFormulaCode firstFormulaStep firstDepthCode firstDepthStep
    firstRootIndex firstInput rootDepth
    hsecond hfirstBundle hfirstBelow hfirstRoot secondBound) as hguard.
  destruct (hguard (raw_rank_le_refl M hPA secondBound)) as
    (newFormulaCode & newFormulaStep & newDepthCode & newDepthStep &
     hnewBundle & hfirstRetained & hembed).
  destruct hsecond as [hsecondBundle [hsecondBelow hsecondRoot]].
  exists newFormulaCode, newFormulaStep, newDepthCode, newDepthStep.
  split.
  - split; [exact hnewBundle |]. split.
    + exact (raw_lt_add_left_fixedTruth M hPA firstBound
        secondRootIndex secondBound hsecondBelow).
    + exact (hembed secondRootIndex secondInput rootDepth
        hsecondBelow hsecondRoot).
  - exact hfirstRetained.
Qed.

(** ------------------------------------------------------------------
    Constructor certificates.

    Atomic and falsity traces start from two empty beta tables.  Binary
    traces concatenate their children before appending the parent row.
    Unary traces use the prefix-preserving append already provided by
    [RawCodedFormulaDiagonalOperation].
*)

Lemma raw_diagonalFormulaOperationBundle_empty : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter,
  RawDiagonalFormulaOperationBundle M atom parameter
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M).
Proof.
  intros M hPA atom parameter.
  split.
  - exact (raw_codedZeroAssignment_defined_all M hPA (raw_zero M)).
  - split.
    + exact (raw_codedZeroAssignment_defined_all M hPA (raw_zero M)).
    + intros index input depth hindex _.
      exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Lemma raw_diagonalFormulaOperationLookup_to_triple : forall
    (M : RawPAModel) formulaCode formulaStep depthCode depthStep
      index input depth,
  RawDiagonalFormulaOperationLookup M
    formulaCode formulaStep depthCode depthStep index input depth ->
  RawCodedFormulaOperationTripleLookup M
    formulaCode formulaStep formulaCode formulaStep depthCode depthStep
    index input input depth.
Proof.
  intros M formulaCode formulaStep depthCode depthStep
    index input depth [hinput hdepth].
  split; [exact hinput |]. split; assumption.
Qed.

Lemma raw_codedFormulaDiagonalOperation_eq : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter depth left right,
  atom parameter depth left left ->
  atom parameter depth right right ->
  RawCodedFormulaDiagonalOperation M atom parameter depth
    (rawFormulaEqCode M left right).
Proof.
  intros M hPA atom parameter depth left right hleft hright.
  assert (hrow : RawDiagonalFormulaOperationTraversalRow M atom parameter
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (rawFormulaEqCode M left right) depth).
  {
    left. exists left, left, right, right.
    repeat split; try reflexivity; assumption.
  }
  destruct (raw_diagonalFormulaOperationBundle_append M hPA atom parameter
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (rawFormulaEqCode M left right) depth
    (raw_diagonalFormulaOperationBundle_empty M hPA atom parameter) hrow)
    as (formulaCode & formulaStep & depthCode & depthStep &
        hbundle & _ & hroot).
  exists formulaCode, formulaStep, depthCode, depthStep,
    (raw_succ M (raw_zero M)), (raw_zero M).
  split; [exact hbundle |]. split.
  - exact (raw_assignment_lt_self_succ M hPA (raw_zero M)).
  - exact hroot.
Qed.

Lemma raw_codedFormulaDiagonalOperation_bot : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter depth,
  RawCodedFormulaDiagonalOperation M atom parameter depth
    (rawFormulaBotCode M).
Proof.
  intros M hPA atom parameter depth.
  assert (hrow : RawDiagonalFormulaOperationTraversalRow M atom parameter
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (rawFormulaBotCode M) depth).
  { right. left. split; reflexivity. }
  destruct (raw_diagonalFormulaOperationBundle_append M hPA atom parameter
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (rawFormulaBotCode M) depth
    (raw_diagonalFormulaOperationBundle_empty M hPA atom parameter) hrow)
    as (formulaCode & formulaStep & depthCode & depthStep &
        hbundle & _ & hroot).
  exists formulaCode, formulaStep, depthCode, depthStep,
    (raw_succ M (raw_zero M)), (raw_zero M).
  split; [exact hbundle |]. split.
  - exact (raw_assignment_lt_self_succ M hPA (raw_zero M)).
  - exact hroot.
Qed.

Lemma raw_codedFormulaDiagonalOperation_binary : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atomFormula : term -> term -> term -> term -> formula)
      (atom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atomFormula parameter depth input output) <->
    atom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter depth (constructor : M -> M -> M),
  (forall formulaCode formulaStep depthCode depthStep
      index input rowDepth,
    RawCodedFormulaBinaryOperationRow M constructor
      formulaCode formulaStep formulaCode formulaStep depthCode depthStep
      index input input rowDepth ->
    RawDiagonalFormulaOperationTraversalRow M atom parameter
      formulaCode formulaStep depthCode depthStep
      index input rowDepth) ->
  forall left right,
  RawCodedFormulaDiagonalOperation M atom parameter depth left ->
  RawCodedFormulaDiagonalOperation M atom parameter depth right ->
  RawCodedFormulaDiagonalOperation M atom parameter depth
    (constructor left right).
Proof.
  intros M hPA atomFormula atom hatom parameter depth constructor
    hinject left right
    (leftFormulaCode & leftFormulaStep & leftDepthCode & leftDepthStep &
     leftBound & leftRootIndex & hleft)
    (rightFormulaCode & rightFormulaStep & rightDepthCode & rightDepthStep &
     rightBound & rightRootIndex & hright).
  destruct (raw_diagonalFormulaOperationTraces_concatenate M hPA
    atomFormula atom hatom parameter depth
    leftFormulaCode leftFormulaStep leftDepthCode leftDepthStep
    leftBound leftRootIndex left
    rightFormulaCode rightFormulaStep rightDepthCode rightDepthStep
    rightBound rightRootIndex right hleft hright)
    as (formulaCode & formulaStep & depthCode & depthStep &
        hcombined & hleftRoot).
  destruct hcombined as [hbundle [hrightBelow hrightRoot]].
  set (combinedBound := raw_add M leftBound rightBound).
  assert (hleftBelow : rawLt M leftRootIndex combinedBound).
  {
    unfold combinedBound.
    exact (raw_lt_le_trans_pair M hPA leftRootIndex leftBound
      (raw_add M leftBound rightBound)
      (proj1 (proj2 hleft)) (raw_proof_left_le_sum M leftBound rightBound)).
  }
  assert (hbinary : RawCodedFormulaBinaryOperationRow M constructor
      formulaCode formulaStep formulaCode formulaStep depthCode depthStep
      combinedBound (constructor left right) (constructor left right) depth).
  {
    exists leftRootIndex, left, left, depth,
      (raw_add M leftBound rightRootIndex), right, right, depth.
    split; [exact hleftBelow |]. split.
    - exact (raw_diagonalFormulaOperationLookup_to_triple M
        formulaCode formulaStep depthCode depthStep
        leftRootIndex left depth hleftRoot).
    - split; [reflexivity |]. split; [exact hrightBelow |]. split.
      + exact (raw_diagonalFormulaOperationLookup_to_triple M
          formulaCode formulaStep depthCode depthStep
          (raw_add M leftBound rightRootIndex) right depth hrightRoot).
      + repeat split; reflexivity.
  }
  pose proof (hinject formulaCode formulaStep depthCode depthStep
    combinedBound (constructor left right) depth hbinary) as hrow.
  destruct (raw_diagonalFormulaOperationBundle_append M hPA atom parameter
    formulaCode formulaStep depthCode depthStep combinedBound
    (constructor left right) depth hbundle hrow)
    as (newFormulaCode & newFormulaStep & newDepthCode & newDepthStep &
        hnewBundle & _ & hnewRoot).
  exists newFormulaCode, newFormulaStep, newDepthCode, newDepthStep,
    (raw_succ M combinedBound), combinedBound.
  split; [exact hnewBundle |]. split.
  - exact (raw_assignment_lt_self_succ M hPA combinedBound).
  - exact hnewRoot.
Qed.

Lemma raw_codedFormulaDiagonalOperation_imp : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atomFormula : term -> term -> term -> term -> formula)
      (atom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atomFormula parameter depth input output) <->
    atom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter depth left right,
  RawCodedFormulaDiagonalOperation M atom parameter depth left ->
  RawCodedFormulaDiagonalOperation M atom parameter depth right ->
  RawCodedFormulaDiagonalOperation M atom parameter depth
    (rawFormulaImpCode M left right).
Proof.
  intros M hPA atomFormula atom hatom parameter depth left right
    hleft hright.
  apply (raw_codedFormulaDiagonalOperation_binary M hPA
    atomFormula atom hatom parameter depth (rawFormulaImpCode M)).
  - intros. right. right. left. exact H.
  - exact hleft.
  - exact hright.
Qed.

Lemma raw_codedFormulaDiagonalOperation_and : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atomFormula : term -> term -> term -> term -> formula)
      (atom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atomFormula parameter depth input output) <->
    atom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter depth left right,
  RawCodedFormulaDiagonalOperation M atom parameter depth left ->
  RawCodedFormulaDiagonalOperation M atom parameter depth right ->
  RawCodedFormulaDiagonalOperation M atom parameter depth
    (rawFormulaAndCode M left right).
Proof.
  intros M hPA atomFormula atom hatom parameter depth left right
    hleft hright.
  apply (raw_codedFormulaDiagonalOperation_binary M hPA
    atomFormula atom hatom parameter depth (rawFormulaAndCode M)).
  - intros. right. right. right. left. exact H.
  - exact hleft.
  - exact hright.
Qed.

Lemma raw_codedFormulaDiagonalOperation_or : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atomFormula : term -> term -> term -> term -> formula)
      (atom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atomFormula parameter depth input output) <->
    atom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter depth left right,
  RawCodedFormulaDiagonalOperation M atom parameter depth left ->
  RawCodedFormulaDiagonalOperation M atom parameter depth right ->
  RawCodedFormulaDiagonalOperation M atom parameter depth
    (rawFormulaOrCode M left right).
Proof.
  intros M hPA atomFormula atom hatom parameter depth left right
    hleft hright.
  apply (raw_codedFormulaDiagonalOperation_binary M hPA
    atomFormula atom hatom parameter depth (rawFormulaOrCode M)).
  - intros. right. right. right. right. left. exact H.
  - exact hleft.
  - exact hright.
Qed.

Corollary raw_codedFormulaDiagonalOperation_ex : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter depth child,
  RawCodedFormulaDiagonalOperation M atom parameter
    (raw_succ M depth) child ->
  RawCodedFormulaDiagonalOperation M atom parameter depth
    (rawFormulaExCode M child).
Proof.
  intros M hPA atom parameter depth child hchild.
  apply (raw_codedFormulaDiagonalOperation_unary M hPA atom parameter depth
    (rawFormulaExCode M)).
  - intros. right. right. right. right. right. right. exact H.
  - exact hchild.
Qed.

(** Capture-avoiding substitution instances. *)

Lemma raw_codedFormulaDiagonalSubstitution_eq : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement depth left right,
  RawCodedFormulaSubstitutionAtom M replacement depth left left ->
  RawCodedFormulaSubstitutionAtom M replacement depth right right ->
  RawCodedFormulaDiagonalSubstitution M replacement depth
    (rawFormulaEqCode M left right).
Proof.
  exact (fun M hPA replacement depth left right =>
    raw_codedFormulaDiagonalOperation_eq M hPA
      (RawCodedFormulaSubstitutionAtom M) replacement depth left right).
Qed.

Lemma raw_codedFormulaDiagonalSubstitution_bot : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement depth,
  RawCodedFormulaDiagonalSubstitution M replacement depth
    (rawFormulaBotCode M).
Proof.
  exact (fun M hPA replacement depth =>
    raw_codedFormulaDiagonalOperation_bot M hPA
      (RawCodedFormulaSubstitutionAtom M) replacement depth).
Qed.

Lemma raw_codedFormulaDiagonalSubstitution_imp : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement depth left right,
  RawCodedFormulaDiagonalSubstitution M replacement depth left ->
  RawCodedFormulaDiagonalSubstitution M replacement depth right ->
  RawCodedFormulaDiagonalSubstitution M replacement depth
    (rawFormulaImpCode M left right).
Proof.
  intros M hPA replacement depth left right hleft hright.
  exact (raw_codedFormulaDiagonalOperation_imp M hPA
    codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)
    replacement depth left right hleft hright).
Qed.

Lemma raw_codedFormulaDiagonalSubstitution_and : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement depth left right,
  RawCodedFormulaDiagonalSubstitution M replacement depth left ->
  RawCodedFormulaDiagonalSubstitution M replacement depth right ->
  RawCodedFormulaDiagonalSubstitution M replacement depth
    (rawFormulaAndCode M left right).
Proof.
  intros M hPA replacement depth left right hleft hright.
  exact (raw_codedFormulaDiagonalOperation_and M hPA
    codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)
    replacement depth left right hleft hright).
Qed.

Lemma raw_codedFormulaDiagonalSubstitution_or : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement depth left right,
  RawCodedFormulaDiagonalSubstitution M replacement depth left ->
  RawCodedFormulaDiagonalSubstitution M replacement depth right ->
  RawCodedFormulaDiagonalSubstitution M replacement depth
    (rawFormulaOrCode M left right).
Proof.
  intros M hPA replacement depth left right hleft hright.
  exact (raw_codedFormulaDiagonalOperation_or M hPA
    codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)
    replacement depth left right hleft hright).
Qed.

Lemma raw_codedFormulaDiagonalSubstitution_ex : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement depth child,
  RawCodedFormulaDiagonalSubstitution M replacement
    (raw_succ M depth) child ->
  RawCodedFormulaDiagonalSubstitution M replacement depth
    (rawFormulaExCode M child).
Proof.
  exact (fun M hPA replacement depth child =>
    raw_codedFormulaDiagonalOperation_ex M hPA
      (RawCodedFormulaSubstitutionAtom M) replacement depth child).
Qed.

(** All-depth forms compose without any standardness assumption on [depth]. *)

Lemma raw_codedFormulaDiagonalSubstitutionAtAllDepths_bot : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement,
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawFormulaBotCode M).
Proof.
  intros M hPA replacement depth.
  exact (raw_codedFormulaDiagonalSubstitution_bot M hPA
    replacement depth).
Qed.

Lemma raw_codedFormulaDiagonalSubstitutionAtAllDepths_eq : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement left right,
  (forall depth,
    RawCodedFormulaSubstitutionAtom M replacement depth left left) ->
  (forall depth,
    RawCodedFormulaSubstitutionAtom M replacement depth right right) ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawFormulaEqCode M left right).
Proof.
  intros M hPA replacement left right hleft hright depth.
  exact (raw_codedFormulaDiagonalSubstitution_eq M hPA
    replacement depth left right (hleft depth) (hright depth)).
Qed.

Lemma raw_codedFormulaDiagonalSubstitutionAtAllDepths_imp : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement left right,
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement left ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement right ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawFormulaImpCode M left right).
Proof.
  intros M hPA replacement left right hleft hright depth.
  exact (raw_codedFormulaDiagonalSubstitution_imp M hPA
    replacement depth left right (hleft depth) (hright depth)).
Qed.

Lemma raw_codedFormulaDiagonalSubstitutionAtAllDepths_and : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement left right,
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement left ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement right ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawFormulaAndCode M left right).
Proof.
  intros M hPA replacement left right hleft hright depth.
  exact (raw_codedFormulaDiagonalSubstitution_and M hPA
    replacement depth left right (hleft depth) (hright depth)).
Qed.

Lemma raw_codedFormulaDiagonalSubstitutionAtAllDepths_or : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement left right,
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement left ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement right ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawFormulaOrCode M left right).
Proof.
  intros M hPA replacement left right hleft hright depth.
  exact (raw_codedFormulaDiagonalSubstitution_or M hPA
    replacement depth left right (hleft depth) (hright depth)).
Qed.

Lemma raw_codedFormulaDiagonalSubstitutionAtAllDepths_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement child,
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement child ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawFormulaAllCode M child).
Proof.
  intros M hPA replacement child hchild depth.
  exact (raw_codedFormulaDiagonalSubstitution_all M hPA
    replacement depth child (hchild (raw_succ M depth))).
Qed.

Lemma raw_codedFormulaDiagonalSubstitutionAtAllDepths_ex : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement child,
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement child ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawFormulaExCode M child).
Proof.
  intros M hPA replacement child hchild depth.
  exact (raw_codedFormulaDiagonalSubstitution_ex M hPA
    replacement depth child (hchild (raw_succ M depth))).
Qed.

(** A one-free-variable formula need not be fixed by substitution at depth
    zero.  It is fixed at every positive depth, however, and that is exactly
    the premise required when the formula is placed below a fresh [all] or
    [exists].  Keeping this weaker invariant avoids asking the future dynamic
    source formula to be closed before the induction compiler binds it. *)
Definition RawCodedFormulaDiagonalSubstitutionAtPositiveDepths
    (M : RawPAModel) (replacement input : M) : Prop :=
  forall depth : M,
    RawCodedFormulaDiagonalSubstitution M replacement
      (raw_succ M depth) input.

Arguments RawCodedFormulaDiagonalSubstitutionAtPositiveDepths
  M replacement input : clear implicits.

Lemma raw_codedFormulaDiagonalSubstitutionAtPositiveDepths_of_all : forall
    (M : RawPAModel) replacement input,
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement input ->
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement input.
Proof. intros M replacement input hall depth. exact (hall (raw_succ M depth)). Qed.

Lemma raw_codedFormulaDiagonalSubstitutionAtPositiveDepths_bot : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement,
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement
    (rawFormulaBotCode M).
Proof.
  intros M hPA replacement depth.
  exact (raw_codedFormulaDiagonalSubstitution_bot M hPA
    replacement (raw_succ M depth)).
Qed.

Lemma raw_codedFormulaDiagonalSubstitutionAtPositiveDepths_eq : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement left right,
  (forall depth,
    RawCodedFormulaSubstitutionAtom M replacement
      (raw_succ M depth) left left) ->
  (forall depth,
    RawCodedFormulaSubstitutionAtom M replacement
      (raw_succ M depth) right right) ->
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement
    (rawFormulaEqCode M left right).
Proof.
  intros M hPA replacement left right hleft hright depth.
  exact (raw_codedFormulaDiagonalSubstitution_eq M hPA
    replacement (raw_succ M depth) left right
    (hleft depth) (hright depth)).
Qed.

Lemma raw_codedFormulaDiagonalSubstitutionAtPositiveDepths_imp : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement left right,
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement left ->
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement right ->
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement
    (rawFormulaImpCode M left right).
Proof.
  intros M hPA replacement left right hleft hright depth.
  exact (raw_codedFormulaDiagonalSubstitution_imp M hPA
    replacement (raw_succ M depth) left right
    (hleft depth) (hright depth)).
Qed.

Lemma raw_codedFormulaDiagonalSubstitutionAtPositiveDepths_and : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement left right,
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement left ->
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement right ->
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement
    (rawFormulaAndCode M left right).
Proof.
  intros M hPA replacement left right hleft hright depth.
  exact (raw_codedFormulaDiagonalSubstitution_and M hPA
    replacement (raw_succ M depth) left right
    (hleft depth) (hright depth)).
Qed.

Lemma raw_codedFormulaDiagonalSubstitutionAtPositiveDepths_or : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement left right,
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement left ->
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement right ->
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement
    (rawFormulaOrCode M left right).
Proof.
  intros M hPA replacement left right hleft hright depth.
  exact (raw_codedFormulaDiagonalSubstitution_or M hPA
    replacement (raw_succ M depth) left right
    (hleft depth) (hright depth)).
Qed.

Lemma raw_codedFormulaDiagonalSubstitutionAtAllDepths_all_of_positive :
    forall (M : RawPAModel), RawPASatisfies M -> forall replacement child,
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths
    M replacement child ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawFormulaAllCode M child).
Proof.
  intros M hPA replacement child hchild depth.
  exact (raw_codedFormulaDiagonalSubstitution_all M hPA
    replacement depth child (hchild depth)).
Qed.

Lemma raw_codedFormulaDiagonalSubstitutionAtAllDepths_ex_of_positive :
    forall (M : RawPAModel), RawPASatisfies M -> forall replacement child,
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths
    M replacement child ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawFormulaExCode M child).
Proof.
  intros M hPA replacement child hchild depth.
  exact (raw_codedFormulaDiagonalSubstitution_ex M hPA
    replacement depth child (hchild depth)).
Qed.

(** The exact syntactic shell generated by [RawCodedPAAxiomInduction].

    The zero instance is closed outright.  The source and successor instance
    may each retain the induction variable, so only their positive-depth
    stability is assumed.  Their enclosing universal quantifiers turn those
    weaker certificates into all-depth certificates before the two binary
    constructor steps assemble the body.
*)
Theorem raw_codedFormulaDiagonalSubstitutionAtAllDepths_inductionBody :
    forall (M : RawPAModel), RawPASatisfies M -> forall replacement
      source successorInstance zeroInstance,
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths
    M replacement source ->
  RawCodedFormulaDiagonalSubstitutionAtPositiveDepths
    M replacement successorInstance ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths
    M replacement zeroInstance ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
    (rawFormulaImpCode M
      (rawFormulaAndCode M zeroInstance
        (rawFormulaAllCode M
          (rawFormulaImpCode M source successorInstance)))
      (rawFormulaAllCode M source)).
Proof.
  intros M hPA replacement source successorInstance zeroInstance
    hsource hsuccessor hzero.
  assert (hstepPositive :
      RawCodedFormulaDiagonalSubstitutionAtPositiveDepths M replacement
        (rawFormulaImpCode M source successorInstance)).
  {
    exact (raw_codedFormulaDiagonalSubstitutionAtPositiveDepths_imp M hPA
      replacement source successorInstance hsource hsuccessor).
  }
  assert (hstepAll :
      RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
        (rawFormulaAllCode M
          (rawFormulaImpCode M source successorInstance))).
  {
    exact (raw_codedFormulaDiagonalSubstitutionAtAllDepths_all_of_positive
      M hPA replacement (rawFormulaImpCode M source successorInstance)
      hstepPositive).
  }
  assert (hpremise :
      RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
        (rawFormulaAndCode M zeroInstance
          (rawFormulaAllCode M
            (rawFormulaImpCode M source successorInstance)))).
  {
    exact (raw_codedFormulaDiagonalSubstitutionAtAllDepths_and M hPA
      replacement zeroInstance
      (rawFormulaAllCode M
        (rawFormulaImpCode M source successorInstance))
      hzero hstepAll).
  }
  assert (hsourceAll :
      RawCodedFormulaDiagonalSubstitutionAtAllDepths M replacement
        (rawFormulaAllCode M source)).
  {
    exact (raw_codedFormulaDiagonalSubstitutionAtAllDepths_all_of_positive
      M hPA replacement source hsource).
  }
  exact (raw_codedFormulaDiagonalSubstitutionAtAllDepths_imp M hPA
    replacement
    (rawFormulaAndCode M zeroInstance
      (rawFormulaAllCode M
        (rawFormulaImpCode M source successorInstance)))
    (rawFormulaAllCode M source) hpremise hsourceAll).
Qed.

End PABoundedRawCodedFormulaDiagonalOperationComposition.
