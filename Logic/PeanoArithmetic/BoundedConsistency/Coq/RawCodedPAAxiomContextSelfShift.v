(**
  PA-axiom contexts are fixed by the eigenvariable context shift.

  The finite PA axioms are ordinary closed quotations.  The induction
  branch is subtler: its source formula and its closure count may both be
  nonstandard elements of an arbitrary model of PA.  Consequently this file
  never decodes either carrier value.  Instead it develops the small amount
  of traversal composition needed to prove, internally, that shifting above
  a certified syntactic bound is the identity and that iterated universal
  closure lowers that cutoff back to zero.

  The first construction below is a prefix-retaining append operation for
  term-shift traversals.  It is deliberately explicit.  Later concatenation
  copies a possibly nonstandard child traversal by an application of PA's
  definable induction, so no metatheoretic recursion is hidden in the proof.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedAssignmentTotality
  RawCodedProofDescent RawCodedFormulaRankStep RawCodedFormulaRankTraversal
  RawCodedFormulaRankTotality
  RawCodedFormulaOperations
  RawCodedPAAxiomWitness RawCodedContextLists RawCodedContextShift
  RawCodedRestrictedPAProof RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthReindexing.

Import ListNotations.

Module PABoundedRawCodedPAAxiomContextSelfShift.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthReindexing.

(** ------------------------------------------------------------------
    Prefix extension for the two columns of a term-shift traversal. *)

Definition RawTermShiftTablePrefixExtension (M : RawPAModel)
    (bound
      oldSourceCode oldSourceStep oldTargetCode oldTargetStep
      newSourceCode newSourceStep newTargetCode newTargetStep : M) : Prop :=
  (forall index value,
    rawLt M index bound ->
    RawCodedAssignmentLookup M
      oldSourceCode oldSourceStep index value ->
    RawCodedAssignmentLookup M
      newSourceCode newSourceStep index value) /\
  (forall index value,
    rawLt M index bound ->
    RawCodedAssignmentLookup M
      oldTargetCode oldTargetStep index value ->
    RawCodedAssignmentLookup M
      newTargetCode newTargetStep index value).

Arguments RawTermShiftTablePrefixExtension M bound
  oldSourceCode oldSourceStep oldTargetCode oldTargetStep
  newSourceCode newSourceStep newTargetCode newTargetStep : clear implicits.

Lemma raw_termShiftPairLookup_prefix_extend : forall
    (M : RawPAModel) bound
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    newSourceCode newSourceStep newTargetCode newTargetStep
    index input output,
  RawTermShiftTablePrefixExtension M bound
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    newSourceCode newSourceStep newTargetCode newTargetStep ->
  rawLt M index bound ->
  RawCodedTermOperationPairLookup M
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    index input output ->
  RawCodedTermOperationPairLookup M
    newSourceCode newSourceStep newTargetCode newTargetStep
    index input output.
Proof.
  intros M bound oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    newSourceCode newSourceStep newTargetCode newTargetStep
    index input output [hsource htarget] hindex [hin hout].
  split.
  - exact (hsource index input hindex hin).
  - exact (htarget index output hindex hout).
Qed.

(** Every recursive premise of a term row lies strictly before the current
    row.  A prefix extension therefore transports the row unchanged. *)
Lemma raw_termShiftTraversalRow_prefix_extend : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount bound current
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    newSourceCode newSourceStep newTargetCode newTargetStep
    input output,
  RawTermShiftTablePrefixExtension M bound
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    newSourceCode newSourceStep newTargetCode newTargetStep ->
  rawLe M current bound ->
  RawCodedTermShiftTraversalRow M cutoff amount
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    current input output ->
  RawCodedTermShiftTraversalRow M cutoff amount
    newSourceCode newSourceStep newTargetCode newTargetStep
    current input output.
Proof.
  intros M hPA cutoff amount bound current
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    newSourceCode newSourceStep newTargetCode newTargetStep
    input output hext hcurrent hrow.
  destruct hrow as
    [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - left. exact hvar.
  - right. left. exact hzero.
  - right. right. left.
    destruct hsucc as
      (childIndex & inputChild & outputChild & hchild & hlookup &
       hinput & houtput).
    exists childIndex, inputChild, outputChild.
    split; [exact hchild |].
    split.
    + apply (raw_termShiftPairLookup_prefix_extend M bound
        oldSourceCode oldSourceStep oldTargetCode oldTargetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        childIndex inputChild outputChild hext).
      * exact (raw_lt_le_trans_pair M hPA
          childIndex current bound hchild hcurrent).
      * exact hlookup.
    + split; assumption.
  - right. right. right. left.
    destruct hadd as
      (leftIndex & inputLeft & outputLeft &
       rightIndex & inputRight & outputRight &
       hleft & hleftLookup & hright & hrightLookup & hinput & houtput).
    exists leftIndex, inputLeft, outputLeft,
      rightIndex, inputRight, outputRight.
    split; [exact hleft |].
    split.
    + apply (raw_termShiftPairLookup_prefix_extend M bound
        oldSourceCode oldSourceStep oldTargetCode oldTargetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        leftIndex inputLeft outputLeft hext).
      * exact (raw_lt_le_trans_pair M hPA
          leftIndex current bound hleft hcurrent).
      * exact hleftLookup.
    + split; [exact hright |].
      split.
      * apply (raw_termShiftPairLookup_prefix_extend M bound
          oldSourceCode oldSourceStep oldTargetCode oldTargetStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          rightIndex inputRight outputRight hext).
        -- exact (raw_lt_le_trans_pair M hPA
             rightIndex current bound hright hcurrent).
        -- exact hrightLookup.
      * split; assumption.
  - right. right. right. right.
    destruct hmul as
      (leftIndex & inputLeft & outputLeft &
       rightIndex & inputRight & outputRight &
       hleft & hleftLookup & hright & hrightLookup & hinput & houtput).
    exists leftIndex, inputLeft, outputLeft,
      rightIndex, inputRight, outputRight.
    split; [exact hleft |].
    split.
    + apply (raw_termShiftPairLookup_prefix_extend M bound
        oldSourceCode oldSourceStep oldTargetCode oldTargetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        leftIndex inputLeft outputLeft hext).
      * exact (raw_lt_le_trans_pair M hPA
          leftIndex current bound hleft hcurrent).
      * exact hleftLookup.
    + split; [exact hright |].
      split.
      * apply (raw_termShiftPairLookup_prefix_extend M bound
          oldSourceCode oldSourceStep oldTargetCode oldTargetStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          rightIndex inputRight outputRight hext).
        -- exact (raw_lt_le_trans_pair M hPA
             rightIndex current bound hright hcurrent).
        -- exact hrightLookup.
      * split; assumption.
Qed.

Definition RawTermShiftTraversalBundle (M : RawPAModel)
    (cutoff amount sourceCode sourceStep targetCode targetStep bound : M)
    : Prop :=
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound /\
  RawCodedAssignmentDefinedThrough M targetCode targetStep bound /\
  RawCodedTermShiftRows M cutoff amount
    sourceCode sourceStep targetCode targetStep bound /\
  rawLe M (raw_zero M) cutoff.

Arguments RawTermShiftTraversalBundle M cutoff amount
  sourceCode sourceStep targetCode targetStep bound : clear implicits.

Definition termShiftTraversalBundleTermAt
    (cutoff amount sourceCode sourceStep targetCode targetStep bound : term)
    : formula :=
  operationAnd4
    (codedAssignmentDefinedThroughTermAt sourceCode sourceStep bound)
    (codedAssignmentDefinedThroughTermAt targetCode targetStep bound)
    (codedTermShiftRowsTermAt cutoff amount
      sourceCode sourceStep targetCode targetStep bound)
    (Formula.leTermAt tZero cutoff).

Lemma raw_sat_termShiftTraversalBundleTermAt_iff : forall
    (M : RawPAModel) e cutoff amount sourceCode sourceStep
      targetCode targetStep bound,
  raw_formula_sat M e
    (termShiftTraversalBundleTermAt cutoff amount
      sourceCode sourceStep targetCode targetStep bound) <->
  RawTermShiftTraversalBundle M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e bound).
Proof.
  intros. unfold termShiftTraversalBundleTermAt,
    RawTermShiftTraversalBundle, operationAnd4.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff,
    raw_sat_codedTermShiftRowsTermAt_iff,
    raw_sat_leTermAt_iff_rank.
  reflexivity.
Qed.

(** Append one already closed row to a term-shift bundle.  Both beta steps
    may change; [RawTermShiftTablePrefixExtension] records exactly what is
    preserved. *)
Theorem raw_termShiftTraversalBundle_append : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount sourceCode sourceStep targetCode targetStep bound
      input output,
  RawTermShiftTraversalBundle M cutoff amount
    sourceCode sourceStep targetCode targetStep bound ->
  RawCodedTermShiftTraversalRow M cutoff amount
    sourceCode sourceStep targetCode targetStep bound input output ->
  exists newSourceCode newSourceStep newTargetCode newTargetStep : M,
    RawTermShiftTraversalBundle M cutoff amount
      newSourceCode newSourceStep newTargetCode newTargetStep
      (raw_succ M bound) /\
    RawTermShiftTablePrefixExtension M bound
      sourceCode sourceStep targetCode targetStep
      newSourceCode newSourceStep newTargetCode newTargetStep /\
    RawCodedTermOperationPairLookup M
      newSourceCode newSourceStep newTargetCode newTargetStep
      bound input output.
Proof.
  intros M hPA cutoff amount sourceCode sourceStep targetCode targetStep
    bound input output [hsourceDefined [htargetDefined [hrows hnonneg]]]
    hclosed.
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    sourceCode sourceStep bound input hsourceDefined)
    as [newSourceCode [newSourceStep
      [hnewSourceDefined [hsourcePrefix hsourceRoot]]]].
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    targetCode targetStep bound output htargetDefined)
    as [newTargetCode [newTargetStep
      [hnewTargetDefined [htargetPrefix htargetRoot]]]].
  set (hext := conj hsourcePrefix htargetPrefix).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep.
  split.
  - split; [exact hnewSourceDefined |].
    split; [exact hnewTargetDefined |].
    split; [|exact hnonneg].
    intros index rowInput rowOutput hindex hlookup.
    destruct (raw_lt_succ_cases M hPA index bound hindex)
      as [hindexOld | ->].
    + destruct (hsourceDefined index hindexOld)
        as [oldInput holdInput].
      destruct (htargetDefined index hindexOld)
        as [oldOutput holdOutput].
      assert (hnewOld : RawCodedTermOperationPairLookup M
          newSourceCode newSourceStep newTargetCode newTargetStep
          index oldInput oldOutput).
      {
        apply (raw_termShiftPairLookup_prefix_extend M bound
          sourceCode sourceStep targetCode targetStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          index oldInput oldOutput hext hindexOld).
        split; assumption.
      }
      destruct hlookup as [hlookupInput hlookupOutput].
      destruct hnewOld as [hnewOldInput hnewOldOutput].
      assert (hinputEq : rowInput = oldInput).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newSourceCode newSourceStep index rowInput oldInput
          hlookupInput hnewOldInput).
      }
      assert (houtputEq : rowOutput = oldOutput).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newTargetCode newTargetStep index rowOutput oldOutput
          hlookupOutput hnewOldOutput).
      }
      subst rowInput. subst rowOutput.
      apply (raw_termShiftTraversalRow_prefix_extend M hPA
        cutoff amount bound index
        sourceCode sourceStep targetCode targetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        oldInput oldOutput hext).
      * exact (raw_lt_to_le M index bound hindexOld).
      * apply (hrows index oldInput oldOutput hindexOld).
        split; assumption.
    + destruct hlookup as [hlookupInput hlookupOutput].
      assert (hinputEq : rowInput = input).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newSourceCode newSourceStep bound rowInput input
          hlookupInput hsourceRoot).
      }
      assert (houtputEq : rowOutput = output).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newTargetCode newTargetStep bound rowOutput output
          hlookupOutput htargetRoot).
      }
      subst rowInput. subst rowOutput.
      apply (raw_termShiftTraversalRow_prefix_extend M hPA
        cutoff amount bound bound
        sourceCode sourceStep targetCode targetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        input output hext).
      * apply raw_rank_le_refl. exact hPA.
      * exact hclosed.
  - split; [exact hext |]. split; assumption.
Qed.

(** ------------------------------------------------------------------
    Copy and concatenate arbitrary (possibly nonstandard) term traces. *)

Definition RawTermShiftPairOffsetEmbedding (M : RawPAModel)
    (offset current
      sourceCode sourceStep targetCode targetStep
      copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep : M)
    : Prop :=
  forall index input output,
    rawLt M index current ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep index input output ->
    RawCodedTermOperationPairLookup M
      copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
      (raw_add M offset index) input output.

Arguments RawTermShiftPairOffsetEmbedding M offset current
  sourceCode sourceStep targetCode targetStep
  copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
  : clear implicits.

Definition termShiftPairOffsetEmbeddingTermAt
    (offset current
      sourceCode sourceStep targetCode targetStep
      copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
      : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 current))
      (pImp
        (codedTermOperationPairLookupTermAt
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0))
        (codedTermOperationPairLookupTermAt
          (liftTerm 3 copiedSourceCode) (liftTerm 3 copiedSourceStep)
          (liftTerm 3 copiedTargetCode) (liftTerm 3 copiedTargetStep)
          (tAdd (liftTerm 3 offset) (tVar 2))
          (tVar 1) (tVar 0)))))).

Lemma raw_sat_termShiftPairOffsetEmbeddingTermAt_iff : forall
    (M : RawPAModel) e offset current
      sourceCode sourceStep targetCode targetStep
      copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep,
  raw_formula_sat M e
    (termShiftPairOffsetEmbeddingTermAt offset current
      sourceCode sourceStep targetCode targetStep
      copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep)
  <->
  RawTermShiftPairOffsetEmbedding M
    (raw_term_eval M e offset) (raw_term_eval M e current)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e copiedSourceCode)
    (raw_term_eval M e copiedSourceStep)
    (raw_term_eval M e copiedTargetCode)
    (raw_term_eval M e copiedTargetStep).
Proof.
  intros. unfold termShiftPairOffsetEmbeddingTermAt,
    RawTermShiftPairOffsetEmbedding.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  cbn [raw_term_eval scons]. split; intros h.
  - repeat setoid_rewrite raw_operation_eval_liftTerm_three in h.
    exact h.
  - repeat setoid_rewrite raw_operation_eval_liftTerm_three.
    exact h.
Qed.

Lemma raw_termShiftTraversalRow_offset : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount offset current
    sourceCode sourceStep targetCode targetStep
    copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
    input output,
  RawTermShiftPairOffsetEmbedding M offset current
    sourceCode sourceStep targetCode targetStep
    copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep ->
  RawCodedTermShiftTraversalRow M cutoff amount
    sourceCode sourceStep targetCode targetStep current input output ->
  RawCodedTermShiftTraversalRow M cutoff amount
    copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
    (raw_add M offset current) input output.
Proof.
  intros M hPA cutoff amount offset current
    sourceCode sourceStep targetCode targetStep
    copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
    input output hembed hrow.
  destruct hrow as
    [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - left. exact hvar.
  - right. left. exact hzero.
  - right. right. left.
    destruct hsucc as
      (childIndex & inputChild & outputChild & hchild & hlookup &
       hinput & houtput).
    exists (raw_add M offset childIndex), inputChild, outputChild.
    split.
    + exact (raw_lt_add_left_fixedTruth M hPA offset
        childIndex current hchild).
    + split.
      * exact (hembed childIndex inputChild outputChild hchild hlookup).
      * split; assumption.
  - right. right. right. left.
    destruct hadd as
      (leftIndex & inputLeft & outputLeft &
       rightIndex & inputRight & outputRight &
       hleft & hleftLookup & hright & hrightLookup & hinput & houtput).
    exists (raw_add M offset leftIndex), inputLeft, outputLeft,
      (raw_add M offset rightIndex), inputRight, outputRight.
    split.
    + exact (raw_lt_add_left_fixedTruth M hPA offset
        leftIndex current hleft).
    + split.
      * exact (hembed leftIndex inputLeft outputLeft hleft hleftLookup).
      * split.
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             rightIndex current hright).
        -- split.
           ++ exact (hembed rightIndex inputRight outputRight
                hright hrightLookup).
           ++ split; assumption.
  - right. right. right. right.
    destruct hmul as
      (leftIndex & inputLeft & outputLeft &
       rightIndex & inputRight & outputRight &
       hleft & hleftLookup & hright & hrightLookup & hinput & houtput).
    exists (raw_add M offset leftIndex), inputLeft, outputLeft,
      (raw_add M offset rightIndex), inputRight, outputRight.
    split.
    + exact (raw_lt_add_left_fixedTruth M hPA offset
        leftIndex current hleft).
    + split.
      * exact (hembed leftIndex inputLeft outputLeft hleft hleftLookup).
      * split.
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             rightIndex current hright).
        -- split.
           ++ exact (hembed rightIndex inputRight outputRight
                hright hrightLookup).
           ++ split; assumption.
Qed.

Definition RawTermShiftTraversalCopyState (M : RawPAModel)
    (cutoff amount
      sourceCode sourceStep targetCode targetStep sourceBound offset
      initialRootIndex initialInput initialOutput current : M) : Prop :=
  rawLe M current sourceBound ->
  exists copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep,
    RawTermShiftTraversalBundle M cutoff amount
      copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
      (raw_add M offset current) /\
    RawCodedTermOperationPairLookup M
      copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
      initialRootIndex initialInput initialOutput /\
    RawTermShiftPairOffsetEmbedding M offset current
      sourceCode sourceStep targetCode targetStep
      copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep.

Arguments RawTermShiftTraversalCopyState M cutoff amount
  sourceCode sourceStep targetCode targetStep sourceBound offset
  initialRootIndex initialInput initialOutput current : clear implicits.

Definition termShiftTraversalCopyStateTermAt
    (cutoff amount
      sourceCode sourceStep targetCode targetStep sourceBound offset
      initialRootIndex initialInput initialOutput current : term) : formula :=
  pImp
    (Formula.leTermAt current sourceBound)
    (operationEx4
      (operationAnd3
        (termShiftTraversalBundleTermAt
          (liftTerm 4 cutoff) (liftTerm 4 amount)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)
          (tAdd (liftTerm 4 offset) (liftTerm 4 current)))
        (codedTermOperationPairLookupTermAt
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)
          (liftTerm 4 initialRootIndex)
          (liftTerm 4 initialInput) (liftTerm 4 initialOutput))
        (termShiftPairOffsetEmbeddingTermAt
          (liftTerm 4 offset) (liftTerm 4 current)
          (liftTerm 4 sourceCode) (liftTerm 4 sourceStep)
          (liftTerm 4 targetCode) (liftTerm 4 targetStep)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)))).

Lemma raw_sat_termShiftTraversalCopyStateTermAt_iff : forall
    (M : RawPAModel) e cutoff amount
      sourceCode sourceStep targetCode targetStep sourceBound offset
      initialRootIndex initialInput initialOutput current,
  raw_formula_sat M e
    (termShiftTraversalCopyStateTermAt cutoff amount
      sourceCode sourceStep targetCode targetStep sourceBound offset
      initialRootIndex initialInput initialOutput current) <->
  RawTermShiftTraversalCopyState M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e sourceBound) (raw_term_eval M e offset)
    (raw_term_eval M e initialRootIndex)
    (raw_term_eval M e initialInput) (raw_term_eval M e initialOutput)
    (raw_term_eval M e current).
Proof.
  intros. unfold termShiftTraversalCopyStateTermAt, operationEx4,
    operationAnd3, RawTermShiftTraversalCopyState.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank.
  setoid_rewrite raw_sat_termShiftTraversalBundleTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_termShiftPairOffsetEmbeddingTermAt_iff.
  cbn [raw_term_eval scons].
  split; intros h hle;
    destruct (h hle) as
      (copiedSourceCode & copiedSourceStep & copiedTargetCode &
       copiedTargetStep & hresult);
    exists copiedSourceCode, copiedSourceStep,
      copiedTargetCode, copiedTargetStep.
  - repeat rewrite (raw_rankTraversal_eval_liftTerm_four M
      copiedTargetStep copiedTargetCode copiedSourceStep copiedSourceCode e)
      in hresult.
    exact hresult.
  - repeat rewrite (raw_rankTraversal_eval_liftTerm_four M
      copiedTargetStep copiedTargetCode copiedSourceStep copiedSourceCode e).
    exact hresult.
Qed.

Lemma raw_termShiftPairOffsetEmbedding_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall offset
      sourceCode sourceStep targetCode targetStep
      copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep,
  RawTermShiftPairOffsetEmbedding M offset (raw_zero M)
    sourceCode sourceStep targetCode targetStep
    copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep.
Proof.
  intros M hPA offset sourceCode sourceStep targetCode targetStep
    copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
    index input output hindex _.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Lemma raw_termShiftTraversalCopyState_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount sourceCode sourceStep targetCode targetStep sourceBound
      offset initialSourceCode initialSourceStep
      initialTargetCode initialTargetStep
      initialRootIndex initialInput initialOutput,
  RawTermShiftTraversalBundle M cutoff amount
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    offset ->
  RawCodedTermOperationPairLookup M
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    initialRootIndex initialInput initialOutput ->
  RawTermShiftTraversalCopyState M cutoff amount
    sourceCode sourceStep targetCode targetStep sourceBound offset
    initialRootIndex initialInput initialOutput (raw_zero M).
Proof.
  intros M hPA cutoff amount sourceCode sourceStep targetCode targetStep
    sourceBound offset initialSourceCode initialSourceStep
    initialTargetCode initialTargetStep initialRootIndex initialInput
    initialOutput hinitialBundle hinitialRoot _.
  exists initialSourceCode, initialSourceStep,
    initialTargetCode, initialTargetStep.
  rewrite raw_assignmentTotality_add_zero_right by exact hPA.
  split; [exact hinitialBundle |]. split; [exact hinitialRoot |].
  exact (raw_termShiftPairOffsetEmbedding_zero M hPA offset
    sourceCode sourceStep targetCode targetStep
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep).
Qed.

Lemma raw_termShiftTraversalCopyState_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount sourceCode sourceStep targetCode targetStep
      sourceBound sourceRootIndex sourceInput sourceOutput
      offset initialRootIndex initialInput initialOutput current,
  RawCodedTermShiftTrace M cutoff amount
    sourceCode sourceStep targetCode targetStep
    sourceBound sourceRootIndex sourceInput sourceOutput ->
  rawLt M initialRootIndex offset ->
  RawTermShiftTraversalCopyState M cutoff amount
    sourceCode sourceStep targetCode targetStep sourceBound offset
    initialRootIndex initialInput initialOutput current ->
  RawTermShiftTraversalCopyState M cutoff amount
    sourceCode sourceStep targetCode targetStep sourceBound offset
    initialRootIndex initialInput initialOutput (raw_succ M current).
Proof.
  intros M hPA cutoff amount sourceCode sourceStep targetCode targetStep
    sourceBound sourceRootIndex sourceInput sourceOutput
    offset initialRootIndex initialInput initialOutput current
    hsource hinitialBelow hcurrent hsuccLe.
  destruct hsource as
    [hsourceDefined [htargetDefined [_ [_ [hsourceRows hnonneg]]]]].
  assert (hcurrentBelow : rawLt M current sourceBound).
  { exact (raw_rank_lt_of_succ_le M hPA current sourceBound hsuccLe). }
  assert (hcurrentLe : rawLe M current sourceBound).
  { exact (raw_lt_to_le M current sourceBound hcurrentBelow). }
  destruct (hcurrent hcurrentLe) as
    (copiedSourceCode & copiedSourceStep & copiedTargetCode &
     copiedTargetStep & hcopiedBundle & hinitialRoot & hembed).
  destruct (hsourceDefined current hcurrentBelow)
    as [rowInput hrowInput].
  destruct (htargetDefined current hcurrentBelow)
    as [rowOutput hrowOutput].
  assert (hsourcePair : RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep
      current rowInput rowOutput).
  { split; assumption. }
  pose proof (hsourceRows current rowInput rowOutput
    hcurrentBelow hsourcePair) as hsourceRow.
  pose proof (raw_termShiftTraversalRow_offset M hPA
    cutoff amount offset current
    sourceCode sourceStep targetCode targetStep
    copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
    rowInput rowOutput hembed hsourceRow) as hcopiedRow.
  destruct (raw_termShiftTraversalBundle_append M hPA
    cutoff amount copiedSourceCode copiedSourceStep
    copiedTargetCode copiedTargetStep (raw_add M offset current)
    rowInput rowOutput hcopiedBundle hcopiedRow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        hnewBundle & hprefix & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep.
  split.
  - rewrite raw_add_succ by exact hPA. exact hnewBundle.
  - split.
    + apply (raw_termShiftPairLookup_prefix_extend M
        (raw_add M offset current)
        copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        initialRootIndex initialInput initialOutput hprefix).
      * exact (raw_lt_le_trans_pair M hPA
          initialRootIndex offset (raw_add M offset current)
          hinitialBelow (raw_proof_left_le_sum M offset current)).
      * exact hinitialRoot.
    + intros index input output hindex hlookup.
      destruct (raw_lt_succ_cases M hPA index current hindex)
        as [hindexOld | ->].
      * apply (raw_termShiftPairLookup_prefix_extend M
          (raw_add M offset current)
          copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          (raw_add M offset index) input output hprefix).
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             index current hindexOld).
        -- exact (hembed index input output hindexOld hlookup).
      * destruct hlookup as [hlookupInput hlookupOutput].
        assert (hinputEq : input = rowInput).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            sourceCode sourceStep current input rowInput
            hlookupInput hrowInput).
        }
        assert (houtputEq : output = rowOutput).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            targetCode targetStep current output rowOutput
            hlookupOutput hrowOutput).
        }
        subst input. subst output. exact hnewRoot.
Qed.

Theorem raw_termShiftTraversalCopyState_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount sourceCode sourceStep targetCode targetStep
      sourceBound sourceRootIndex sourceInput sourceOutput
      offset initialSourceCode initialSourceStep
      initialTargetCode initialTargetStep
      initialRootIndex initialInput initialOutput,
  RawCodedTermShiftTrace M cutoff amount
    sourceCode sourceStep targetCode targetStep
    sourceBound sourceRootIndex sourceInput sourceOutput ->
  RawTermShiftTraversalBundle M cutoff amount
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    offset ->
  rawLt M initialRootIndex offset ->
  RawCodedTermOperationPairLookup M
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    initialRootIndex initialInput initialOutput ->
  forall current,
  RawTermShiftTraversalCopyState M cutoff amount
    sourceCode sourceStep targetCode targetStep sourceBound offset
    initialRootIndex initialInput initialOutput current.
Proof.
  intros M hPA cutoff amount sourceCode sourceStep targetCode targetStep
    sourceBound sourceRootIndex sourceInput sourceOutput
    offset initialSourceCode initialSourceStep
    initialTargetCode initialTargetStep
    initialRootIndex initialInput initialOutput
    hsource hinitialBundle hinitialBelow hinitialRoot.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => cutoff
    | 1 => amount
    | 2 => sourceCode
    | 3 => sourceStep
    | 4 => targetCode
    | 5 => targetStep
    | 6 => sourceBound
    | 7 => offset
    | 8 => initialRootIndex
    | 9 => initialInput
    | _ => initialOutput
    end).
  set (phi := termShiftTraversalCopyStateTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
    (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_termShiftTraversalCopyStateTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
        (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_termShiftTraversalCopyState_zero M hPA
        cutoff amount sourceCode sourceStep targetCode targetStep sourceBound
        offset initialSourceCode initialSourceStep
        initialTargetCode initialTargetStep
        initialRootIndex initialInput initialOutput
        hinitialBundle hinitialRoot).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_termShiftTraversalCopyStateTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
          (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_termShiftTraversalCopyStateTermAt_iff M
        (scons M (raw_succ M current) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
        (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_termShiftTraversalCopyState_succ M hPA
        cutoff amount sourceCode sourceStep targetCode targetStep
        sourceBound sourceRootIndex sourceInput sourceOutput
        offset initialRootIndex initialInput initialOutput current
        hsource hinitialBelow hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_termShiftTraversalCopyStateTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
      (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 0))
    (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

(** Concatenation retains the first root and makes the shifted second root
    the distinguished root of the combined traversal. *)
Theorem raw_termShiftTraces_concatenate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount
      firstSourceCode firstSourceStep firstTargetCode firstTargetStep
      firstBound firstRootIndex firstInput firstOutput
      secondSourceCode secondSourceStep secondTargetCode secondTargetStep
      secondBound secondRootIndex secondInput secondOutput,
  RawCodedTermShiftTrace M cutoff amount
    firstSourceCode firstSourceStep firstTargetCode firstTargetStep
    firstBound firstRootIndex firstInput firstOutput ->
  RawCodedTermShiftTrace M cutoff amount
    secondSourceCode secondSourceStep secondTargetCode secondTargetStep
    secondBound secondRootIndex secondInput secondOutput ->
  exists newSourceCode newSourceStep newTargetCode newTargetStep : M,
    RawCodedTermShiftTrace M cutoff amount
      newSourceCode newSourceStep newTargetCode newTargetStep
      (raw_add M firstBound secondBound)
      (raw_add M firstBound secondRootIndex) secondInput secondOutput /\
    RawCodedTermOperationPairLookup M
      newSourceCode newSourceStep newTargetCode newTargetStep
      firstRootIndex firstInput firstOutput.
Proof.
  intros M hPA cutoff amount
    firstSourceCode firstSourceStep firstTargetCode firstTargetStep
    firstBound firstRootIndex firstInput firstOutput
    secondSourceCode secondSourceStep secondTargetCode secondTargetStep
    secondBound secondRootIndex secondInput secondOutput
    hfirst hsecond.
  destruct hfirst as
    [hfirstSource [hfirstTarget [hfirstBelow
      [hfirstRoot [hfirstRows hnonneg]]]]].
  assert (hfirstBundle : RawTermShiftTraversalBundle M cutoff amount
      firstSourceCode firstSourceStep firstTargetCode firstTargetStep
      firstBound).
  { repeat split; assumption. }
  pose proof (raw_termShiftTraversalCopyState_all M hPA
    cutoff amount
    secondSourceCode secondSourceStep secondTargetCode secondTargetStep
    secondBound secondRootIndex secondInput secondOutput
    firstBound firstSourceCode firstSourceStep firstTargetCode firstTargetStep
    firstRootIndex firstInput firstOutput
    hsecond hfirstBundle hfirstBelow hfirstRoot secondBound) as hguard.
  destruct (hguard (raw_rank_le_refl M hPA secondBound)) as
    (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
     hnewBundle & hfirstRetained & hembed).
  destruct hsecond as
    [hsecondSource [hsecondTarget [hsecondBelow
      [hsecondRoot [hsecondRows hsecondNonneg]]]]].
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep.
  split.
  - destruct hnewBundle as [hnewSource [hnewTarget [hnewRows hnewNonneg]]].
    exact (conj hnewSource
      (conj hnewTarget
        (conj
          (raw_lt_add_left_fixedTruth M hPA firstBound
            secondRootIndex secondBound hsecondBelow)
          (conj
            (hembed secondRootIndex secondInput secondOutput
              hsecondBelow hsecondRoot)
            (conj hnewRows hnewNonneg))))).
  - exact hfirstRetained.
Qed.

(** ------------------------------------------------------------------
    Structural constructors for identity term shifts. *)

Lemma raw_termShiftTraversalBundle_empty : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount,
  RawTermShiftTraversalBundle M cutoff amount
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M).
Proof.
  intros M hPA cutoff amount.
  split.
  - exact (raw_codedZeroAssignment_defined_all M hPA (raw_zero M)).
  - split.
    + exact (raw_codedZeroAssignment_defined_all M hPA (raw_zero M)).
    + split.
      * intros index input output hindex _.
        exfalso. exact (raw_not_lt_zero M hPA index hindex).
      * apply raw_rank_zero_le. exact hPA.
Qed.

Lemma raw_codedTermShift_variable_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount index,
  rawLt M index cutoff ->
  RawCodedTermShift M cutoff amount
    (rawTermVarCode M index) (rawTermVarCode M index).
Proof.
  intros M hPA cutoff amount index hindex.
  assert (hrow : RawCodedTermShiftTraversalRow M cutoff amount
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (rawTermVarCode M index) (rawTermVarCode M index)).
  {
    left. exists index, index. split; [reflexivity |].
    split; [reflexivity |]. left. split; [exact hindex | reflexivity].
  }
  destruct (raw_termShiftTraversalBundle_append M hPA
    cutoff amount (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (rawTermVarCode M index) (rawTermVarCode M index)
    (raw_termShiftTraversalBundle_empty M hPA cutoff amount) hrow)
    as (sourceCode & sourceStep & targetCode & targetStep &
        hbundle & _ & hroot).
  exists sourceCode, sourceStep, targetCode, targetStep,
    (raw_succ M (raw_zero M)), (raw_zero M).
  destruct hbundle as [hsource [htarget [hrows hnonneg]]].
  exact (conj hsource
    (conj htarget
      (conj (raw_assignment_lt_self_succ M hPA (raw_zero M))
        (conj hroot (conj hrows hnonneg))))).
Qed.

Lemma raw_codedTermShift_zero_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount,
  RawCodedTermShift M cutoff amount
    (rawTermZeroCode M) (rawTermZeroCode M).
Proof.
  intros M hPA cutoff amount.
  assert (hrow : RawCodedTermShiftTraversalRow M cutoff amount
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (rawTermZeroCode M) (rawTermZeroCode M)).
  { right. left. split; reflexivity. }
  destruct (raw_termShiftTraversalBundle_append M hPA
    cutoff amount (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (rawTermZeroCode M) (rawTermZeroCode M)
    (raw_termShiftTraversalBundle_empty M hPA cutoff amount) hrow)
    as (sourceCode & sourceStep & targetCode & targetStep &
        hbundle & _ & hroot).
  exists sourceCode, sourceStep, targetCode, targetStep,
    (raw_succ M (raw_zero M)), (raw_zero M).
  destruct hbundle as [hsource [htarget [hrows hnonneg]]].
  exact (conj hsource
    (conj htarget
      (conj (raw_assignment_lt_self_succ M hPA (raw_zero M))
        (conj hroot (conj hrows hnonneg))))).
Qed.

Lemma raw_codedTermShift_succ_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount child,
  RawCodedTermShift M cutoff amount child child ->
  RawCodedTermShift M cutoff amount
    (rawTermSuccCode M child) (rawTermSuccCode M child).
Proof.
  intros M hPA cutoff amount child
    (sourceCode & sourceStep & targetCode & targetStep & bound &
     rootIndex & htrace).
  destruct htrace as
    [hsource [htarget [hrootBelow [hroot [hrows hnonneg]]]]].
  assert (hbundle : RawTermShiftTraversalBundle M cutoff amount
      sourceCode sourceStep targetCode targetStep bound).
  { exact (conj hsource (conj htarget (conj hrows hnonneg))). }
  assert (hrow : RawCodedTermShiftTraversalRow M cutoff amount
      sourceCode sourceStep targetCode targetStep bound
      (rawTermSuccCode M child) (rawTermSuccCode M child)).
  {
    right. right. left.
    exists rootIndex, child, child.
    split; [exact hrootBelow |]. split; [exact hroot |].
    split; reflexivity.
  }
  destruct (raw_termShiftTraversalBundle_append M hPA
    cutoff amount sourceCode sourceStep targetCode targetStep bound
    (rawTermSuccCode M child) (rawTermSuccCode M child) hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        hnewBundle & _ & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    (raw_succ M bound), bound.
  destruct hnewBundle as
    [hnewSource [hnewTarget [hnewRows hnewNonneg]]].
  exact (conj hnewSource
    (conj hnewTarget
      (conj (raw_assignment_lt_self_succ M hPA bound)
        (conj hnewRoot (conj hnewRows hnewNonneg))))).
Qed.

Lemma raw_codedTermShift_add_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount left right,
  RawCodedTermShift M cutoff amount left left ->
  RawCodedTermShift M cutoff amount right right ->
  RawCodedTermShift M cutoff amount
    (rawTermAddCode M left right) (rawTermAddCode M left right).
Proof.
  intros M hPA cutoff amount left right
    (leftSourceCode & leftSourceStep & leftTargetCode & leftTargetStep &
     leftBound & leftRootIndex & hleft)
    (rightSourceCode & rightSourceStep & rightTargetCode & rightTargetStep &
     rightBound & rightRootIndex & hright).
  destruct (raw_termShiftTraces_concatenate M hPA cutoff amount
    leftSourceCode leftSourceStep leftTargetCode leftTargetStep
    leftBound leftRootIndex left left
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightBound rightRootIndex right right hleft hright)
    as (sourceCode & sourceStep & targetCode & targetStep &
        hcombined & hleftRoot).
  destruct hcombined as
    [hsource [htarget [hrightBelow [hrightRoot [hrows hnonneg]]]]].
  set (bound := raw_add M leftBound rightBound).
  assert (hbundle : RawTermShiftTraversalBundle M cutoff amount
      sourceCode sourceStep targetCode targetStep bound).
  { exact (conj hsource (conj htarget (conj hrows hnonneg))). }
  assert (hrow : RawCodedTermShiftTraversalRow M cutoff amount
      sourceCode sourceStep targetCode targetStep bound
      (rawTermAddCode M left right) (rawTermAddCode M left right)).
  {
    right. right. right. left.
    exists leftRootIndex, left, left,
      (raw_add M leftBound rightRootIndex), right, right.
    split.
    - exact (raw_lt_le_trans_pair M hPA leftRootIndex leftBound bound
        (proj1 (proj2 (proj2 hleft)))
        (raw_proof_left_le_sum M leftBound rightBound)).
    - split; [exact hleftRoot |].
      split; [exact hrightBelow |].
      split; [exact hrightRoot |]. split; reflexivity.
  }
  destruct (raw_termShiftTraversalBundle_append M hPA
    cutoff amount sourceCode sourceStep targetCode targetStep bound
    (rawTermAddCode M left right) (rawTermAddCode M left right)
    hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        hnewBundle & _ & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    (raw_succ M bound), bound.
  destruct hnewBundle as
    [hnewSource [hnewTarget [hnewRows hnewNonneg]]].
  exact (conj hnewSource
    (conj hnewTarget
      (conj (raw_assignment_lt_self_succ M hPA bound)
        (conj hnewRoot (conj hnewRows hnewNonneg))))).
Qed.

Lemma raw_codedTermShift_mul_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount left right,
  RawCodedTermShift M cutoff amount left left ->
  RawCodedTermShift M cutoff amount right right ->
  RawCodedTermShift M cutoff amount
    (rawTermMulCode M left right) (rawTermMulCode M left right).
Proof.
  intros M hPA cutoff amount left right
    (leftSourceCode & leftSourceStep & leftTargetCode & leftTargetStep &
     leftBound & leftRootIndex & hleft)
    (rightSourceCode & rightSourceStep & rightTargetCode & rightTargetStep &
     rightBound & rightRootIndex & hright).
  assert (hleftBelow : rawLt M leftRootIndex leftBound).
  { exact (proj1 (proj2 (proj2 hleft))). }
  destruct (raw_termShiftTraces_concatenate M hPA cutoff amount
    leftSourceCode leftSourceStep leftTargetCode leftTargetStep
    leftBound leftRootIndex left left
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightBound rightRootIndex right right hleft hright)
    as (sourceCode & sourceStep & targetCode & targetStep &
        hcombined & hleftRoot).
  destruct hcombined as
    [hsource [htarget [hrightBelow [hrightRoot [hrows hnonneg]]]]].
  set (bound := raw_add M leftBound rightBound).
  assert (hbundle : RawTermShiftTraversalBundle M cutoff amount
      sourceCode sourceStep targetCode targetStep bound).
  { exact (conj hsource (conj htarget (conj hrows hnonneg))). }
  assert (hrow : RawCodedTermShiftTraversalRow M cutoff amount
      sourceCode sourceStep targetCode targetStep bound
      (rawTermMulCode M left right) (rawTermMulCode M left right)).
  {
    right. right. right. right.
    exists leftRootIndex, left, left,
      (raw_add M leftBound rightRootIndex), right, right.
    split.
    - exact (raw_lt_le_trans_pair M hPA leftRootIndex leftBound bound
        hleftBelow (raw_proof_left_le_sum M leftBound rightBound)).
    - split; [exact hleftRoot |].
      split; [exact hrightBelow |].
      split; [exact hrightRoot |]. split; reflexivity.
  }
  destruct (raw_termShiftTraversalBundle_append M hPA
    cutoff amount sourceCode sourceStep targetCode targetStep bound
    (rawTermMulCode M left right) (rawTermMulCode M left right)
    hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        hnewBundle & _ & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    (raw_succ M bound), bound.
  destruct hnewBundle as
    [hnewSource [hnewTarget [hnewRows hnewNonneg]]].
  exact (conj hnewSource
    (conj hnewTarget
      (conj (raw_assignment_lt_self_succ M hPA bound)
        (conj hnewRoot (conj hnewRows hnewNonneg))))).
Qed.

(** ------------------------------------------------------------------
    A bound certificate makes every sufficiently high term shift the
    identity.  The invariant is a represented strong-prefix assertion over
    one fixed bound traversal, so child rows can be used at nonstandard
    indices. *)

Definition RawTermBoundShiftIdentityBelow (M : RawPAModel)
    (sourceCode sourceStep boundCode boundStep current : M) : Prop :=
  forall index input inputBound cutoff amount,
    rawLt M index current ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep boundCode boundStep index input inputBound ->
    rawLe M inputBound cutoff ->
    RawCodedTermShift M cutoff amount input input.

Arguments RawTermBoundShiftIdentityBelow M
  sourceCode sourceStep boundCode boundStep current : clear implicits.

Definition selfShiftAll5 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll body)))).

Definition termBoundShiftIdentityBelowTermAt
    (sourceCode sourceStep boundCode boundStep current : term) : formula :=
  selfShiftAll5
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 5 current))
      (pImp
        (codedTermOperationPairLookupTermAt
          (liftTerm 5 sourceCode) (liftTerm 5 sourceStep)
          (liftTerm 5 boundCode) (liftTerm 5 boundStep)
          (tVar 4) (tVar 3) (tVar 2))
        (pImp
          (Formula.leTermAt (tVar 2) (tVar 1))
          (codedTermShiftTermAt
            (tVar 1) (tVar 0) (tVar 3) (tVar 3))))).

Lemma raw_selfShift_eval_liftTerm_five : forall (M : RawPAModel)
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

Lemma raw_sat_termBoundShiftIdentityBelowTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep boundCode boundStep current,
  raw_formula_sat M e
    (termBoundShiftIdentityBelowTermAt
      sourceCode sourceStep boundCode boundStep current) <->
  RawTermBoundShiftIdentityBelow M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e boundCode) (raw_term_eval M e boundStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold termBoundShiftIdentityBelowTermAt, selfShiftAll5,
    RawTermBoundShiftIdentityBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_leTermAt_iff_rank.
  setoid_rewrite raw_sat_codedTermShiftTermAt_iff.
  repeat setoid_rewrite raw_selfShift_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawTermBoundShiftIdentityWithin (M : RawPAModel)
    (sourceCode sourceStep boundCode boundStep limit current : M) : Prop :=
  rawLe M current limit ->
  RawTermBoundShiftIdentityBelow M
    sourceCode sourceStep boundCode boundStep current.

Arguments RawTermBoundShiftIdentityWithin M
  sourceCode sourceStep boundCode boundStep limit current : clear implicits.

Definition termBoundShiftIdentityWithinTermAt
    (sourceCode sourceStep boundCode boundStep limit current : term)
    : formula :=
  pImp
    (Formula.leTermAt current limit)
    (termBoundShiftIdentityBelowTermAt
      sourceCode sourceStep boundCode boundStep current).

Lemma raw_sat_termBoundShiftIdentityWithinTermAt_iff : forall
    (M : RawPAModel) e
      sourceCode sourceStep boundCode boundStep limit current,
  raw_formula_sat M e
    (termBoundShiftIdentityWithinTermAt
      sourceCode sourceStep boundCode boundStep limit current) <->
  RawTermBoundShiftIdentityWithin M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e boundCode) (raw_term_eval M e boundStep)
    (raw_term_eval M e limit) (raw_term_eval M e current).
Proof.
  intros. unfold termBoundShiftIdentityWithinTermAt,
    RawTermBoundShiftIdentityWithin.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank,
    raw_sat_termBoundShiftIdentityBelowTermAt_iff.
  reflexivity.
Qed.

Lemma raw_termBoundShiftIdentityBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sourceCode sourceStep boundCode boundStep,
  RawTermBoundShiftIdentityBelow M
    sourceCode sourceStep boundCode boundStep (raw_zero M).
Proof.
  intros M hPA sourceCode sourceStep boundCode boundStep
    index input inputBound cutoff amount hindex _ _.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Lemma raw_termBoundShiftIdentityBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sourceCode sourceStep boundCode boundStep root limit current,
  RawCodedTermBoundTrace M
    sourceCode sourceStep boundCode boundStep root limit ->
  rawLt M current (raw_succ M root) ->
  RawTermBoundShiftIdentityBelow M
    sourceCode sourceStep boundCode boundStep current ->
  RawTermBoundShiftIdentityBelow M
    sourceCode sourceStep boundCode boundStep (raw_succ M current).
Proof.
  intros M hPA sourceCode sourceStep boundCode boundStep root limit current
    [_ [_ [_ hboundRows]]] hcurrent hprefix
    index input inputBound cutoff amount hindex hlookup hboundCutoff.
  destruct (raw_lt_succ_cases M hPA index current hindex)
    as [hindexOld | ->].
  - exact (hprefix index input inputBound cutoff amount
      hindexOld hlookup hboundCutoff).
  - pose proof (hboundRows current input inputBound hcurrent hlookup)
      as hrow.
    destruct hrow as
      [hvar | [hzero | [hsucc | [hadd | hmul]]]].
    + destruct hvar as
        (inputIndex & hinput & hboundEq).
      subst input. subst inputBound.
      apply raw_codedTermShift_variable_identity; [exact hPA |].
      apply (raw_rank_lt_of_succ_le M hPA inputIndex cutoff).
      exact hboundCutoff.
    + destruct hzero as [hinput hboundEq].
      subst input. subst inputBound.
      apply raw_codedTermShift_zero_identity. exact hPA.
    + destruct hsucc as
        (childIndex & inputChild & childBound & hchild & hchildLookup &
         hinput & hboundEq).
      subst input. subst inputBound.
      apply raw_codedTermShift_succ_identity; [exact hPA |].
      exact (hprefix childIndex inputChild childBound cutoff amount
        hchild hchildLookup hboundCutoff).
    + destruct hadd as
        (leftIndex & inputLeft & leftBound &
         rightIndex & inputRight & rightBound &
         hleft & hleftLookup & hright & hrightLookup & hinput & hboundEq).
      subst input. subst inputBound.
      apply raw_codedTermShift_add_identity; [exact hPA | |].
      * apply (hprefix leftIndex inputLeft leftBound cutoff amount
          hleft hleftLookup).
        exact (raw_le_trans M hPA leftBound
          (raw_add M leftBound rightBound) cutoff
          (raw_proof_left_le_sum M leftBound rightBound) hboundCutoff).
      * apply (hprefix rightIndex inputRight rightBound cutoff amount
          hright hrightLookup).
        exact (raw_le_trans M hPA rightBound
          (raw_add M leftBound rightBound) cutoff
          (raw_proof_right_le_sum M hPA leftBound rightBound) hboundCutoff).
    + destruct hmul as
        (leftIndex & inputLeft & leftBound &
         rightIndex & inputRight & rightBound &
         hleft & hleftLookup & hright & hrightLookup & hinput & hboundEq).
      subst input. subst inputBound.
      apply raw_codedTermShift_mul_identity; [exact hPA | |].
      * apply (hprefix leftIndex inputLeft leftBound cutoff amount
          hleft hleftLookup).
        exact (raw_le_trans M hPA leftBound
          (raw_add M leftBound rightBound) cutoff
          (raw_proof_left_le_sum M leftBound rightBound) hboundCutoff).
      * apply (hprefix rightIndex inputRight rightBound cutoff amount
          hright hrightLookup).
        exact (raw_le_trans M hPA rightBound
          (raw_add M leftBound rightBound) cutoff
          (raw_proof_right_le_sum M hPA leftBound rightBound) hboundCutoff).
Qed.

Theorem raw_termBoundShiftIdentityWithin_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sourceCode sourceStep boundCode boundStep root limit,
  RawCodedTermBoundTrace M
    sourceCode sourceStep boundCode boundStep root limit ->
  forall current,
  RawTermBoundShiftIdentityWithin M
    sourceCode sourceStep boundCode boundStep (raw_succ M root) current.
Proof.
  intros M hPA sourceCode sourceStep boundCode boundStep root limit htrace.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => sourceCode
    | 1 => sourceStep
    | 2 => boundCode
    | 3 => boundStep
    | _ => raw_succ M root
    end).
  set (phi := termBoundShiftIdentityWithinTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_termBoundShiftIdentityWithinTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons]. intros _.
      exact (raw_termBoundShiftIdentityBelow_zero M hPA
        sourceCode sourceStep boundCode boundStep).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_termBoundShiftIdentityWithinTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_termBoundShiftIdentityWithinTermAt_iff M
        (scons M (raw_succ M current) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      intro hsuccLe.
      assert (hcurrentBelow : rawLt M current (raw_succ M root)).
      { exact (raw_rank_lt_of_succ_le M hPA current
          (raw_succ M root) hsuccLe). }
      apply (raw_termBoundShiftIdentityBelow_succ M hPA
        sourceCode sourceStep boundCode boundStep root limit current
        htrace hcurrentBelow).
      apply hcurrent.
      exact (raw_lt_to_le M current (raw_succ M root) hcurrentBelow).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_termBoundShiftIdentityWithinTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))
    (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

Theorem raw_codedTermShift_identity_above_bound : forall
    (M : RawPAModel), RawPASatisfies M -> forall input inputBound,
  RawCodedTermBound M input inputBound ->
  forall cutoff amount,
  rawLe M inputBound cutoff ->
  RawCodedTermShift M cutoff amount input input.
Proof.
  intros M hPA input inputBound
    (sourceCode & sourceStep & boundCode & boundStep & htrace)
    cutoff amount hbound.
  destruct htrace as
    [hsourceDefined [hboundDefined [hrootLookup hrows]]].
  assert (htraceAgain : RawCodedTermBoundTrace M
      sourceCode sourceStep boundCode boundStep input inputBound).
  { exact (conj hsourceDefined
      (conj hboundDefined (conj hrootLookup hrows))). }
  pose proof (raw_termBoundShiftIdentityWithin_all M hPA
    sourceCode sourceStep boundCode boundStep input inputBound
    htraceAgain (raw_succ M input)) as hall.
  specialize (hall (raw_rank_le_refl M hPA (raw_succ M input))).
  exact (hall input input inputBound cutoff amount
    (raw_assignment_lt_self_succ M hPA input) hrootLookup hbound).
Qed.

(** ------------------------------------------------------------------
    Diagonal formula-shift traces.

    For an identity shift the source and target formula columns coincide.
    Keeping only that one formula column, together with the binder-depth
    column, cuts the concatenation construction from three beta tables to
    two without weakening the certificate eventually supplied to
    [RawCodedFormulaShift]. *)

Definition RawDiagonalFormulaShiftLookup (M : RawPAModel)
    (formulaCode formulaStep depthCode depthStep
      index input depth : M) : Prop :=
  RawCodedTermOperationPairLookup M
    formulaCode formulaStep depthCode depthStep index input depth.

Arguments RawDiagonalFormulaShiftLookup M
  formulaCode formulaStep depthCode depthStep index input depth
  : clear implicits.

Definition diagonalFormulaShiftLookupTermAt
    (formulaCode formulaStep depthCode depthStep
      index input depth : term) : formula :=
  codedTermOperationPairLookupTermAt
    formulaCode formulaStep depthCode depthStep index input depth.

Lemma raw_sat_diagonalFormulaShiftLookupTermAt_iff : forall
    (M : RawPAModel) e formulaCode formulaStep depthCode depthStep
      index input depth,
  raw_formula_sat M e
    (diagonalFormulaShiftLookupTermAt
      formulaCode formulaStep depthCode depthStep index input depth) <->
  RawDiagonalFormulaShiftLookup M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e depth).
Proof.
  intros. apply raw_sat_codedTermOperationPairLookupTermAt_iff.
Qed.

Definition RawDiagonalFormulaShiftTraversalRow (M : RawPAModel)
    (amount formulaCode formulaStep depthCode depthStep
      index input depth : M) : Prop :=
  RawCodedFormulaOperationTraversalRow M (RawCodedFormulaShiftAtom M)
    amount formulaCode formulaStep formulaCode formulaStep
    depthCode depthStep index input input depth.

Arguments RawDiagonalFormulaShiftTraversalRow M amount
  formulaCode formulaStep depthCode depthStep index input depth
  : clear implicits.

Definition diagonalFormulaShiftTraversalRowTermAt
    (amount formulaCode formulaStep depthCode depthStep
      index input depth : term) : formula :=
  codedFormulaOperationTraversalRowTermAt codedFormulaShiftAtomTermAt
    amount formulaCode formulaStep formulaCode formulaStep
    depthCode depthStep index input input depth.

Lemma raw_sat_diagonalFormulaShiftTraversalRowTermAt_iff : forall
    (M : RawPAModel) e amount formulaCode formulaStep depthCode depthStep
      index input depth,
  raw_formula_sat M e
    (diagonalFormulaShiftTraversalRowTermAt amount
      formulaCode formulaStep depthCode depthStep index input depth) <->
  RawDiagonalFormulaShiftTraversalRow M
    (raw_term_eval M e amount)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e depth).
Proof.
  intros. unfold diagonalFormulaShiftTraversalRowTermAt,
    RawDiagonalFormulaShiftTraversalRow.
  apply (raw_sat_codedFormulaOperationTraversalRowTermAt_iff M e
    codedFormulaShiftAtomTermAt (RawCodedFormulaShiftAtom M)).
  exact (raw_sat_codedFormulaShiftAtomTermAt_iff M).
Qed.

Lemma raw_diagonalFormulaShiftLookup_prefix_extend : forall
    (M : RawPAModel) bound
      oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
      newFormulaCode newFormulaStep newDepthCode newDepthStep
      index input depth,
  RawTermShiftTablePrefixExtension M bound
    oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    newFormulaCode newFormulaStep newDepthCode newDepthStep ->
  rawLt M index bound ->
  RawDiagonalFormulaShiftLookup M
    oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    index input depth ->
  RawDiagonalFormulaShiftLookup M
    newFormulaCode newFormulaStep newDepthCode newDepthStep
    index input depth.
Proof.
  exact raw_termShiftPairLookup_prefix_extend.
Qed.

Lemma raw_diagonalFormulaShiftTriple_prefix_extend : forall
    (M : RawPAModel) bound
      oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
      newFormulaCode newFormulaStep newDepthCode newDepthStep
      index input output depth,
  RawTermShiftTablePrefixExtension M bound
    oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    newFormulaCode newFormulaStep newDepthCode newDepthStep ->
  rawLt M index bound ->
  RawCodedFormulaOperationTripleLookup M
    oldFormulaCode oldFormulaStep oldFormulaCode oldFormulaStep
    oldDepthCode oldDepthStep index input output depth ->
  RawCodedFormulaOperationTripleLookup M
    newFormulaCode newFormulaStep newFormulaCode newFormulaStep
    newDepthCode newDepthStep index input output depth.
Proof.
  intros M bound oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    newFormulaCode newFormulaStep newDepthCode newDepthStep
    index input output depth [hformula hdepth] hindex
    [hinput [houtput hdepthLookup]].
  repeat split.
  - exact (hformula index input hindex hinput).
  - exact (hformula index output hindex houtput).
  - exact (hdepth index depth hindex hdepthLookup).
Qed.

Lemma raw_diagonalFormulaShiftTraversalRow_prefix_extend : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount bound current
      oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
      newFormulaCode newFormulaStep newDepthCode newDepthStep input depth,
  RawTermShiftTablePrefixExtension M bound
    oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    newFormulaCode newFormulaStep newDepthCode newDepthStep ->
  rawLe M current bound ->
  RawDiagonalFormulaShiftTraversalRow M amount
    oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    current input depth ->
  RawDiagonalFormulaShiftTraversalRow M amount
    newFormulaCode newFormulaStep newDepthCode newDepthStep
    current input depth.
Proof.
  intros M hPA amount bound current
    oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
    newFormulaCode newFormulaStep newDepthCode newDepthStep
    input depth hext hcurrent hrow.
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
    exists leftIndex, inputLeft, outputLeft, leftDepth,
      rightIndex, inputRight, outputRight, rightDepth.
    split; [exact hleft |]. split.
    + apply (raw_diagonalFormulaShiftTriple_prefix_extend M bound
        oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        leftIndex inputLeft outputLeft leftDepth hext).
      * exact (raw_lt_le_trans_pair M hPA
          leftIndex current bound hleft hcurrent).
      * exact hleftLookup.
    + split; [exact hleftDepth |]. split; [exact hright |]. split.
      * apply (raw_diagonalFormulaShiftTriple_prefix_extend M bound
          oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
          newFormulaCode newFormulaStep newDepthCode newDepthStep
          rightIndex inputRight outputRight rightDepth hext).
        -- exact (raw_lt_le_trans_pair M hPA
             rightIndex current bound hright hcurrent).
        -- exact hrightLookup.
      * repeat split; assumption.
  - right. right. right. left.
    destruct hand as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleft & hleftLookup & hleftDepth & hright & hrightLookup &
       hrightDepth & hinput & houtput).
    exists leftIndex, inputLeft, outputLeft, leftDepth,
      rightIndex, inputRight, outputRight, rightDepth.
    split; [exact hleft |]. split.
    + apply (raw_diagonalFormulaShiftTriple_prefix_extend M bound
        oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        leftIndex inputLeft outputLeft leftDepth hext).
      * exact (raw_lt_le_trans_pair M hPA
          leftIndex current bound hleft hcurrent).
      * exact hleftLookup.
    + split; [exact hleftDepth |]. split; [exact hright |]. split.
      * apply (raw_diagonalFormulaShiftTriple_prefix_extend M bound
          oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
          newFormulaCode newFormulaStep newDepthCode newDepthStep
          rightIndex inputRight outputRight rightDepth hext).
        -- exact (raw_lt_le_trans_pair M hPA
             rightIndex current bound hright hcurrent).
        -- exact hrightLookup.
      * repeat split; assumption.
  - right. right. right. right. left.
    destruct hor as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleft & hleftLookup & hleftDepth & hright & hrightLookup &
       hrightDepth & hinput & houtput).
    exists leftIndex, inputLeft, outputLeft, leftDepth,
      rightIndex, inputRight, outputRight, rightDepth.
    split; [exact hleft |]. split.
    + apply (raw_diagonalFormulaShiftTriple_prefix_extend M bound
        oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        leftIndex inputLeft outputLeft leftDepth hext).
      * exact (raw_lt_le_trans_pair M hPA
          leftIndex current bound hleft hcurrent).
      * exact hleftLookup.
    + split; [exact hleftDepth |]. split; [exact hright |]. split.
      * apply (raw_diagonalFormulaShiftTriple_prefix_extend M bound
          oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
          newFormulaCode newFormulaStep newDepthCode newDepthStep
          rightIndex inputRight outputRight rightDepth hext).
        -- exact (raw_lt_le_trans_pair M hPA
             rightIndex current bound hright hcurrent).
        -- exact hrightLookup.
      * repeat split; assumption.
  - right. right. right. right. right. left.
    destruct hall as
      (childIndex & inputChild & outputChild & childDepth &
       hchild & hchildLookup & hchildDepth & hinput & houtput).
    exists childIndex, inputChild, outputChild, childDepth.
    split; [exact hchild |]. split.
    + apply (raw_diagonalFormulaShiftTriple_prefix_extend M bound
        oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        childIndex inputChild outputChild childDepth hext).
      * exact (raw_lt_le_trans_pair M hPA
          childIndex current bound hchild hcurrent).
      * exact hchildLookup.
    + repeat split; assumption.
  - right. right. right. right. right. right.
    destruct hex as
      (childIndex & inputChild & outputChild & childDepth &
       hchild & hchildLookup & hchildDepth & hinput & houtput).
    exists childIndex, inputChild, outputChild, childDepth.
    split; [exact hchild |]. split.
    + apply (raw_diagonalFormulaShiftTriple_prefix_extend M bound
        oldFormulaCode oldFormulaStep oldDepthCode oldDepthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        childIndex inputChild outputChild childDepth hext).
      * exact (raw_lt_le_trans_pair M hPA
          childIndex current bound hchild hcurrent).
      * exact hchildLookup.
    + repeat split; assumption.
Qed.

Definition RawDiagonalFormulaShiftRows (M : RawPAModel)
    (amount formulaCode formulaStep depthCode depthStep bound : M) : Prop :=
  forall index input depth,
    rawLt M index bound ->
    RawDiagonalFormulaShiftLookup M
      formulaCode formulaStep depthCode depthStep index input depth ->
    RawDiagonalFormulaShiftTraversalRow M amount
      formulaCode formulaStep depthCode depthStep index input depth.

Arguments RawDiagonalFormulaShiftRows M amount
  formulaCode formulaStep depthCode depthStep bound : clear implicits.

Definition diagonalFormulaShiftRowsTermAt
    (amount formulaCode formulaStep depthCode depthStep bound : term)
    : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 bound))
      (pImp
        (diagonalFormulaShiftLookupTermAt
          (liftTerm 3 formulaCode) (liftTerm 3 formulaStep)
          (liftTerm 3 depthCode) (liftTerm 3 depthStep)
          (tVar 2) (tVar 1) (tVar 0))
        (diagonalFormulaShiftTraversalRowTermAt
          (liftTerm 3 amount)
          (liftTerm 3 formulaCode) (liftTerm 3 formulaStep)
          (liftTerm 3 depthCode) (liftTerm 3 depthStep)
          (tVar 2) (tVar 1) (tVar 0)))))).

Lemma raw_sat_diagonalFormulaShiftRowsTermAt_iff : forall
    (M : RawPAModel) e amount formulaCode formulaStep depthCode depthStep
      bound,
  raw_formula_sat M e
    (diagonalFormulaShiftRowsTermAt amount
      formulaCode formulaStep depthCode depthStep bound) <->
  RawDiagonalFormulaShiftRows M
    (raw_term_eval M e amount)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e bound).
Proof.
  intros. unfold diagonalFormulaShiftRowsTermAt,
    RawDiagonalFormulaShiftRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_diagonalFormulaShiftLookupTermAt_iff.
  setoid_rewrite raw_sat_diagonalFormulaShiftTraversalRowTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawDiagonalFormulaShiftBundle (M : RawPAModel)
    (amount formulaCode formulaStep depthCode depthStep bound : M) : Prop :=
  RawCodedAssignmentDefinedThrough M formulaCode formulaStep bound /\
  RawCodedAssignmentDefinedThrough M depthCode depthStep bound /\
  RawDiagonalFormulaShiftRows M amount
    formulaCode formulaStep depthCode depthStep bound.

Arguments RawDiagonalFormulaShiftBundle M amount
  formulaCode formulaStep depthCode depthStep bound : clear implicits.

Definition diagonalFormulaShiftBundleTermAt
    (amount formulaCode formulaStep depthCode depthStep bound : term)
    : formula :=
  operationAnd3
    (codedAssignmentDefinedThroughTermAt formulaCode formulaStep bound)
    (codedAssignmentDefinedThroughTermAt depthCode depthStep bound)
    (diagonalFormulaShiftRowsTermAt amount
      formulaCode formulaStep depthCode depthStep bound).

Lemma raw_sat_diagonalFormulaShiftBundleTermAt_iff : forall
    (M : RawPAModel) e amount formulaCode formulaStep depthCode depthStep
      bound,
  raw_formula_sat M e
    (diagonalFormulaShiftBundleTermAt amount
      formulaCode formulaStep depthCode depthStep bound) <->
  RawDiagonalFormulaShiftBundle M
    (raw_term_eval M e amount)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e bound).
Proof.
  intros. unfold diagonalFormulaShiftBundleTermAt,
    RawDiagonalFormulaShiftBundle, operationAnd3.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff,
    raw_sat_diagonalFormulaShiftRowsTermAt_iff.
  reflexivity.
Qed.

Theorem raw_diagonalFormulaShiftBundle_append : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      amount formulaCode formulaStep depthCode depthStep bound input depth,
  RawDiagonalFormulaShiftBundle M amount
    formulaCode formulaStep depthCode depthStep bound ->
  RawDiagonalFormulaShiftTraversalRow M amount
    formulaCode formulaStep depthCode depthStep bound input depth ->
  exists newFormulaCode newFormulaStep newDepthCode newDepthStep : M,
    RawDiagonalFormulaShiftBundle M amount
      newFormulaCode newFormulaStep newDepthCode newDepthStep
      (raw_succ M bound) /\
    RawTermShiftTablePrefixExtension M bound
      formulaCode formulaStep depthCode depthStep
      newFormulaCode newFormulaStep newDepthCode newDepthStep /\
    RawDiagonalFormulaShiftLookup M
      newFormulaCode newFormulaStep newDepthCode newDepthStep
      bound input depth.
Proof.
  intros M hPA amount formulaCode formulaStep depthCode depthStep
    bound input depth [hformulaDefined [hdepthDefined hrows]] hclosed.
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    formulaCode formulaStep bound input hformulaDefined)
    as [newFormulaCode [newFormulaStep
      [hnewFormulaDefined [hformulaPrefix hformulaRoot]]]].
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    depthCode depthStep bound depth hdepthDefined)
    as [newDepthCode [newDepthStep
      [hnewDepthDefined [hdepthPrefix hdepthRoot]]]].
  set (hext := conj hformulaPrefix hdepthPrefix).
  exists newFormulaCode, newFormulaStep, newDepthCode, newDepthStep.
  split.
  - split; [exact hnewFormulaDefined |].
    split; [exact hnewDepthDefined |].
    intros index rowInput rowDepth hindex hlookup.
    destruct (raw_lt_succ_cases M hPA index bound hindex)
      as [hindexOld | ->].
    + destruct (hformulaDefined index hindexOld)
        as [oldInput holdInput].
      destruct (hdepthDefined index hindexOld)
        as [oldDepth holdDepth].
      assert (hnewOld : RawDiagonalFormulaShiftLookup M
          newFormulaCode newFormulaStep newDepthCode newDepthStep
          index oldInput oldDepth).
      {
        apply (raw_diagonalFormulaShiftLookup_prefix_extend M bound
          formulaCode formulaStep depthCode depthStep
          newFormulaCode newFormulaStep newDepthCode newDepthStep
          index oldInput oldDepth hext hindexOld).
        split; assumption.
      }
      destruct hlookup as [hlookupInput hlookupDepth].
      destruct hnewOld as [hnewOldInput hnewOldDepth].
      assert (hinputEq : rowInput = oldInput).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newFormulaCode newFormulaStep index rowInput oldInput
          hlookupInput hnewOldInput).
      }
      assert (hdepthEq : rowDepth = oldDepth).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newDepthCode newDepthStep index rowDepth oldDepth
          hlookupDepth hnewOldDepth).
      }
      subst rowInput. subst rowDepth.
      apply (raw_diagonalFormulaShiftTraversalRow_prefix_extend M hPA
        amount bound index
        formulaCode formulaStep depthCode depthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        oldInput oldDepth hext).
      * exact (raw_lt_to_le M index bound hindexOld).
      * apply (hrows index oldInput oldDepth hindexOld).
        split; assumption.
    + destruct hlookup as [hlookupInput hlookupDepth].
      assert (hinputEq : rowInput = input).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newFormulaCode newFormulaStep bound rowInput input
          hlookupInput hformulaRoot).
      }
      assert (hdepthEq : rowDepth = depth).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newDepthCode newDepthStep bound rowDepth depth
          hlookupDepth hdepthRoot).
      }
      subst rowInput. subst rowDepth.
      apply (raw_diagonalFormulaShiftTraversalRow_prefix_extend M hPA
        amount bound bound
        formulaCode formulaStep depthCode depthStep
        newFormulaCode newFormulaStep newDepthCode newDepthStep
        input depth hext).
      * apply raw_rank_le_refl. exact hPA.
      * exact hclosed.
  - split; [exact hext |]. split; assumption.
Qed.

(** A diagonal trace is already a full formula-operation trace once its
    single formula lookup is used for both the source and target columns. *)
Definition RawDiagonalFormulaShiftTrace (M : RawPAModel)
    (amount rootDepth formulaCode formulaStep depthCode depthStep
      bound rootIndex input : M) : Prop :=
  RawDiagonalFormulaShiftBundle M amount
    formulaCode formulaStep depthCode depthStep bound /\
  rawLt M rootIndex bound /\
  RawDiagonalFormulaShiftLookup M
    formulaCode formulaStep depthCode depthStep
    rootIndex input rootDepth.

Arguments RawDiagonalFormulaShiftTrace M amount rootDepth
  formulaCode formulaStep depthCode depthStep bound rootIndex input
  : clear implicits.

Lemma raw_codedFormulaShift_of_diagonal_trace : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount rootDepth
      formulaCode formulaStep depthCode depthStep bound rootIndex input,
  RawDiagonalFormulaShiftTrace M amount rootDepth
    formulaCode formulaStep depthCode depthStep bound rootIndex input ->
  RawCodedFormulaShift M rootDepth amount input input.
Proof.
  intros M hPA amount rootDepth formulaCode formulaStep depthCode depthStep
    bound rootIndex input
    [[hformulaDefined [hdepthDefined hrows]] [hrootBelow hroot]].
  exists formulaCode, formulaStep, formulaCode, formulaStep,
    depthCode, depthStep, bound, rootIndex.
  split; [exact hformulaDefined |].
  split; [exact hformulaDefined |].
  split; [exact hdepthDefined |].
  split; [exact hrootBelow |]. split.
  - destruct hroot as [hformula hdepth].
    split; [exact hformula |]. split; assumption.
  - intros index rowInput rowOutput rowDepth hindex
      [hinput [houtput hdepth]].
    assert (houtputEq : rowOutput = rowInput).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        formulaCode formulaStep index rowOutput rowInput houtput hinput).
    }
    subst rowOutput.
    exact (hrows index rowInput rowDepth hindex (conj hinput hdepth)).
Qed.

(** ------------------------------------------------------------------
    Copying and concatenating possibly nonstandard diagonal traces. *)

Definition RawDiagonalFormulaShiftOffsetEmbedding (M : RawPAModel)
    (offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep : M)
    : Prop :=
  RawTermShiftPairOffsetEmbedding M offset current
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep.

Arguments RawDiagonalFormulaShiftOffsetEmbedding M offset current
  sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
  targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
  : clear implicits.

Definition diagonalFormulaShiftOffsetEmbeddingTermAt
    (offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
      : term) : formula :=
  termShiftPairOffsetEmbeddingTermAt offset current
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep.

Lemma raw_sat_diagonalFormulaShiftOffsetEmbeddingTermAt_iff : forall
    (M : RawPAModel) e offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep,
  raw_formula_sat M e
    (diagonalFormulaShiftOffsetEmbeddingTermAt offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep)
  <->
  RawDiagonalFormulaShiftOffsetEmbedding M
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

Lemma raw_diagonalFormulaShiftTriple_offset : forall
    (M : RawPAModel) offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
      index input output depth,
  RawDiagonalFormulaShiftOffsetEmbedding M offset current
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

Lemma raw_diagonalFormulaShiftTraversalRow_offset : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
      input depth,
  RawDiagonalFormulaShiftOffsetEmbedding M offset current
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep ->
  RawDiagonalFormulaShiftTraversalRow M amount
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    current input depth ->
  RawDiagonalFormulaShiftTraversalRow M amount
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
    (raw_add M offset current) input depth.
Proof.
  intros M hPA amount offset current
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
      * exact (raw_diagonalFormulaShiftTriple_offset M offset current
          sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
          targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
          leftIndex inputLeft outputLeft leftDepth hembed hleft hleftLookup).
      * split; [exact hleftDepth |]. split.
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             rightIndex current hright).
        -- split.
           ++ exact (raw_diagonalFormulaShiftTriple_offset M offset current
                sourceFormulaCode sourceFormulaStep
                sourceDepthCode sourceDepthStep
                targetFormulaCode targetFormulaStep
                targetDepthCode targetDepthStep
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
      * exact (raw_diagonalFormulaShiftTriple_offset M offset current
          sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
          targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
          leftIndex inputLeft outputLeft leftDepth hembed hleft hleftLookup).
      * split; [exact hleftDepth |]. split.
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             rightIndex current hright).
        -- split.
           ++ exact (raw_diagonalFormulaShiftTriple_offset M offset current
                sourceFormulaCode sourceFormulaStep
                sourceDepthCode sourceDepthStep
                targetFormulaCode targetFormulaStep
                targetDepthCode targetDepthStep
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
      * exact (raw_diagonalFormulaShiftTriple_offset M offset current
          sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
          targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
          leftIndex inputLeft outputLeft leftDepth hembed hleft hleftLookup).
      * split; [exact hleftDepth |]. split.
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             rightIndex current hright).
        -- split.
           ++ exact (raw_diagonalFormulaShiftTriple_offset M offset current
                sourceFormulaCode sourceFormulaStep
                sourceDepthCode sourceDepthStep
                targetFormulaCode targetFormulaStep
                targetDepthCode targetDepthStep
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
      * exact (raw_diagonalFormulaShiftTriple_offset M offset current
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
      * exact (raw_diagonalFormulaShiftTriple_offset M offset current
          sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
          targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
          childIndex inputChild outputChild childDepth
          hembed hchild hchildLookup).
      * repeat split; assumption.
Qed.

Definition RawDiagonalFormulaShiftCopyState (M : RawPAModel)
    (amount
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound offset initialRootIndex initialInput initialDepth current : M)
    : Prop :=
  rawLe M current sourceBound ->
  exists targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep,
    RawDiagonalFormulaShiftBundle M amount
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
      (raw_add M offset current) /\
    RawDiagonalFormulaShiftLookup M
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
      initialRootIndex initialInput initialDepth /\
    RawDiagonalFormulaShiftOffsetEmbedding M offset current
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep.

Arguments RawDiagonalFormulaShiftCopyState M amount
  sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
  sourceBound offset initialRootIndex initialInput initialDepth current
  : clear implicits.

Definition diagonalFormulaShiftCopyStateTermAt
    (amount
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound offset initialRootIndex initialInput initialDepth current
      : term) : formula :=
  pImp
    (Formula.leTermAt current sourceBound)
    (operationEx4
      (operationAnd3
        (diagonalFormulaShiftBundleTermAt
          (liftTerm 4 amount)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)
          (tAdd (liftTerm 4 offset) (liftTerm 4 current)))
        (diagonalFormulaShiftLookupTermAt
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)
          (liftTerm 4 initialRootIndex)
          (liftTerm 4 initialInput) (liftTerm 4 initialDepth))
        (diagonalFormulaShiftOffsetEmbeddingTermAt
          (liftTerm 4 offset) (liftTerm 4 current)
          (liftTerm 4 sourceFormulaCode) (liftTerm 4 sourceFormulaStep)
          (liftTerm 4 sourceDepthCode) (liftTerm 4 sourceDepthStep)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)))).

Lemma raw_sat_diagonalFormulaShiftCopyStateTermAt_iff : forall
    (M : RawPAModel) e amount
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound offset initialRootIndex initialInput initialDepth current,
  raw_formula_sat M e
    (diagonalFormulaShiftCopyStateTermAt amount
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound offset initialRootIndex initialInput initialDepth current)
  <->
  RawDiagonalFormulaShiftCopyState M
    (raw_term_eval M e amount)
    (raw_term_eval M e sourceFormulaCode)
    (raw_term_eval M e sourceFormulaStep)
    (raw_term_eval M e sourceDepthCode)
    (raw_term_eval M e sourceDepthStep)
    (raw_term_eval M e sourceBound) (raw_term_eval M e offset)
    (raw_term_eval M e initialRootIndex)
    (raw_term_eval M e initialInput) (raw_term_eval M e initialDepth)
    (raw_term_eval M e current).
Proof.
  intros. unfold diagonalFormulaShiftCopyStateTermAt, operationEx4,
    operationAnd3, RawDiagonalFormulaShiftCopyState.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank.
  setoid_rewrite raw_sat_diagonalFormulaShiftBundleTermAt_iff.
  setoid_rewrite raw_sat_diagonalFormulaShiftLookupTermAt_iff.
  setoid_rewrite raw_sat_diagonalFormulaShiftOffsetEmbeddingTermAt_iff.
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

Lemma raw_diagonalFormulaShiftOffsetEmbedding_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall offset
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep,
  RawDiagonalFormulaShiftOffsetEmbedding M offset (raw_zero M)
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

Lemma raw_diagonalFormulaShiftCopyState_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      amount
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound offset
      initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
      initialRootIndex initialInput initialDepth,
  RawDiagonalFormulaShiftBundle M amount
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
    offset ->
  RawDiagonalFormulaShiftLookup M
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
    initialRootIndex initialInput initialDepth ->
  RawDiagonalFormulaShiftCopyState M amount
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound offset initialRootIndex initialInput initialDepth
    (raw_zero M).
Proof.
  intros M hPA amount
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound offset
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
    initialRootIndex initialInput initialDepth
    hinitialBundle hinitialRoot _.
  exists initialFormulaCode, initialFormulaStep,
    initialDepthCode, initialDepthStep.
  rewrite raw_assignmentTotality_add_zero_right by exact hPA.
  split; [exact hinitialBundle |]. split; [exact hinitialRoot |].
  exact (raw_diagonalFormulaShiftOffsetEmbedding_zero M hPA offset
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep).
Qed.

Lemma raw_diagonalFormulaShiftCopyState_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      amount
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound sourceRootIndex sourceInput sourceRootDepth
      offset initialRootIndex initialInput initialDepth current,
  RawDiagonalFormulaShiftTrace M amount sourceRootDepth
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound sourceRootIndex sourceInput ->
  rawLt M initialRootIndex offset ->
  RawDiagonalFormulaShiftCopyState M amount
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound offset initialRootIndex initialInput initialDepth current ->
  RawDiagonalFormulaShiftCopyState M amount
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound offset initialRootIndex initialInput initialDepth
    (raw_succ M current).
Proof.
  intros M hPA amount
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
  assert (hsourceLookup : RawDiagonalFormulaShiftLookup M
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      current rowInput rowDepth).
  { split; assumption. }
  pose proof (hsourceRows current rowInput rowDepth
    hcurrentBelow hsourceLookup) as hsourceRow.
  pose proof (raw_diagonalFormulaShiftTraversalRow_offset M hPA
    amount offset current
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
    rowInput rowDepth hembed hsourceRow) as htargetRow.
  destruct (raw_diagonalFormulaShiftBundle_append M hPA
    amount targetFormulaCode targetFormulaStep targetDepthCode targetDepthStep
    (raw_add M offset current) rowInput rowDepth
    htargetBundle htargetRow)
    as (newFormulaCode & newFormulaStep & newDepthCode & newDepthStep &
        hnewBundle & hprefix & hnewRoot).
  exists newFormulaCode, newFormulaStep, newDepthCode, newDepthStep.
  split.
  - rewrite raw_add_succ by exact hPA. exact hnewBundle.
  - split.
    + apply (raw_diagonalFormulaShiftLookup_prefix_extend M
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
      * apply (raw_diagonalFormulaShiftLookup_prefix_extend M
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

Theorem raw_diagonalFormulaShiftCopyState_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      amount
      sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
      sourceBound sourceRootIndex sourceInput sourceRootDepth
      offset
      initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
      initialRootIndex initialInput initialDepth,
  RawDiagonalFormulaShiftTrace M amount sourceRootDepth
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound sourceRootIndex sourceInput ->
  RawDiagonalFormulaShiftBundle M amount
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
    offset ->
  rawLt M initialRootIndex offset ->
  RawDiagonalFormulaShiftLookup M
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
    initialRootIndex initialInput initialDepth ->
  forall current,
  RawDiagonalFormulaShiftCopyState M amount
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound offset initialRootIndex initialInput initialDepth current.
Proof.
  intros M hPA amount
    sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
    sourceBound sourceRootIndex sourceInput sourceRootDepth
    offset
    initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
    initialRootIndex initialInput initialDepth
    hsource hinitialBundle hinitialBelow hinitialRoot.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => amount
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
  set (phi := diagonalFormulaShiftCopyStateTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
    (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_diagonalFormulaShiftCopyStateTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
        (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_diagonalFormulaShiftCopyState_zero M hPA amount
        sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
        sourceBound offset
        initialFormulaCode initialFormulaStep initialDepthCode initialDepthStep
        initialRootIndex initialInput initialDepth
        hinitialBundle hinitialRoot).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_diagonalFormulaShiftCopyStateTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_diagonalFormulaShiftCopyStateTermAt_iff M
        (scons M (raw_succ M current) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
        (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_diagonalFormulaShiftCopyState_succ M hPA amount
        sourceFormulaCode sourceFormulaStep sourceDepthCode sourceDepthStep
        sourceBound sourceRootIndex sourceInput sourceRootDepth
        offset initialRootIndex initialInput initialDepth current
        hsource hinitialBelow hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_diagonalFormulaShiftCopyStateTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
      (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 0))
    (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

Theorem raw_diagonalFormulaShiftTraces_concatenate : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount rootDepth
      firstFormulaCode firstFormulaStep firstDepthCode firstDepthStep
      firstBound firstRootIndex firstInput
      secondFormulaCode secondFormulaStep secondDepthCode secondDepthStep
      secondBound secondRootIndex secondInput,
  RawDiagonalFormulaShiftTrace M amount rootDepth
    firstFormulaCode firstFormulaStep firstDepthCode firstDepthStep
    firstBound firstRootIndex firstInput ->
  RawDiagonalFormulaShiftTrace M amount rootDepth
    secondFormulaCode secondFormulaStep secondDepthCode secondDepthStep
    secondBound secondRootIndex secondInput ->
  exists newFormulaCode newFormulaStep newDepthCode newDepthStep : M,
    RawDiagonalFormulaShiftTrace M amount rootDepth
      newFormulaCode newFormulaStep newDepthCode newDepthStep
      (raw_add M firstBound secondBound)
      (raw_add M firstBound secondRootIndex) secondInput /\
    RawDiagonalFormulaShiftLookup M
      newFormulaCode newFormulaStep newDepthCode newDepthStep
      firstRootIndex firstInput rootDepth.
Proof.
  intros M hPA amount rootDepth
    firstFormulaCode firstFormulaStep firstDepthCode firstDepthStep
    firstBound firstRootIndex firstInput
    secondFormulaCode secondFormulaStep secondDepthCode secondDepthStep
    secondBound secondRootIndex secondInput hfirst hsecond.
  destruct hfirst as [hfirstBundle [hfirstBelow hfirstRoot]].
  pose proof (raw_diagonalFormulaShiftCopyState_all M hPA amount
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

(** The existential diagonal relation is represented explicitly because it
    is the induction invariant used below for nonstandard formula codes. *)
Definition diagonalFormulaShiftTraceTermAt
    (amount rootDepth formulaCode formulaStep depthCode depthStep
      bound rootIndex input : term) : formula :=
  operationAnd3
    (diagonalFormulaShiftBundleTermAt amount
      formulaCode formulaStep depthCode depthStep bound)
    (Formula.ltTermAt rootIndex bound)
    (diagonalFormulaShiftLookupTermAt
      formulaCode formulaStep depthCode depthStep
      rootIndex input rootDepth).

Lemma raw_sat_diagonalFormulaShiftTraceTermAt_iff : forall
    (M : RawPAModel) e amount rootDepth
      formulaCode formulaStep depthCode depthStep bound rootIndex input,
  raw_formula_sat M e
    (diagonalFormulaShiftTraceTermAt amount rootDepth
      formulaCode formulaStep depthCode depthStep bound rootIndex input) <->
  RawDiagonalFormulaShiftTrace M
    (raw_term_eval M e amount) (raw_term_eval M e rootDepth)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e bound) (raw_term_eval M e rootIndex)
    (raw_term_eval M e input).
Proof.
  intros. unfold diagonalFormulaShiftTraceTermAt,
    RawDiagonalFormulaShiftTrace, operationAnd3.
  cbn [raw_formula_sat].
  rewrite raw_sat_diagonalFormulaShiftBundleTermAt_iff,
    raw_sat_ltTermAt_iff,
    raw_sat_diagonalFormulaShiftLookupTermAt_iff.
  reflexivity.
Qed.

Definition RawCodedFormulaDiagonalShift (M : RawPAModel)
    (cutoff amount input : M) : Prop :=
  exists formulaCode formulaStep depthCode depthStep bound rootIndex : M,
    RawDiagonalFormulaShiftTrace M amount cutoff
      formulaCode formulaStep depthCode depthStep bound rootIndex input.

Arguments RawCodedFormulaDiagonalShift M cutoff amount input
  : clear implicits.

Definition codedFormulaDiagonalShiftTermAt
    (cutoff amount input : term) : formula :=
  operationEx6
    (diagonalFormulaShiftTraceTermAt
      (liftTerm 6 amount) (liftTerm 6 cutoff)
      (tVar 5) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0)
      (liftTerm 6 input)).

Lemma raw_sat_codedFormulaDiagonalShiftTermAt_iff : forall
    (M : RawPAModel) e cutoff amount input,
  raw_formula_sat M e
    (codedFormulaDiagonalShiftTermAt cutoff amount input) <->
  RawCodedFormulaDiagonalShift M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e input).
Proof.
  intros. unfold codedFormulaDiagonalShiftTermAt, operationEx6,
    RawCodedFormulaDiagonalShift.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_diagonalFormulaShiftTraceTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_six.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedFormulaShift_of_diagonal : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount input,
  RawCodedFormulaDiagonalShift M cutoff amount input ->
  RawCodedFormulaShift M cutoff amount input input.
Proof.
  intros M hPA cutoff amount input
    (formulaCode & formulaStep & depthCode & depthStep &
     bound & rootIndex & htrace).
  exact (raw_codedFormulaShift_of_diagonal_trace M hPA amount cutoff
    formulaCode formulaStep depthCode depthStep bound rootIndex input htrace).
Qed.

Lemma raw_diagonalFormulaShiftBundle_empty : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount,
  RawDiagonalFormulaShiftBundle M amount
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M).
Proof.
  intros M hPA amount.
  split.
  - exact (raw_codedZeroAssignment_defined_all M hPA (raw_zero M)).
  - split.
    + exact (raw_codedZeroAssignment_defined_all M hPA (raw_zero M)).
    + intros index input depth hindex _.
      exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Lemma raw_diagonalLookup_to_triple : forall
    (M : RawPAModel) formulaCode formulaStep depthCode depthStep
      index input depth,
  RawDiagonalFormulaShiftLookup M
    formulaCode formulaStep depthCode depthStep index input depth ->
  RawCodedFormulaOperationTripleLookup M
    formulaCode formulaStep formulaCode formulaStep depthCode depthStep
    index input input depth.
Proof.
  intros M formulaCode formulaStep depthCode depthStep
    index input depth [hinput hdepth].
  split; [exact hinput |]. split; assumption.
Qed.

Lemma raw_codedFormulaDiagonalShift_eq_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount depth
      left right leftBound rightBound,
  RawCodedTermBound M left leftBound ->
  RawCodedTermBound M right rightBound ->
  rawLe M (raw_add M leftBound rightBound) depth ->
  RawCodedFormulaDiagonalShift M depth amount
    (rawFormulaEqCode M left right).
Proof.
  intros M hPA amount depth left right leftBound rightBound
    hleftBound hrightBound hsumBound.
  assert (hleftShift : RawCodedTermShift M depth amount left left).
  {
    apply (raw_codedTermShift_identity_above_bound M hPA
      left leftBound hleftBound depth amount).
    exact (raw_le_trans M hPA leftBound
      (raw_add M leftBound rightBound) depth
      (raw_proof_left_le_sum M leftBound rightBound) hsumBound).
  }
  assert (hrightShift : RawCodedTermShift M depth amount right right).
  {
    apply (raw_codedTermShift_identity_above_bound M hPA
      right rightBound hrightBound depth amount).
    exact (raw_le_trans M hPA rightBound
      (raw_add M leftBound rightBound) depth
      (raw_proof_right_le_sum M hPA leftBound rightBound) hsumBound).
  }
  assert (hrow : RawDiagonalFormulaShiftTraversalRow M amount
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (rawFormulaEqCode M left right) depth).
  {
    left. exists left, left, right, right.
    split; [reflexivity |]. split; [reflexivity |]. split; assumption.
  }
  destruct (raw_diagonalFormulaShiftBundle_append M hPA amount
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (rawFormulaEqCode M left right) depth
    (raw_diagonalFormulaShiftBundle_empty M hPA amount) hrow)
    as (formulaCode & formulaStep & depthCode & depthStep &
        hbundle & _ & hroot).
  exists formulaCode, formulaStep, depthCode, depthStep,
    (raw_succ M (raw_zero M)), (raw_zero M).
  split; [exact hbundle |]. split.
  - exact (raw_assignment_lt_self_succ M hPA (raw_zero M)).
  - exact hroot.
Qed.

Lemma raw_codedFormulaDiagonalShift_bot_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount depth,
  RawCodedFormulaDiagonalShift M depth amount (rawFormulaBotCode M).
Proof.
  intros M hPA amount depth.
  assert (hrow : RawDiagonalFormulaShiftTraversalRow M amount
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (rawFormulaBotCode M) depth).
  { right. left. split; reflexivity. }
  destruct (raw_diagonalFormulaShiftBundle_append M hPA amount
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
    (raw_zero M) (rawFormulaBotCode M) depth
    (raw_diagonalFormulaShiftBundle_empty M hPA amount) hrow)
    as (formulaCode & formulaStep & depthCode & depthStep &
        hbundle & _ & hroot).
  exists formulaCode, formulaStep, depthCode, depthStep,
    (raw_succ M (raw_zero M)), (raw_zero M).
  split; [exact hbundle |]. split.
  - exact (raw_assignment_lt_self_succ M hPA (raw_zero M)).
  - exact hroot.
Qed.

Lemma raw_codedFormulaDiagonalShift_binary_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount depth
      (constructor : M -> M -> M),
  (forall formulaCode formulaStep depthCode depthStep
      index input rowDepth,
    RawCodedFormulaBinaryOperationRow M constructor
      formulaCode formulaStep formulaCode formulaStep depthCode depthStep
      index input input rowDepth ->
    RawDiagonalFormulaShiftTraversalRow M amount
      formulaCode formulaStep depthCode depthStep
      index input rowDepth) ->
  forall left right,
  RawCodedFormulaDiagonalShift M depth amount left ->
  RawCodedFormulaDiagonalShift M depth amount right ->
  RawCodedFormulaDiagonalShift M depth amount (constructor left right).
Proof.
  intros M hPA amount depth constructor hinject left right
    (leftFormulaCode & leftFormulaStep & leftDepthCode & leftDepthStep &
     leftBound & leftRootIndex & hleft)
    (rightFormulaCode & rightFormulaStep & rightDepthCode & rightDepthStep &
     rightBound & rightRootIndex & hright).
  destruct (raw_diagonalFormulaShiftTraces_concatenate M hPA amount depth
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
    - exact (raw_diagonalLookup_to_triple M
        formulaCode formulaStep depthCode depthStep
        leftRootIndex left depth hleftRoot).
    - split; [reflexivity |]. split; [exact hrightBelow |]. split.
      + exact (raw_diagonalLookup_to_triple M
          formulaCode formulaStep depthCode depthStep
          (raw_add M leftBound rightRootIndex) right depth hrightRoot).
      + repeat split; reflexivity.
  }
  pose proof (hinject formulaCode formulaStep depthCode depthStep
    combinedBound (constructor left right) depth hbinary) as hrow.
  destruct (raw_diagonalFormulaShiftBundle_append M hPA amount
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

Lemma raw_codedFormulaDiagonalShift_imp_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount depth left right,
  RawCodedFormulaDiagonalShift M depth amount left ->
  RawCodedFormulaDiagonalShift M depth amount right ->
  RawCodedFormulaDiagonalShift M depth amount
    (rawFormulaImpCode M left right).
Proof.
  intros M hPA amount depth left right hleft hright.
  apply (raw_codedFormulaDiagonalShift_binary_identity M hPA amount depth
    (rawFormulaImpCode M)).
  - intros. right. right. left. exact H.
  - exact hleft.
  - exact hright.
Qed.

Lemma raw_codedFormulaDiagonalShift_and_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount depth left right,
  RawCodedFormulaDiagonalShift M depth amount left ->
  RawCodedFormulaDiagonalShift M depth amount right ->
  RawCodedFormulaDiagonalShift M depth amount
    (rawFormulaAndCode M left right).
Proof.
  intros M hPA amount depth left right hleft hright.
  apply (raw_codedFormulaDiagonalShift_binary_identity M hPA amount depth
    (rawFormulaAndCode M)).
  - intros. right. right. right. left. exact H.
  - exact hleft.
  - exact hright.
Qed.

Lemma raw_codedFormulaDiagonalShift_or_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount depth left right,
  RawCodedFormulaDiagonalShift M depth amount left ->
  RawCodedFormulaDiagonalShift M depth amount right ->
  RawCodedFormulaDiagonalShift M depth amount
    (rawFormulaOrCode M left right).
Proof.
  intros M hPA amount depth left right hleft hright.
  apply (raw_codedFormulaDiagonalShift_binary_identity M hPA amount depth
    (rawFormulaOrCode M)).
  - intros. right. right. right. right. left. exact H.
  - exact hleft.
  - exact hright.
Qed.

Lemma raw_codedFormulaDiagonalShift_unary_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount depth
      (constructor : M -> M),
  (forall formulaCode formulaStep depthCode depthStep
      index input rowDepth,
    RawCodedFormulaUnaryOperationRow M constructor
      formulaCode formulaStep formulaCode formulaStep depthCode depthStep
      index input input rowDepth ->
    RawDiagonalFormulaShiftTraversalRow M amount
      formulaCode formulaStep depthCode depthStep
      index input rowDepth) ->
  forall child,
  RawCodedFormulaDiagonalShift M (raw_succ M depth) amount child ->
  RawCodedFormulaDiagonalShift M depth amount (constructor child).
Proof.
  intros M hPA amount depth constructor hinject child
    (formulaCode & formulaStep & depthCode & depthStep &
     bound & rootIndex & hchild).
  destruct hchild as [hbundle [hrootBelow hroot]].
  assert (hunary : RawCodedFormulaUnaryOperationRow M constructor
      formulaCode formulaStep formulaCode formulaStep depthCode depthStep
      bound (constructor child) (constructor child) depth).
  {
    exists rootIndex, child, child, (raw_succ M depth).
    split; [exact hrootBelow |]. split.
    - exact (raw_diagonalLookup_to_triple M
        formulaCode formulaStep depthCode depthStep
        rootIndex child (raw_succ M depth) hroot).
    - repeat split; reflexivity.
  }
  pose proof (hinject formulaCode formulaStep depthCode depthStep
    bound (constructor child) depth hunary) as hrow.
  destruct (raw_diagonalFormulaShiftBundle_append M hPA amount
    formulaCode formulaStep depthCode depthStep bound
    (constructor child) depth hbundle hrow)
    as (newFormulaCode & newFormulaStep & newDepthCode & newDepthStep &
        hnewBundle & _ & hnewRoot).
  exists newFormulaCode, newFormulaStep, newDepthCode, newDepthStep,
    (raw_succ M bound), bound.
  split; [exact hnewBundle |]. split.
  - exact (raw_assignment_lt_self_succ M hPA bound).
  - exact hnewRoot.
Qed.

Lemma raw_codedFormulaDiagonalShift_all_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount depth child,
  RawCodedFormulaDiagonalShift M (raw_succ M depth) amount child ->
  RawCodedFormulaDiagonalShift M depth amount (rawFormulaAllCode M child).
Proof.
  intros M hPA amount depth child hchild.
  apply (raw_codedFormulaDiagonalShift_unary_identity M hPA amount depth
    (rawFormulaAllCode M)).
  - intros. right. right. right. right. right. left. exact H.
  - exact hchild.
Qed.

Lemma raw_codedFormulaDiagonalShift_ex_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount depth child,
  RawCodedFormulaDiagonalShift M (raw_succ M depth) amount child ->
  RawCodedFormulaDiagonalShift M depth amount (rawFormulaExCode M child).
Proof.
  intros M hPA amount depth child hchild.
  apply (raw_codedFormulaDiagonalShift_unary_identity M hPA amount depth
    (rawFormulaExCode M)).
  - intros. right. right. right. right. right. right. exact H.
  - exact hchild.
Qed.

(** ------------------------------------------------------------------
    A formula-bound certificate makes every sufficiently high formula shift
    diagonal.  This is the occurrence-indexed strong-prefix invariant; in
    particular, quantified children are proved at the successor cutoff. *)

Definition RawFormulaBoundDiagonalShiftBelow (M : RawPAModel)
    (sourceCode sourceStep boundCode boundStep current : M) : Prop :=
  forall index input inputBound cutoff amount,
    rawLt M index current ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep boundCode boundStep index input inputBound ->
    rawLe M inputBound cutoff ->
    RawCodedFormulaDiagonalShift M cutoff amount input.

Arguments RawFormulaBoundDiagonalShiftBelow M
  sourceCode sourceStep boundCode boundStep current : clear implicits.

Definition formulaBoundDiagonalShiftBelowTermAt
    (sourceCode sourceStep boundCode boundStep current : term) : formula :=
  selfShiftAll5
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 5 current))
      (pImp
        (codedTermOperationPairLookupTermAt
          (liftTerm 5 sourceCode) (liftTerm 5 sourceStep)
          (liftTerm 5 boundCode) (liftTerm 5 boundStep)
          (tVar 4) (tVar 3) (tVar 2))
        (pImp
          (Formula.leTermAt (tVar 2) (tVar 1))
          (codedFormulaDiagonalShiftTermAt
            (tVar 1) (tVar 0) (tVar 3))))).

Lemma raw_sat_formulaBoundDiagonalShiftBelowTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep boundCode boundStep current,
  raw_formula_sat M e
    (formulaBoundDiagonalShiftBelowTermAt
      sourceCode sourceStep boundCode boundStep current) <->
  RawFormulaBoundDiagonalShiftBelow M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e boundCode) (raw_term_eval M e boundStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold formulaBoundDiagonalShiftBelowTermAt, selfShiftAll5,
    RawFormulaBoundDiagonalShiftBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_leTermAt_iff_rank.
  setoid_rewrite raw_sat_codedFormulaDiagonalShiftTermAt_iff.
  repeat setoid_rewrite raw_selfShift_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawFormulaBoundDiagonalShiftWithin (M : RawPAModel)
    (sourceCode sourceStep boundCode boundStep limit current : M) : Prop :=
  rawLe M current limit ->
  RawFormulaBoundDiagonalShiftBelow M
    sourceCode sourceStep boundCode boundStep current.

Arguments RawFormulaBoundDiagonalShiftWithin M
  sourceCode sourceStep boundCode boundStep limit current : clear implicits.

Definition formulaBoundDiagonalShiftWithinTermAt
    (sourceCode sourceStep boundCode boundStep limit current : term)
    : formula :=
  pImp
    (Formula.leTermAt current limit)
    (formulaBoundDiagonalShiftBelowTermAt
      sourceCode sourceStep boundCode boundStep current).

Lemma raw_sat_formulaBoundDiagonalShiftWithinTermAt_iff : forall
    (M : RawPAModel) e
      sourceCode sourceStep boundCode boundStep limit current,
  raw_formula_sat M e
    (formulaBoundDiagonalShiftWithinTermAt
      sourceCode sourceStep boundCode boundStep limit current) <->
  RawFormulaBoundDiagonalShiftWithin M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e boundCode) (raw_term_eval M e boundStep)
    (raw_term_eval M e limit) (raw_term_eval M e current).
Proof.
  intros. unfold formulaBoundDiagonalShiftWithinTermAt,
    RawFormulaBoundDiagonalShiftWithin.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank,
    raw_sat_formulaBoundDiagonalShiftBelowTermAt_iff.
  reflexivity.
Qed.

Lemma raw_formulaBoundDiagonalShiftBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sourceCode sourceStep boundCode boundStep,
  RawFormulaBoundDiagonalShiftBelow M
    sourceCode sourceStep boundCode boundStep (raw_zero M).
Proof.
  intros M hPA sourceCode sourceStep boundCode boundStep
    index input inputBound cutoff amount hindex _ _.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Lemma raw_formulaBoundDiagonalShiftBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sourceCode sourceStep boundCode boundStep root output current,
  RawCodedFormulaBoundTrace M
    sourceCode sourceStep boundCode boundStep root output ->
  rawLt M current (raw_succ M root) ->
  RawFormulaBoundDiagonalShiftBelow M
    sourceCode sourceStep boundCode boundStep current ->
  RawFormulaBoundDiagonalShiftBelow M
    sourceCode sourceStep boundCode boundStep (raw_succ M current).
Proof.
  intros M hPA sourceCode sourceStep boundCode boundStep root output current
    [_ [_ [_ hboundRows]]] hcurrent hprefix
    index input inputBound cutoff amount hindex hlookup hboundCutoff.
  destruct (raw_lt_succ_cases M hPA index current hindex)
    as [hindexOld | ->].
  - exact (hprefix index input inputBound cutoff amount
      hindexOld hlookup hboundCutoff).
  - pose proof (hboundRows current input inputBound hcurrent hlookup)
      as hrow.
    destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
    + destruct heq as
        (leftTerm & leftBound & rightTerm & rightBound &
         hinput & hleftBound & hrightBound & hboundEq).
      subst input. subst inputBound.
      exact (raw_codedFormulaDiagonalShift_eq_identity M hPA
        amount cutoff leftTerm rightTerm leftBound rightBound
        hleftBound hrightBound hboundCutoff).
    + destruct hbot as [hinput hboundEq].
      subst input. subst inputBound.
      exact (raw_codedFormulaDiagonalShift_bot_identity M hPA
        amount cutoff).
    + destruct himp as
        (leftIndex & inputLeft & leftBound &
         rightIndex & inputRight & rightBound &
         hleft & hleftLookup & hright & hrightLookup & hinput & hboundEq).
      subst input. subst inputBound.
      apply (raw_codedFormulaDiagonalShift_imp_identity M hPA
        amount cutoff inputLeft inputRight).
      * apply (hprefix leftIndex inputLeft leftBound cutoff amount
          hleft hleftLookup).
        exact (raw_le_trans M hPA leftBound
          (raw_add M leftBound rightBound) cutoff
          (raw_proof_left_le_sum M leftBound rightBound) hboundCutoff).
      * apply (hprefix rightIndex inputRight rightBound cutoff amount
          hright hrightLookup).
        exact (raw_le_trans M hPA rightBound
          (raw_add M leftBound rightBound) cutoff
          (raw_proof_right_le_sum M hPA leftBound rightBound) hboundCutoff).
    + destruct hand as
        (leftIndex & inputLeft & leftBound &
         rightIndex & inputRight & rightBound &
         hleft & hleftLookup & hright & hrightLookup & hinput & hboundEq).
      subst input. subst inputBound.
      apply (raw_codedFormulaDiagonalShift_and_identity M hPA
        amount cutoff inputLeft inputRight).
      * apply (hprefix leftIndex inputLeft leftBound cutoff amount
          hleft hleftLookup).
        exact (raw_le_trans M hPA leftBound
          (raw_add M leftBound rightBound) cutoff
          (raw_proof_left_le_sum M leftBound rightBound) hboundCutoff).
      * apply (hprefix rightIndex inputRight rightBound cutoff amount
          hright hrightLookup).
        exact (raw_le_trans M hPA rightBound
          (raw_add M leftBound rightBound) cutoff
          (raw_proof_right_le_sum M hPA leftBound rightBound) hboundCutoff).
    + destruct hor as
        (leftIndex & inputLeft & leftBound &
         rightIndex & inputRight & rightBound &
         hleft & hleftLookup & hright & hrightLookup & hinput & hboundEq).
      subst input. subst inputBound.
      apply (raw_codedFormulaDiagonalShift_or_identity M hPA
        amount cutoff inputLeft inputRight).
      * apply (hprefix leftIndex inputLeft leftBound cutoff amount
          hleft hleftLookup).
        exact (raw_le_trans M hPA leftBound
          (raw_add M leftBound rightBound) cutoff
          (raw_proof_left_le_sum M leftBound rightBound) hboundCutoff).
      * apply (hprefix rightIndex inputRight rightBound cutoff amount
          hright hrightLookup).
        exact (raw_le_trans M hPA rightBound
          (raw_add M leftBound rightBound) cutoff
          (raw_proof_right_le_sum M hPA leftBound rightBound) hboundCutoff).
    + destruct hall as
        (childIndex & inputChild & childBound &
         hchild & hchildLookup & hinput & hboundEq).
      subst input. subst inputBound.
      apply (raw_codedFormulaDiagonalShift_all_identity M hPA
        amount cutoff inputChild).
      apply (hprefix childIndex inputChild childBound
        (raw_succ M cutoff) amount hchild hchildLookup).
      exact (raw_le_trans M hPA childBound cutoff (raw_succ M cutoff)
        hboundCutoff
        (raw_lt_to_le M cutoff (raw_succ M cutoff)
          (raw_assignment_lt_self_succ M hPA cutoff))).
    + destruct hex as
        (childIndex & inputChild & childBound &
         hchild & hchildLookup & hinput & hboundEq).
      subst input. subst inputBound.
      apply (raw_codedFormulaDiagonalShift_ex_identity M hPA
        amount cutoff inputChild).
      apply (hprefix childIndex inputChild childBound
        (raw_succ M cutoff) amount hchild hchildLookup).
      exact (raw_le_trans M hPA childBound cutoff (raw_succ M cutoff)
        hboundCutoff
        (raw_lt_to_le M cutoff (raw_succ M cutoff)
          (raw_assignment_lt_self_succ M hPA cutoff))).
Qed.

Theorem raw_formulaBoundDiagonalShiftWithin_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sourceCode sourceStep boundCode boundStep root output,
  RawCodedFormulaBoundTrace M
    sourceCode sourceStep boundCode boundStep root output ->
  forall current,
  RawFormulaBoundDiagonalShiftWithin M
    sourceCode sourceStep boundCode boundStep (raw_succ M root) current.
Proof.
  intros M hPA sourceCode sourceStep boundCode boundStep root output htrace.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => sourceCode
    | 1 => sourceStep
    | 2 => boundCode
    | 3 => boundStep
    | _ => raw_succ M root
    end).
  set (phi := formulaBoundDiagonalShiftWithinTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_formulaBoundDiagonalShiftWithinTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons]. intros _.
      exact (raw_formulaBoundDiagonalShiftBelow_zero M hPA
        sourceCode sourceStep boundCode boundStep).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_formulaBoundDiagonalShiftWithinTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_formulaBoundDiagonalShiftWithinTermAt_iff M
        (scons M (raw_succ M current) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      intro hsuccLe.
      assert (hcurrentBelow : rawLt M current (raw_succ M root)).
      { exact (raw_rank_lt_of_succ_le M hPA current
          (raw_succ M root) hsuccLe). }
      apply (raw_formulaBoundDiagonalShiftBelow_succ M hPA
        sourceCode sourceStep boundCode boundStep root output current
        htrace hcurrentBelow).
      apply hcurrent.
      exact (raw_lt_to_le M current (raw_succ M root) hcurrentBelow).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_formulaBoundDiagonalShiftWithinTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))
    (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

Theorem raw_codedFormulaShift_identity_above_bound : forall
    (M : RawPAModel), RawPASatisfies M -> forall input inputBound,
  RawCodedFormulaBound M input inputBound ->
  forall cutoff amount,
  rawLe M inputBound cutoff ->
  RawCodedFormulaShift M cutoff amount input input.
Proof.
  intros M hPA input inputBound
    (sourceCode & sourceStep & boundCode & boundStep & htrace)
    cutoff amount hbound.
  destruct htrace as
    [hsourceDefined [hboundDefined [hrootLookup hrows]]].
  assert (htraceAgain : RawCodedFormulaBoundTrace M
      sourceCode sourceStep boundCode boundStep input inputBound).
  { exact (conj hsourceDefined
      (conj hboundDefined (conj hrootLookup hrows))). }
  pose proof (raw_formulaBoundDiagonalShiftWithin_all M hPA
    sourceCode sourceStep boundCode boundStep input inputBound
    htraceAgain (raw_succ M input)) as hall.
  specialize (hall (raw_rank_le_refl M hPA (raw_succ M input))).
  apply (raw_codedFormulaShift_of_diagonal M hPA cutoff amount input).
  exact (hall input input inputBound cutoff amount
    (raw_assignment_lt_self_succ M hPA input) hrootLookup hbound).
Qed.

End PABoundedRawCodedPAAxiomContextSelfShift.
