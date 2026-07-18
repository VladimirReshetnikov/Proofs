(**
  Pointwise de Bruijn shift of model-internal proof contexts.

  The universal-introduction and existential-elimination rules do not keep
  their premise context literally equal to the conclusion context: every
  formula in it is renamed by successor.  For a possibly nonstandard coded
  context this map cannot be performed by Rocq recursion.  Instead, the
  relation below compares two honest context traversals row by row and asks
  the already arithmetized formula-shift graph to relate their heads.

  Both traversals share one model-internal length.  The functionality theorem
  for contexts then makes the public relation independent of the particular
  beta tables hidden by its existential quantifiers.  The cons construction
  uses beta prepend on both traversals, so it also works through nonstandard
  tails and never decodes a carrier element.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedContextLists RawCodedContextStructure
  RawCodedContextFunctionality RawCodedFormulaOperations.

Import ListNotations.

Module PABoundedRawCodedContextShift.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextFunctionality.
Import PABoundedRawCodedFormulaOperations.

(** ------------------------------------------------------------------
    Pointwise agreement of two chosen head tables. *)

Definition RawContextShiftRows (M : RawPAModel)
    (bound sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep : M)
    : Prop :=
  forall index,
    rawLt M index bound ->
    forall sourceFormula targetFormula,
      RawCodedAssignmentLookup M
        sourceHeadCode sourceHeadStep index sourceFormula ->
      RawCodedAssignmentLookup M
        targetHeadCode targetHeadStep index targetFormula ->
      RawCodedFormulaShift M
        (raw_zero M) (rawNumeralValue M 1)
        sourceFormula targetFormula.

Arguments RawContextShiftRows
  M bound sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep
  : clear implicits.

Definition contextShiftRowsTermAt
    (bound sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep : term)
    : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (pAll
        (pImp
          (codedAssignmentLookupTermAt
            (liftTerm 2 sourceHeadCode) (liftTerm 2 sourceHeadStep)
            (tVar 1) (tVar 0))
          (pAll
            (pImp
              (codedAssignmentLookupTermAt
                (liftTerm 3 targetHeadCode) (liftTerm 3 targetHeadStep)
                (tVar 2) (tVar 0))
              (codedFormulaShiftTermAt
                tZero (Term.numeral 1) (tVar 1) (tVar 0))))))).

Lemma raw_contextShift_eval_liftTerm_two : forall
    (M : RawPAModel) a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M a b e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 2) with (S (S i)) by lia. reflexivity.
Qed.

Lemma raw_sat_contextShiftRowsTermAt_iff : forall
    (M : RawPAModel) e
    bound sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep,
  raw_formula_sat M e
    (contextShiftRowsTermAt
      bound sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep) <->
  RawContextShiftRows M
    (raw_term_eval M e bound)
    (raw_term_eval M e sourceHeadCode)
    (raw_term_eval M e sourceHeadStep)
    (raw_term_eval M e targetHeadCode)
    (raw_term_eval M e targetHeadStep).
Proof.
  intros M e bound sourceHeadCode sourceHeadStep
    targetHeadCode targetHeadStep.
  unfold contextShiftRowsTermAt, RawContextShiftRows.
  cbn [raw_formula_sat]. split.
  - intros hall index hindex sourceFormula targetFormula
      hsource htarget.
    assert (hltSat : raw_formula_sat M (scons M index e)
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_contextList_eval_liftTerm_one.
      cbn [raw_term_eval scons]. exact hindex.
    }
    pose proof (hall index hltSat sourceFormula) as hsourceImp.
    assert (hsourceSat : raw_formula_sat M
        (scons M sourceFormula (scons M index e))
        (codedAssignmentLookupTermAt
          (liftTerm 2 sourceHeadCode) (liftTerm 2 sourceHeadStep)
          (tVar 1) (tVar 0))).
    {
      apply (proj2
        (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)).
      rewrite !raw_contextShift_eval_liftTerm_two.
      cbn [raw_term_eval scons]. exact hsource.
    }
    pose proof (hsourceImp hsourceSat targetFormula) as htargetImp.
    assert (htargetSat : raw_formula_sat M
        (scons M targetFormula
          (scons M sourceFormula (scons M index e)))
        (codedAssignmentLookupTermAt
          (liftTerm 3 targetHeadCode) (liftTerm 3 targetHeadStep)
          (tVar 2) (tVar 0))).
    {
      apply (proj2
        (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)).
      rewrite !raw_contextList_eval_liftTerm_three.
      cbn [raw_term_eval scons]. exact htarget.
    }
    apply (proj1 (raw_sat_codedFormulaShiftTermAt_iff M
      (scons M targetFormula
        (scons M sourceFormula (scons M index e)))
      tZero (Term.numeral 1) (tVar 1) (tVar 0))).
    cbn [raw_term_eval scons].
    exact (htargetImp htargetSat).
  - intros hrows index hltSat sourceFormula hsourceSat
      targetFormula htargetSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat) as hindex.
    rewrite raw_contextList_eval_liftTerm_one in hindex.
    cbn [raw_term_eval scons] in hindex.
    pose proof (proj1
      (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)
      hsourceSat) as hsource.
    rewrite !raw_contextShift_eval_liftTerm_two in hsource.
    cbn [raw_term_eval scons] in hsource.
    pose proof (proj1
      (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)
      htargetSat) as htarget.
    rewrite !raw_contextList_eval_liftTerm_three in htarget.
    cbn [raw_term_eval scons] in htarget.
    apply (proj2 (raw_sat_codedFormulaShiftTermAt_iff M
      (scons M targetFormula
        (scons M sourceFormula (scons M index e)))
      tZero (Term.numeral 1) (tVar 1) (tVar 0))).
    cbn [raw_term_eval scons].
    exact (hrows index hindex sourceFormula targetFormula
      hsource htarget).
Qed.

(** ------------------------------------------------------------------
    Public pointwise shift relation. *)

Definition RawContextShiftWithTables (M : RawPAModel)
    (sourceRoot targetRoot bound
      sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
      targetTailCode targetTailStep targetHeadCode targetHeadStep : M)
    : Prop :=
  RawContextListTraversal M sourceRoot bound
    sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep /\
  RawContextListTraversal M targetRoot bound
    targetTailCode targetTailStep targetHeadCode targetHeadStep /\
  RawContextShiftRows M bound
    sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep.

Arguments RawContextShiftWithTables
  M sourceRoot targetRoot bound
    sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
    targetTailCode targetTailStep targetHeadCode targetHeadStep
  : clear implicits.

Definition contextShiftWithTablesTermAt
    (sourceRoot targetRoot bound
      sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
      targetTailCode targetTailStep targetHeadCode targetHeadStep : term)
    : formula :=
  pAnd
    (contextListTraversalTermAt
      sourceRoot bound sourceTailCode sourceTailStep
      sourceHeadCode sourceHeadStep)
    (pAnd
      (contextListTraversalTermAt
        targetRoot bound targetTailCode targetTailStep
        targetHeadCode targetHeadStep)
      (contextShiftRowsTermAt bound
        sourceHeadCode sourceHeadStep targetHeadCode targetHeadStep)).

Lemma raw_sat_contextShiftWithTablesTermAt_iff : forall
    (M : RawPAModel) e
    sourceRoot targetRoot bound
    sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
    targetTailCode targetTailStep targetHeadCode targetHeadStep,
  raw_formula_sat M e
    (contextShiftWithTablesTermAt
      sourceRoot targetRoot bound
      sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
      targetTailCode targetTailStep targetHeadCode targetHeadStep) <->
  RawContextShiftWithTables M
    (raw_term_eval M e sourceRoot) (raw_term_eval M e targetRoot)
    (raw_term_eval M e bound)
    (raw_term_eval M e sourceTailCode)
    (raw_term_eval M e sourceTailStep)
    (raw_term_eval M e sourceHeadCode)
    (raw_term_eval M e sourceHeadStep)
    (raw_term_eval M e targetTailCode)
    (raw_term_eval M e targetTailStep)
    (raw_term_eval M e targetHeadCode)
    (raw_term_eval M e targetHeadStep).
Proof.
  intros. unfold contextShiftWithTablesTermAt,
    RawContextShiftWithTables.
  cbn [raw_formula_sat].
  rewrite !raw_sat_contextListTraversalTermAt_iff,
    raw_sat_contextShiftRowsTermAt_iff.
  reflexivity.
Qed.

Definition contextShiftEx9 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx body)))))))).

Definition contextShiftTermAt (sourceRoot targetRoot : term) : formula :=
  contextShiftEx9
    (contextShiftWithTablesTermAt
      (liftTerm 9 sourceRoot) (liftTerm 9 targetRoot)
      (tVar 8)
      (tVar 7) (tVar 6) (tVar 5) (tVar 4)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)).

Definition RawContextShift (M : RawPAModel)
    (sourceRoot targetRoot : M) : Prop :=
  exists bound
    sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
    targetTailCode targetTailStep targetHeadCode targetHeadStep : M,
  RawContextShiftWithTables M sourceRoot targetRoot bound
    sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
    targetTailCode targetTailStep targetHeadCode targetHeadStep.

Arguments RawContextShift M sourceRoot targetRoot : clear implicits.

Lemma raw_contextShift_eval_liftTerm_nine : forall
    (M : RawPAModel) a b c d f g h i j (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i (scons M j e)))))))))
    (liftTerm 9 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro k.
  replace (k + 9) with
    (S (S (S (S (S (S (S (S (S k))))))))) by lia.
  reflexivity.
Qed.

Lemma raw_sat_contextShiftTermAt_iff : forall
    (M : RawPAModel) e sourceRoot targetRoot,
  raw_formula_sat M e (contextShiftTermAt sourceRoot targetRoot) <->
  RawContextShift M
    (raw_term_eval M e sourceRoot) (raw_term_eval M e targetRoot).
Proof.
  intros M e sourceRoot targetRoot.
  unfold contextShiftTermAt, contextShiftEx9, RawContextShift.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextShiftWithTablesTermAt_iff.
  repeat setoid_rewrite raw_contextShift_eval_liftTerm_nine.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Structural and membership consequences. *)

Lemma raw_contextShift_source_realizable : forall
    (M : RawPAModel) sourceRoot targetRoot,
  RawContextShift M sourceRoot targetRoot ->
  RawContextListRealizable M sourceRoot.
Proof.
  intros M sourceRoot targetRoot
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep & [hsource _]).
  exists bound, sourceTailCode, sourceTailStep,
    sourceHeadCode, sourceHeadStep. exact hsource.
Qed.

Lemma raw_contextShift_target_realizable : forall
    (M : RawPAModel) sourceRoot targetRoot,
  RawContextShift M sourceRoot targetRoot ->
  RawContextListRealizable M targetRoot.
Proof.
  intros M sourceRoot targetRoot
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep & [_ [htarget _]]).
  exists bound, targetTailCode, targetTailStep,
    targetHeadCode, targetHeadStep. exact htarget.
Qed.

Theorem raw_contextShift_source_member : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall sourceRoot targetRoot sourceFormula,
  RawContextShift M sourceRoot targetRoot ->
  RawContextListMember M sourceRoot sourceFormula ->
  exists targetFormula,
    RawContextListMember M targetRoot targetFormula /\
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      sourceFormula targetFormula.
Proof.
  intros M hPA sourceRoot targetRoot sourceFormula
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep &
      [hsource [htarget hrows]]) hmember.
  pose proof (proj1 (raw_contextListMember_iff_with_traversal M hPA
    sourceRoot sourceFormula bound sourceTailCode sourceTailStep
    sourceHeadCode sourceHeadStep hsource) hmember)
    as [index [hindex hsourceLookup]].
  pose proof htarget as htargetFacts.
  destruct htargetFacts as [_ [_ [htargetDefined _]]].
  destruct (htargetDefined index hindex)
    as [targetFormula htargetLookup].
  exists targetFormula. split.
  - apply (proj2 (raw_contextListMember_iff_with_traversal M hPA
      targetRoot targetFormula bound targetTailCode targetTailStep
      targetHeadCode targetHeadStep htarget)).
    exists index. split; assumption.
  - exact (hrows index hindex sourceFormula targetFormula
      hsourceLookup htargetLookup).
Qed.

Theorem raw_contextShift_target_member : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall sourceRoot targetRoot targetFormula,
  RawContextShift M sourceRoot targetRoot ->
  RawContextListMember M targetRoot targetFormula ->
  exists sourceFormula,
    RawContextListMember M sourceRoot sourceFormula /\
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      sourceFormula targetFormula.
Proof.
  intros M hPA sourceRoot targetRoot targetFormula
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep &
      [hsource [htarget hrows]]) hmember.
  pose proof (proj1 (raw_contextListMember_iff_with_traversal M hPA
    targetRoot targetFormula bound targetTailCode targetTailStep
    targetHeadCode targetHeadStep htarget) hmember)
    as [index [hindex htargetLookup]].
  pose proof hsource as hsourceFacts.
  destruct hsourceFacts as [_ [_ [hsourceDefined _]]].
  destruct (hsourceDefined index hindex)
    as [sourceFormula hsourceLookup].
  exists sourceFormula. split.
  - apply (proj2 (raw_contextListMember_iff_with_traversal M hPA
      sourceRoot sourceFormula bound sourceTailCode sourceTailStep
      sourceHeadCode sourceHeadStep hsource)).
    exists index. split; assumption.
  - exact (hrows index hindex sourceFormula targetFormula
      hsourceLookup htargetLookup).
Qed.

Theorem raw_contextShift_empty : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawContextShift M (raw_zero M) (raw_zero M).
Proof.
  intros M hPA.
  destruct (raw_contextList_zero_traversal_exists M hPA)
    as [tailCode [tailStep hzero]].
  exists (raw_zero M), tailCode, tailStep,
    (raw_zero M), (raw_zero M),
    tailCode, tailStep, (raw_zero M), (raw_zero M).
  split; [exact hzero |]. split; [exact hzero |].
  intros index hindex.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

(** Pointwise shift is closed by canonical cons.  The proof compares the
    freshly prepended row zero directly and reduces every successor row to
    the old pair of tables. *)
Theorem raw_contextShift_cons : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall sourceTail targetTail sourceHead targetHead,
  RawContextShift M sourceTail targetTail ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1) sourceHead targetHead ->
  RawContextShift M
    (rawListNode M sourceHead sourceTail)
    (rawListNode M targetHead targetTail).
Proof.
  intros M hPA sourceTail targetTail sourceHead targetHead
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep &
      [hsource [htarget hrows]]) hheadShift.
  destruct (raw_contextListConsExtension_exists M hPA
    sourceTail sourceHead bound
    sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep hsource)
    as (newSourceTailCode & newSourceTailStep &
      newSourceHeadCode & newSourceHeadStep &
      _ & hsourceHeadPrepend & hnewSource).
  destruct (raw_contextListConsExtension_exists M hPA
    targetTail targetHead bound
    targetTailCode targetTailStep targetHeadCode targetHeadStep htarget)
    as (newTargetTailCode & newTargetTailStep &
      newTargetHeadCode & newTargetHeadStep &
      _ & htargetHeadPrepend & hnewTarget).
  exists (raw_succ M bound),
    newSourceTailCode, newSourceTailStep,
    newSourceHeadCode, newSourceHeadStep,
    newTargetTailCode, newTargetTailStep,
    newTargetHeadCode, newTargetHeadStep.
  split; [exact hnewSource |]. split; [exact hnewTarget |].
  intros index hindex rowSource rowTarget
    hsourceLookup htargetLookup.
  destruct (raw_assignment_zero_or_successor M hPA index)
    as [-> | [predecessor ->]].
  - pose proof (proj1 (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
      sourceHeadCode sourceHeadStep sourceHead bound
      newSourceHeadCode newSourceHeadStep rowSource
      hsourceHeadPrepend) hsourceLookup) as hsourceEq.
    pose proof (proj1 (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
      targetHeadCode targetHeadStep targetHead bound
      newTargetHeadCode newTargetHeadStep rowTarget
      htargetHeadPrepend) htargetLookup) as htargetEq.
    subst rowSource. subst rowTarget. exact hheadShift.
  - assert (hpredSelf : rawLt M predecessor (raw_succ M predecessor)).
    { exact (raw_assignment_lt_self_succ M hPA predecessor). }
    assert (hpredBound : rawLt M predecessor bound).
    {
      destruct (raw_lt_succ_cases M hPA
        (raw_succ M predecessor) bound hindex) as [hlt | heq].
      - exact (raw_assignment_lt_trans M hPA predecessor
          (raw_succ M predecessor) bound hpredSelf hlt).
      - rewrite <- heq. exact hpredSelf.
    }
    assert (holdSource : RawCodedAssignmentLookup M
        sourceHeadCode sourceHeadStep predecessor rowSource).
    {
      exact (proj1 (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
        sourceHeadCode sourceHeadStep sourceHead bound
        newSourceHeadCode newSourceHeadStep
        (proj1 (proj2 (proj2 hsource))) hsourceHeadPrepend
        predecessor hpredBound rowSource) hsourceLookup).
    }
    assert (holdTarget : RawCodedAssignmentLookup M
        targetHeadCode targetHeadStep predecessor rowTarget).
    {
      exact (proj1 (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
        targetHeadCode targetHeadStep targetHead bound
        newTargetHeadCode newTargetHeadStep
        (proj1 (proj2 (proj2 htarget))) htargetHeadPrepend
        predecessor hpredBound rowTarget) htargetLookup).
    }
    exact (hrows predecessor hpredBound rowSource rowTarget
      holdSource holdTarget).
Qed.

End PABoundedRawCodedContextShift.
