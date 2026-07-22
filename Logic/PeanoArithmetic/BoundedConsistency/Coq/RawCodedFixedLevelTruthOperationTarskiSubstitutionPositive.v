(**
  Positive-level Tarski transport for coded single substitution.

  A substitution trace carries an internal binder depth.  At that depth the
  replacement has first been shifted, and the source term is then opened.
  In a nonstandard model neither trace can be decoded into an external Rocq
  syntax tree.  We therefore record the two environment invariants by PA
  formulae and propagate them with the represented operation-table
  induction, exactly as for shift transport.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation RawCodedAssignment RawCodedProofDescent
  PolynomialPairInjectivity
  RawCodedTermEvaluationTraversal
  RawCodedFormulaRankTraversal RawCodedFormulaOperations
  RawCodedRankZeroTruthTraversal
  RawCodedRankZeroTruthStepFunctionality
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFixedLevelTruthSchedule RawCodedFixedLevelTruthLaws
  RawCodedFixedLevelTruthOperationTransport
  RawCodedFixedLevelTruthOperationTarski
  RawCodedFixedLevelTruthOperationTarskiPositive.

Import ListNotations.

Module PABoundedRawCodedFixedLevelTruthOperationTarskiSubstitutionPositive.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofDescent.
Import PABoundedPolynomialPairInjectivity.
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
Import PABoundedRawCodedFixedLevelTruthOperationTarskiPositive.

(** ------------------------------------------------------------------
    The represented opening-assignment invariant.

    Below [depth], opening preserves an index.  At [depth], the source
    assignment must contain the value of the replacement.  Above [depth],
    opening deletes one binder and therefore uses the predecessor index on
    the target side.  Both formula-code bounds are explicit: beta prepend
    has no contractual behaviour outside its certified prefix. *)

Definition codedFormulaSubstitutionOpeningCompatibilityTermAt
    (depth replacementValue sourceBound targetBound
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  operationTarskiPositiveAll4
    (pImp
      (Formula.ltTermAt (tVar 3) (liftTerm 4 sourceBound))
      (pImp
        (codedAssignmentLookupTermAt
          (liftTerm 4 sourceAssignmentCode)
          (liftTerm 4 sourceAssignmentStep) (tVar 3) (tVar 1))
        (operationAnd3
          (pImp
            (Formula.ltTermAt (tVar 3) (liftTerm 4 depth))
            (pImp
              (Formula.ltTermAt (tVar 3) (liftTerm 4 targetBound))
              (pImp
                (codedAssignmentLookupTermAt
                  (liftTerm 4 targetAssignmentCode)
                  (liftTerm 4 targetAssignmentStep) (tVar 3) (tVar 0))
                (pEq (tVar 1) (tVar 0)))))
          (pImp
            (pEq (tVar 3) (liftTerm 4 depth))
            (pEq (tVar 1) (liftTerm 4 replacementValue)))
          (pImp
            (pEq (tVar 3) (tSucc (tVar 2)))
            (pImp
              (Formula.ltTermAt (liftTerm 4 depth) (tVar 3))
              (pImp
                (Formula.ltTermAt (tVar 2) (liftTerm 4 targetBound))
                (pImp
                  (codedAssignmentLookupTermAt
                    (liftTerm 4 targetAssignmentCode)
                    (liftTerm 4 targetAssignmentStep)
                    (tVar 2) (tVar 0))
                  (pEq (tVar 1) (tVar 0))))))))).

Definition RawCodedFormulaSubstitutionOpeningCompatibility
    (M : RawPAModel)
    (depth replacementValue sourceBound targetBound
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  forall inputIndex predecessor sourceValue targetValue : M,
    rawLt M inputIndex sourceBound ->
    RawCodedAssignmentLookup M sourceAssignmentCode sourceAssignmentStep
      inputIndex sourceValue ->
    (rawLt M inputIndex depth ->
      rawLt M inputIndex targetBound ->
      RawCodedAssignmentLookup M targetAssignmentCode targetAssignmentStep
        inputIndex targetValue ->
      sourceValue = targetValue) /\
    (inputIndex = depth -> sourceValue = replacementValue) /\
    (inputIndex = raw_succ M predecessor ->
      rawLt M depth inputIndex ->
      rawLt M predecessor targetBound ->
      RawCodedAssignmentLookup M targetAssignmentCode targetAssignmentStep
        predecessor targetValue ->
      sourceValue = targetValue).

Arguments RawCodedFormulaSubstitutionOpeningCompatibility
  M depth replacementValue sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_sat_codedFormulaSubstitutionOpeningCompatibilityTermAt_iff :
  forall (M : RawPAModel) e depth replacementValue sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (codedFormulaSubstitutionOpeningCompatibilityTermAt
      depth replacementValue sourceBound targetBound
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawCodedFormulaSubstitutionOpeningCompatibility M
    (raw_term_eval M e depth) (raw_term_eval M e replacementValue)
    (raw_term_eval M e sourceBound) (raw_term_eval M e targetBound)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold codedFormulaSubstitutionOpeningCompatibilityTermAt,
    operationTarskiPositiveAll4, operationAnd3,
    RawCodedFormulaSubstitutionOpeningCompatibility.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  repeat setoid_rewrite raw_operationTarskiPositive_eval_liftTerm_four.
  cbn [raw_term_eval scons]. tauto.
Qed.

Lemma raw_codedFormulaShiftAssignmentLocalCompatibility_target_restrict :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount sourceBound targetParentBound targetChildBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaShiftAssignmentLocalCompatibility M cutoff amount
    sourceBound targetParentBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  rawLt M targetChildBound targetParentBound ->
  RawCodedFormulaShiftAssignmentLocalCompatibility M cutoff amount
    sourceBound targetChildBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA cutoff amount sourceBound targetParentBound targetChildBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hcompat hchild
    inputIndex outputIndex sourceValue targetValue
    hinput houtput hshift hsource htarget.
  exact (hcompat inputIndex outputIndex sourceValue targetValue
    hinput
    (raw_assignment_lt_trans M hPA outputIndex targetChildBound
      targetParentBound houtput hchild)
    hshift hsource htarget).
Qed.

Lemma raw_codedFormulaSubstitutionOpeningCompatibility_restrict :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    depth replacementValue sourceParentBound targetParentBound
    sourceChildBound targetChildBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaSubstitutionOpeningCompatibility M
    depth replacementValue sourceParentBound targetParentBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  rawLt M sourceChildBound sourceParentBound ->
  rawLt M targetChildBound targetParentBound ->
  RawCodedFormulaSubstitutionOpeningCompatibility M
    depth replacementValue sourceChildBound targetChildBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA depth replacementValue sourceParentBound targetParentBound
    sourceChildBound targetChildBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hcompat hsourceChild htargetChild
    inputIndex predecessor sourceValue targetValue
    hinput hsourceLookup.
  destruct (hcompat inputIndex predecessor sourceValue targetValue
    (raw_assignment_lt_trans M hPA inputIndex sourceChildBound
      sourceParentBound hinput hsourceChild) hsourceLookup)
    as [hlow [hequal hhigh]].
  split.
  - intros hbelow htargetBound htargetLookup.
    exact (hlow hbelow
      (raw_assignment_lt_trans M hPA inputIndex targetChildBound
        targetParentBound htargetBound htargetChild) htargetLookup).
  - split; [exact hequal |].
  intros hsuccessor habove hpredecessor htargetLookup.
  exact (hhigh hsuccessor habove
    (raw_assignment_lt_trans M hPA predecessor targetChildBound
      targetParentBound hpredecessor htargetChild) htargetLookup).
Qed.

(** At the root, the public substitution relation is precisely opening at
    depth zero.  The proof uses only the head/tail laws promised by prepend;
    it does not invert an arbitrary out-of-bound beta row. *)
Lemma raw_codedFormulaSubstitutionOpeningCompatibility_root : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacementValue sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedAssignmentPrepend M
    targetAssignmentCode targetAssignmentStep replacementValue sourceBound
    sourceAssignmentCode sourceAssignmentStep ->
  RawCodedFormulaSubstitutionOpeningCompatibility M
    (raw_zero M) replacementValue sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA replacementValue sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hprepend
    inputIndex predecessor sourceValue targetValue
    hinput hsourceLookup.
  split.
  - intros himpossible _ _. exfalso.
    exact (raw_not_lt_zero M hPA inputIndex himpossible).
  - split.
    + intro hzero. subst inputIndex.
      exact (proj1
        (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
          targetAssignmentCode targetAssignmentStep replacementValue
          sourceBound sourceAssignmentCode sourceAssignmentStep
          sourceValue hprepend) hsourceLookup).
    + intros hsuccessor _ hpredecessorBound htargetLookup.
      subst inputIndex.
      assert (hpredecessorSource : rawLt M predecessor sourceBound).
      {
        exact (raw_assignment_lt_trans M hPA predecessor
          (raw_succ M predecessor) sourceBound
          (raw_assignment_lt_self_succ M hPA predecessor) hinput).
      }
      pose proof (raw_codedAssignmentPrepend_tail M
        targetAssignmentCode targetAssignmentStep replacementValue
        sourceBound sourceAssignmentCode sourceAssignmentStep
        predecessor targetValue hprepend hpredecessorSource htargetLookup)
        as hsourceTarget.
      exact (raw_codedAssignmentLookup_functional M hPA
        sourceAssignmentCode sourceAssignmentStep
        (raw_succ M predecessor) sourceValue targetValue
        hsourceLookup hsourceTarget).
Qed.

(** Increasing the shift amount by one and prepending one value to the
    target environment preserve evaluation of the fixed root replacement.
    Unlike the ordinary binder law for formula shift, the root environment
    is deliberately not prepended here. *)
Lemma raw_shiftedIndex_zero_successor_amount : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    amount inputIndex outputIndex,
  RawShiftedIndex M (raw_zero M) (raw_succ M amount)
    inputIndex outputIndex ->
  exists predecessorOutput : M,
    outputIndex = raw_succ M predecessorOutput /\
    RawShiftedIndex M (raw_zero M) amount inputIndex predecessorOutput.
Proof.
  intros M hPA amount inputIndex outputIndex
    [[himpossible _] | [hzeroLe houtput]].
  - exfalso. exact (raw_not_lt_zero M hPA inputIndex himpossible).
  - exists (raw_add M inputIndex amount). split.
    + rewrite houtput. apply raw_add_succ. exact hPA.
    + right. split; [exact hzeroLe | reflexivity].
Qed.

Lemma raw_lt_successors_cancel_substitution : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  rawLt M (raw_succ M left) (raw_succ M right) ->
  rawLt M left right.
Proof.
  intros M hPA left right [gap hgap]. exists gap.
  rewrite raw_succ_add_pair in hgap by exact hPA.
  exact (raw_succ_injective_syntax M hPA _ _ hgap).
Qed.

Theorem
    raw_codedFormulaShiftAssignmentLocalCompatibility_amount_prepend :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    amount sourceBound targetParentBound targetChildBound witness
    rootAssignmentCode rootAssignmentStep
    targetAssignmentCode targetAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep,
  RawCodedFormulaShiftAssignmentLocalCompatibility M
    (raw_zero M) amount sourceBound targetParentBound
    rootAssignmentCode rootAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawCodedAssignmentDefinedThrough M
    targetAssignmentCode targetAssignmentStep targetParentBound ->
  RawCodedAssignmentPrepend M
    targetAssignmentCode targetAssignmentStep witness targetParentBound
    targetChildAssignmentCode targetChildAssignmentStep ->
  rawLt M targetChildBound targetParentBound ->
  RawCodedFormulaShiftAssignmentLocalCompatibility M
    (raw_zero M) (raw_succ M amount) sourceBound targetChildBound
    rootAssignmentCode rootAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep.
Proof.
  intros M hPA amount sourceBound targetParentBound targetChildBound witness
    rootAssignmentCode rootAssignmentStep
    targetAssignmentCode targetAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep
    hcompat htargetDefined hprepend htargetChild
    inputIndex outputIndex sourceValue targetValue
    hinput houtput hshift hsourceLookup htargetLookup.
  destruct (raw_shiftedIndex_zero_successor_amount M hPA
    amount inputIndex outputIndex hshift) as
    (predecessorOutput & houtputSuccessor & holdShift).
  subst outputIndex.
  assert (hpredecessorBound :
      rawLt M predecessorOutput targetParentBound).
  {
    apply (raw_assignment_lt_trans M hPA predecessorOutput
      targetChildBound targetParentBound); [|exact htargetChild].
    exact (raw_assignment_lt_trans M hPA predecessorOutput
      (raw_succ M predecessorOutput) targetChildBound
      (raw_assignment_lt_self_succ M hPA predecessorOutput) houtput).
  }
  pose proof (proj1
    (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
      targetAssignmentCode targetAssignmentStep witness targetParentBound
      targetChildAssignmentCode targetChildAssignmentStep
      htargetDefined hprepend predecessorOutput hpredecessorBound
      targetValue) htargetLookup) as holdTargetLookup.
  exact (hcompat inputIndex predecessorOutput sourceValue targetValue
    hinput hpredecessorBound holdShift hsourceLookup holdTargetLookup).
Qed.

(** Paired prepend increments the opening cutoff.  The high-index branch is
    the subtle one: the new target lookup is itself in a prepended table, so
    its predecessor is recovered only after proving that the old index is a
    successor. *)
Theorem raw_codedFormulaSubstitutionOpeningCompatibility_prepend : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    depth replacementValue sourceParentBound targetParentBound
    sourceChildBound targetChildBound witness
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    sourceChildAssignmentCode sourceChildAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep,
  RawCodedFormulaSubstitutionOpeningCompatibility M
    depth replacementValue sourceParentBound targetParentBound
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
  RawCodedFormulaSubstitutionOpeningCompatibility M
    (raw_succ M depth) replacementValue sourceChildBound targetChildBound
    sourceChildAssignmentCode sourceChildAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep.
Proof.
  intros M hPA depth replacementValue sourceParentBound targetParentBound
    sourceChildBound targetChildBound witness
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    sourceChildAssignmentCode sourceChildAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep
    hcompat hsourceDefined htargetDefined
    hsourcePrepend htargetPrepend hsourceChild htargetChild
    inputIndex predecessor sourceValue targetValue
    hinputChild hsourceLookup.
  destruct (raw_assignment_zero_or_successor M hPA inputIndex)
    as [hzero | [oldIndex hsuccessor]].
  - subst inputIndex. split.
    + intros _ _ htargetLookup.
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
    + split.
      * intro hzeroSuccessor. exfalso.
        exact (raw_zero_not_succ_syntax M hPA depth hzeroSuccessor).
      * intro hzeroSuccessor. exfalso.
        exact (raw_zero_not_succ_syntax M hPA predecessor hzeroSuccessor).
  - subst inputIndex.
    assert (holdSourceBound : rawLt M oldIndex sourceParentBound).
    {
      apply (raw_assignment_lt_trans M hPA oldIndex
        sourceChildBound sourceParentBound); [|exact hsourceChild].
      exact (raw_assignment_lt_trans M hPA oldIndex
        (raw_succ M oldIndex) sourceChildBound
        (raw_assignment_lt_self_succ M hPA oldIndex) hinputChild).
    }
    pose proof (proj1
      (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
        sourceAssignmentCode sourceAssignmentStep witness sourceParentBound
        sourceChildAssignmentCode sourceChildAssignmentStep
        hsourceDefined hsourcePrepend oldIndex holdSourceBound sourceValue)
      hsourceLookup) as holdSourceLookup.
    destruct (hcompat oldIndex predecessor sourceValue targetValue
      holdSourceBound holdSourceLookup) as [holdLow [holdEqual holdHigh]].
    split.
    + intros hbelow htargetIndexBound htargetLookup.
      assert (holdBelow : rawLt M oldIndex depth).
      { exact (raw_lt_successors_cancel_substitution M hPA
          oldIndex depth hbelow). }
      assert (holdTargetBound : rawLt M oldIndex targetParentBound).
      {
        apply (raw_assignment_lt_trans M hPA oldIndex
          targetChildBound targetParentBound); [|exact htargetChild].
        exact (raw_assignment_lt_trans M hPA oldIndex
          (raw_succ M oldIndex) targetChildBound
          (raw_assignment_lt_self_succ M hPA oldIndex)
          htargetIndexBound).
      }
      pose proof (proj1
        (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
          targetAssignmentCode targetAssignmentStep witness
          targetParentBound
          targetChildAssignmentCode targetChildAssignmentStep
          htargetDefined htargetPrepend oldIndex holdTargetBound targetValue)
        htargetLookup) as holdTargetLookup.
      exact (holdLow holdBelow holdTargetBound holdTargetLookup).
    + split.
      * intro hequal.
        apply (raw_succ_injective_syntax M hPA) in hequal.
        exact (holdEqual hequal).
      * intros hpredecessor habove hpredecessorBound htargetLookup.
        apply (raw_succ_injective_syntax M hPA) in hpredecessor.
        subst predecessor.
        assert (holdAbove : rawLt M depth oldIndex).
        { exact (raw_lt_successors_cancel_substitution M hPA
            depth oldIndex habove). }
        destruct (raw_assignment_zero_or_successor M hPA oldIndex)
          as [holdZero | [oldPredecessor holdSuccessor]].
        { subst oldIndex. exfalso.
          exact (raw_not_lt_zero M hPA depth holdAbove). }
        subst oldIndex.
        assert (holdPredecessorBound :
            rawLt M oldPredecessor targetParentBound).
        {
          apply (raw_assignment_lt_trans M hPA oldPredecessor
            targetChildBound targetParentBound); [|exact htargetChild].
          exact (raw_assignment_lt_trans M hPA oldPredecessor
            (raw_succ M oldPredecessor) targetChildBound
            (raw_assignment_lt_self_succ M hPA oldPredecessor)
            hpredecessorBound).
        }
        pose proof (proj1
          (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
            targetAssignmentCode targetAssignmentStep witness
            targetParentBound
            targetChildAssignmentCode targetChildAssignmentStep
            htargetDefined htargetPrepend oldPredecessor
            holdPredecessorBound targetValue) htargetLookup)
          as holdTargetLookup.
        destruct (hcompat (raw_succ M oldPredecessor) oldPredecessor
          sourceValue targetValue holdSourceBound holdSourceLookup)
          as [_ [_ holdParentHigh]].
        exact (holdParentHigh eq_refl holdAbove
          holdPredecessorBound holdTargetLookup).
Qed.

(** The table induction consumes the two preceding relations together.  The
    root target assignment remains fixed in the first component, while the
    current source and target assignments evolve under binders. *)
Definition codedFormulaSubstitutionBinderCompatibilityTermAt
    (replacement replacementValue depth sourceBound targetBound
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  pAnd
    (codedFormulaShiftAssignmentLocalCompatibilityTermAt
      tZero depth (tSucc replacement) targetBound
      rootTargetAssignmentCode rootTargetAssignmentStep
      targetAssignmentCode targetAssignmentStep)
    (codedFormulaSubstitutionOpeningCompatibilityTermAt
      depth replacementValue sourceBound targetBound
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep).

Definition RawCodedFormulaSubstitutionBinderCompatibility
    (M : RawPAModel)
    (replacement replacementValue depth sourceBound targetBound
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  RawCodedFormulaShiftAssignmentLocalCompatibility M
    (raw_zero M) depth (raw_succ M replacement) targetBound
    rootTargetAssignmentCode rootTargetAssignmentStep
    targetAssignmentCode targetAssignmentStep /\
  RawCodedFormulaSubstitutionOpeningCompatibility M
    depth replacementValue sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.

Arguments RawCodedFormulaSubstitutionBinderCompatibility
  M replacement replacementValue depth sourceBound targetBound
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_sat_codedFormulaSubstitutionBinderCompatibilityTermAt_iff :
  forall (M : RawPAModel) e
    replacement replacementValue depth sourceBound targetBound
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (codedFormulaSubstitutionBinderCompatibilityTermAt
      replacement replacementValue depth sourceBound targetBound
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawCodedFormulaSubstitutionBinderCompatibility M
    (raw_term_eval M e replacement)
    (raw_term_eval M e replacementValue)
    (raw_term_eval M e depth)
    (raw_term_eval M e sourceBound) (raw_term_eval M e targetBound)
    (raw_term_eval M e rootTargetAssignmentCode)
    (raw_term_eval M e rootTargetAssignmentStep)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold codedFormulaSubstitutionBinderCompatibilityTermAt,
    RawCodedFormulaSubstitutionBinderCompatibility.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedFormulaShiftAssignmentLocalCompatibilityTermAt_iff,
    raw_sat_codedFormulaSubstitutionOpeningCompatibilityTermAt_iff.
  reflexivity.
Qed.

Lemma raw_codedFormulaSubstitutionBinderCompatibility_restrict : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacement replacementValue depth
    sourceParentBound targetParentBound sourceChildBound targetChildBound
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaSubstitutionBinderCompatibility M
    replacement replacementValue depth sourceParentBound targetParentBound
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  rawLt M sourceChildBound sourceParentBound ->
  rawLt M targetChildBound targetParentBound ->
  RawCodedFormulaSubstitutionBinderCompatibility M
    replacement replacementValue depth sourceChildBound targetChildBound
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA replacement replacementValue depth
    sourceParentBound targetParentBound sourceChildBound targetChildBound
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    [hreplacement hopening] hsourceChild htargetChild.
  split.
  - exact
      (raw_codedFormulaShiftAssignmentLocalCompatibility_target_restrict
        M hPA (raw_zero M) depth (raw_succ M replacement)
        targetParentBound targetChildBound
        rootTargetAssignmentCode rootTargetAssignmentStep
        targetAssignmentCode targetAssignmentStep
        hreplacement htargetChild).
  - exact (raw_codedFormulaSubstitutionOpeningCompatibility_restrict M hPA
      depth replacementValue sourceParentBound targetParentBound
      sourceChildBound targetChildBound
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      hopening hsourceChild htargetChild).
Qed.

Theorem raw_codedFormulaSubstitutionBinderCompatibility_prepend : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacement replacementValue depth
    sourceParentBound targetParentBound sourceChildBound targetChildBound
    witness rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    sourceChildAssignmentCode sourceChildAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep,
  RawCodedFormulaSubstitutionBinderCompatibility M
    replacement replacementValue depth sourceParentBound targetParentBound
    rootTargetAssignmentCode rootTargetAssignmentStep
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
  RawCodedFormulaSubstitutionBinderCompatibility M
    replacement replacementValue (raw_succ M depth)
    sourceChildBound targetChildBound
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceChildAssignmentCode sourceChildAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep.
Proof.
  intros M hPA replacement replacementValue depth
    sourceParentBound targetParentBound sourceChildBound targetChildBound
    witness rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    sourceChildAssignmentCode sourceChildAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep
    [hreplacement hopening] hsourceDefined htargetDefined
    hsourcePrepend htargetPrepend hsourceChild htargetChild.
  split.
  - exact
      (raw_codedFormulaShiftAssignmentLocalCompatibility_amount_prepend
        M hPA depth (raw_succ M replacement)
        targetParentBound targetChildBound witness
        rootTargetAssignmentCode rootTargetAssignmentStep
        targetAssignmentCode targetAssignmentStep
        targetChildAssignmentCode targetChildAssignmentStep
        hreplacement htargetDefined htargetPrepend htargetChild).
  - exact
      (raw_codedFormulaSubstitutionOpeningCompatibility_prepend M hPA
        depth replacementValue sourceParentBound targetParentBound
        sourceChildBound targetChildBound witness
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        sourceChildAssignmentCode sourceChildAssignmentStep
        targetChildAssignmentCode targetChildAssignmentStep
        hopening hsourceDefined htargetDefined
        hsourcePrepend htargetPrepend hsourceChild htargetChild).
Qed.

Lemma raw_codedFormulaSubstitutionBinderCompatibility_root : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacement replacementValue source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedAssignmentPrepend M
    targetAssignmentCode targetAssignmentStep replacementValue source
    sourceAssignmentCode sourceAssignmentStep ->
  RawCodedFormulaSubstitutionBinderCompatibility M
    replacement replacementValue (raw_zero M) source target
    targetAssignmentCode targetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA replacement replacementValue source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hprepend.
  split.
  - apply (raw_codedFormulaShiftAssignmentRelation_local M hPA
      (raw_zero M) (raw_zero M) (raw_succ M replacement) target
      targetAssignmentCode targetAssignmentStep
      targetAssignmentCode targetAssignmentStep).
    apply raw_codedFormulaZeroShiftAssignmentRelation_refl. exact hPA.
  - exact (raw_codedFormulaSubstitutionOpeningCompatibility_root M hPA
      replacementValue source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep hprepend).
Qed.

(** ------------------------------------------------------------------
    Atomic substitution evaluation under the represented invariant. *)

Lemma raw_formulaSubstitutionOpeningVariableEvaluationBiCompatible : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacement liftedReplacement replacementValue depth
    sourceBound targetBound
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedTermShift M (raw_zero M) depth
    replacement liftedReplacement ->
  RawTermEvaluationCertificate M replacement replacementValue
    rootTargetAssignmentCode rootTargetAssignmentStep ->
  RawCodedFormulaShiftAssignmentLocalCompatibility M
    (raw_zero M) depth (raw_succ M replacement) targetBound
    rootTargetAssignmentCode rootTargetAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawCodedFormulaSubstitutionOpeningCompatibility M
    depth replacementValue sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawTermOperationVariableEvaluationBiCompatible M
    (RawCodedTermOpeningVariableRow M depth liftedReplacement)
    sourceBound targetBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA replacement liftedReplacement replacementValue depth
    sourceBound targetBound
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hreplacementShift hreplacementEvaluation
    hreplacementCompatibility hopeningCompatibility
    input output sourceValue targetValue
    (inputIndex & hinput & hcases)
    hinputBound houtputBound hsourceEvaluation htargetEvaluation.
  subst input.
  assert (hinputIndexBound : rawLt M inputIndex sourceBound).
  {
    apply (raw_assignment_lt_trans M hPA inputIndex
      (rawTermVarCode M inputIndex) sourceBound); [|exact hinputBound].
    change (rawLt M inputIndex
      (rawListCode M [rawNumeralValue M 0; inputIndex])).
    apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
  }
  pose proof (raw_termEvaluationCertificate_var_view M hPA
    inputIndex sourceValue sourceAssignmentCode sourceAssignmentStep
    hsourceEvaluation) as hsourceLookup.
  destruct hcases as
    [[hbelow houtput] | [[hequal houtput] |
      (predecessor & hsuccessor & habove & houtput)]].
  - subst output.
    assert (houtputIndexBound : rawLt M inputIndex targetBound).
    {
      apply (raw_assignment_lt_trans M hPA inputIndex
        (rawTermVarCode M inputIndex) targetBound); [|exact houtputBound].
      change (rawLt M inputIndex
        (rawListCode M [rawNumeralValue M 0; inputIndex])).
      apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
    }
    pose proof (raw_termEvaluationCertificate_var_view M hPA
      inputIndex targetValue targetAssignmentCode targetAssignmentStep
      htargetEvaluation) as htargetLookup.
    destruct (hopeningCompatibility inputIndex inputIndex
      sourceValue targetValue hinputIndexBound hsourceLookup)
      as [hlow _].
    exact (hlow hbelow houtputIndexBound htargetLookup).
  - subst inputIndex. subst output.
    destruct (hopeningCompatibility depth depth sourceValue targetValue
      hinputIndexBound hsourceLookup) as [_ [hequalValue _]].
    pose proof (hequalValue eq_refl) as hsourceValue.
    subst sourceValue.
    apply (raw_codedTermShift_evaluation_values_agree_local M hPA
      (raw_zero M) depth (raw_succ M replacement) targetBound
      replacement liftedReplacement
      rootTargetAssignmentCode rootTargetAssignmentStep
      targetAssignmentCode targetAssignmentStep
      hreplacementShift hreplacementCompatibility).
    + exact (raw_assignment_lt_self_succ M hPA replacement).
    + exact houtputBound.
    + exact hreplacementEvaluation.
    + exact htargetEvaluation.
  - subst inputIndex. subst output.
    assert (hpredecessorBound : rawLt M predecessor targetBound).
    {
      apply (raw_assignment_lt_trans M hPA predecessor
        (rawTermVarCode M predecessor) targetBound); [|exact houtputBound].
      change (rawLt M predecessor
        (rawListCode M [rawNumeralValue M 0; predecessor])).
      apply rawProofListCode_member_lt; [exact hPA |]. simpl. tauto.
    }
    pose proof (raw_termEvaluationCertificate_var_view M hPA
      predecessor targetValue targetAssignmentCode targetAssignmentStep
      htargetEvaluation) as htargetLookup.
    destruct (hopeningCompatibility (raw_succ M predecessor) predecessor
      sourceValue targetValue hinputIndexBound hsourceLookup)
      as [_ [_ hhigh]].
    exact (hhigh eq_refl habove hpredecessorBound htargetLookup).
Qed.

Theorem raw_codedTermOpening_evaluation_values_agree_local : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacement liftedReplacement replacementValue depth
    sourceBound targetBound input output
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedTermOpening M depth liftedReplacement input output ->
  RawCodedTermShift M (raw_zero M) depth
    replacement liftedReplacement ->
  RawTermEvaluationCertificate M replacement replacementValue
    rootTargetAssignmentCode rootTargetAssignmentStep ->
  RawCodedFormulaShiftAssignmentLocalCompatibility M
    (raw_zero M) depth (raw_succ M replacement) targetBound
    rootTargetAssignmentCode rootTargetAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawCodedFormulaSubstitutionOpeningCompatibility M
    depth replacementValue sourceBound targetBound
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
  intros M hPA replacement liftedReplacement replacementValue depth
    sourceBound targetBound input output
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace)
    hreplacementShift hreplacementEvaluation
    hreplacementCompatibility hopeningCompatibility
    hinputBound houtputBound sourceValue targetValue
    hsourceEvaluation htargetEvaluation.
  destruct htrace as
    (hsourceDefined & htargetDefined & hroot & hrootLookup & hrows).
  exact (raw_termOperationTrace_evaluation_values_agree_local M hPA
    (RawCodedTermOpeningVariableRow M depth liftedReplacement)
    sourceBound targetBound sourceCode sourceStep targetCode targetStep
    bound rootIndex input output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsourceDefined htargetDefined hroot hrootLookup hrows
    (raw_formulaSubstitutionOpeningVariableEvaluationBiCompatible M hPA
      replacement liftedReplacement replacementValue depth
      sourceBound targetBound
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      hreplacementShift hreplacementEvaluation
      hreplacementCompatibility hopeningCompatibility)
    sourceValue targetValue hinputBound houtputBound
    hsourceEvaluation htargetEvaluation).
Qed.

Theorem
    raw_formulaSubstitutionEqOperationRow_rankZero_outputs_agree_local :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    replacement replacementValue depth source target
    sourceOutput targetOutput
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaEqOperationRow M (RawCodedFormulaSubstitutionAtom M)
    replacement depth source target ->
  RawTermEvaluationCertificate M replacement replacementValue
    rootTargetAssignmentCode rootTargetAssignmentStep ->
  RawCodedFormulaShiftAssignmentLocalCompatibility M
    (raw_zero M) depth (raw_succ M replacement) target
    rootTargetAssignmentCode rootTargetAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawCodedFormulaSubstitutionOpeningCompatibility M
    depth replacementValue source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawRankZeroTruthCertificate M source sourceOutput
    sourceAssignmentCode sourceAssignmentStep ->
  RawRankZeroTruthCertificate M target targetOutput
    targetAssignmentCode targetAssignmentStep ->
  sourceOutput = targetOutput.
Proof.
  intros M hPA replacement replacementValue depth source target
    sourceOutput targetOutput
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (sourceLeft & targetLeft & sourceRight & targetRight &
     hsource & htarget &
     (liftedLeft & hleftShift & hleftOpen) &
     (liftedRight & hrightShift & hrightOpen))
    hreplacementEvaluation hreplacementCompatibility
    hopeningCompatibility hsourceCertificate htargetCertificate.
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
    apply (raw_codedTermOpening_evaluation_values_agree_local M hPA
      replacement liftedLeft replacementValue depth
      source target sourceLeft targetLeft
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      hleftOpen hleftShift hreplacementEvaluation
      hreplacementCompatibility hopeningCompatibility).
    - rewrite hsource. apply raw_formulaEq_left_lt. exact hPA.
    - rewrite htarget. apply raw_formulaEq_left_lt. exact hPA.
    - exact hsourceLeft.
    - exact htargetLeft.
  }
  assert (hrightValue : sourceRightValue = targetRightValue).
  {
    apply (raw_codedTermOpening_evaluation_values_agree_local M hPA
      replacement liftedRight replacementValue depth
      source target sourceRight targetRight
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      hrightOpen hrightShift hreplacementEvaluation
      hreplacementCompatibility hopeningCompatibility).
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

Lemma raw_eq_scheduled_transport_of_rankZero_outputs_agree : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
    sourceLeft sourceRight targetLeft targetRight source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  source = rawFormulaEqCode M sourceLeft sourceRight ->
  target = rawFormulaEqCode M targetLeft targetRight ->
  (forall sourceOutput targetOutput,
    RawRankZeroTruthCertificate M source sourceOutput
      sourceAssignmentCode sourceAssignmentStep ->
    RawRankZeroTruthCertificate M target targetOutput
      targetAssignmentCode targetAssignmentStep ->
    sourceOutput = targetOutput) ->
  RawFixedLevelTruthAdmissible M inputLevel
    source sourceAssignmentCode sourceAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    target targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA inputLevel sourceLeft sourceRight targetLeft targetRight
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsource htarget hagreement hsourceAdmissible htargetAdmissible.
  apply (raw_scheduledTruthCertificateTransport_of_sigma_iff M hPA
    inputLevel source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hsourceAdmissible htargetAdmissible).
  split.
  - intro hsourceSigma.
    destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
      inputLevel M hPA target targetAssignmentCode targetAssignmentStep
      htargetAdmissible) as [htargetSigma | htargetPi]; [exact htargetSigma |].
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
    pose proof (hagreement (rawNumeralValue M 1) (raw_zero M)
      hsourceZero htargetZero) as hone.
    exact (False_rect _ (raw_zero_neq_truthOne M hPA (eq_sym hone))).
  - intro htargetSigma.
    destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
      inputLevel M hPA source sourceAssignmentCode sourceAssignmentStep
      hsourceAdmissible) as [hsourceSigma | hsourcePi]; [exact hsourceSigma |].
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
    pose proof (hagreement (raw_zero M) (rawNumeralValue M 1)
      hsourceZero htargetZero) as hzero.
    exact (False_rect _ (raw_zero_neq_truthOne M hPA hzero)).
Qed.

Lemma raw_formulaSubstitutionEqOperationRow_scheduled_transport : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
    replacement replacementValue depth source target
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaEqOperationRow M (RawCodedFormulaSubstitutionAtom M)
    replacement depth source target ->
  RawTermEvaluationCertificate M replacement replacementValue
    rootTargetAssignmentCode rootTargetAssignmentStep ->
  RawCodedFormulaShiftAssignmentLocalCompatibility M
    (raw_zero M) depth (raw_succ M replacement) target
    rootTargetAssignmentCode rootTargetAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawCodedFormulaSubstitutionOpeningCompatibility M
    depth replacementValue source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    source sourceAssignmentCode sourceAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    target targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA inputLevel replacement replacementValue depth source target
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep heq
    hreplacementEvaluation hreplacementCompatibility
    hopeningCompatibility hsourceAdmissible htargetAdmissible.
  destruct heq as
    (sourceLeft & targetLeft & sourceRight & targetRight &
     hsource & htarget & hleft & hright).
  apply (raw_eq_scheduled_transport_of_rankZero_outputs_agree M hPA
    inputLevel sourceLeft sourceRight targetLeft targetRight source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hsource htarget).
  - intros sourceOutput targetOutput hsourceZero htargetZero.
    apply
      (raw_formulaSubstitutionEqOperationRow_rankZero_outputs_agree_local
        M hPA replacement replacementValue depth source target
        sourceOutput targetOutput
        rootTargetAssignmentCode rootTargetAssignmentStep
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep).
    + exists sourceLeft, targetLeft, sourceRight, targetRight.
      repeat split; assumption.
    + exact hreplacementEvaluation.
    + exact hreplacementCompatibility.
    + exact hopeningCompatibility.
    + exact hsourceZero.
    + exact htargetZero.
  - exact hsourceAdmissible.
  - exact htargetAdmissible.
Qed.

(** ------------------------------------------------------------------
    Represented substitution-table transport. *)

Definition formulaSubstitutionScheduledTransportBelowTermAt
    (inputLevel : nat)
    (current replacement replacementValue sourceRoot targetRoot
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceCode sourceStep targetCode targetStep depthCode depthStep : term)
    : formula :=
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
              (codedFormulaSubstitutionBinderCompatibilityTermAt
                (liftTerm 8 replacement) (liftTerm 8 replacementValue)
                (tVar 4) (tVar 6) (tVar 5)
                (liftTerm 8 rootTargetAssignmentCode)
                (liftTerm 8 rootTargetAssignmentStep)
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

Definition RawFormulaSubstitutionScheduledTransportBelow
    (M : RawPAModel) (inputLevel : nat)
    (current replacement replacementValue sourceRoot targetRoot
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceCode sourceStep targetCode targetStep depthCode depthStep : M)
    : Prop :=
  forall index input output depth
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M,
    rawLt M index current ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth ->
    rawLt M input sourceRoot ->
    rawLt M output targetRoot ->
    RawCodedFormulaSubstitutionBinderCompatibility M
      replacement replacementValue depth input output
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep ->
    RawFixedLevelTruthAdmissible M inputLevel
      input sourceAssignmentCode sourceAssignmentStep ->
    RawFixedLevelTruthAdmissible M inputLevel
      output targetAssignmentCode targetAssignmentStep ->
    RawFixedLevelTruthCertificateTransport M (S inputLevel)
      input output sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep.

Arguments RawFormulaSubstitutionScheduledTransportBelow
  M inputLevel current replacement replacementValue sourceRoot targetRoot
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceCode sourceStep targetCode targetStep depthCode depthStep
  : clear implicits.

Lemma raw_sat_formulaSubstitutionScheduledTransportBelowTermAt_iff : forall
    (M : RawPAModel) e inputLevel
    current replacement replacementValue sourceRoot targetRoot
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceCode sourceStep targetCode targetStep depthCode depthStep,
  raw_formula_sat M e
    (formulaSubstitutionScheduledTransportBelowTermAt inputLevel
      current replacement replacementValue sourceRoot targetRoot
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceCode sourceStep targetCode targetStep depthCode depthStep) <->
  RawFormulaSubstitutionScheduledTransportBelow M inputLevel
    (raw_term_eval M e current) (raw_term_eval M e replacement)
    (raw_term_eval M e replacementValue)
    (raw_term_eval M e sourceRoot) (raw_term_eval M e targetRoot)
    (raw_term_eval M e rootTargetAssignmentCode)
    (raw_term_eval M e rootTargetAssignmentStep)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep).
Proof.
  intros. unfold formulaSubstitutionScheduledTransportBelowTermAt,
    operationTarskiPositiveAll8,
    RawFormulaSubstitutionScheduledTransportBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaOperationTripleLookupTermAt_iff.
  setoid_rewrite
    raw_sat_codedFormulaSubstitutionBinderCompatibilityTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelTruthAdmissibleTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelTruthCertificateTransportTermAt_iff.
  repeat setoid_rewrite raw_operationTarskiPositive_eval_liftTerm_eight.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The following thin wrappers deliberately match the arities used by the
    already-audited shift successor proof.  Here its [cutoff] slot is the
    substitution depth and its [amount] slot is the replacement code.  This
    lets the logical seven-constructor argument remain visibly identical,
    while the wrapper expands to the richer substitution environment. *)
(** A monomorphic wrapper is convenient inside one arbitrary model. *)
Definition RawFormulaSubstitutionScheduledCompatibilityAt
    (M : RawPAModel)
    (replacementValue rootTargetAssignmentCode rootTargetAssignmentStep
      depth replacement sourceBound targetBound
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  RawCodedFormulaSubstitutionBinderCompatibility M
    replacement replacementValue depth sourceBound targetBound
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.

Lemma raw_formulaSubstitutionScheduledCompatibilityAt_restrict : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacementValue rootTargetAssignmentCode rootTargetAssignmentStep
    depth replacement sourceParentBound targetParentBound
    sourceChildBound targetChildBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawFormulaSubstitutionScheduledCompatibilityAt M
    replacementValue rootTargetAssignmentCode rootTargetAssignmentStep
    depth replacement sourceParentBound targetParentBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  rawLt M sourceChildBound sourceParentBound ->
  rawLt M targetChildBound targetParentBound ->
  RawFormulaSubstitutionScheduledCompatibilityAt M
    replacementValue rootTargetAssignmentCode rootTargetAssignmentStep
    depth replacement sourceChildBound targetChildBound
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros. unfold RawFormulaSubstitutionScheduledCompatibilityAt in *.
  eapply raw_codedFormulaSubstitutionBinderCompatibility_restrict;
    eassumption.
Qed.

Lemma raw_formulaSubstitutionScheduledCompatibilityAt_prepend : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacementValue rootTargetAssignmentCode rootTargetAssignmentStep
    depth replacement sourceParentBound targetParentBound
    sourceChildBound targetChildBound witness
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    sourceChildAssignmentCode sourceChildAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep,
  RawFormulaSubstitutionScheduledCompatibilityAt M
    replacementValue rootTargetAssignmentCode rootTargetAssignmentStep
    depth replacement sourceParentBound targetParentBound
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
  RawFormulaSubstitutionScheduledCompatibilityAt M
    replacementValue rootTargetAssignmentCode rootTargetAssignmentStep
    (raw_succ M depth) replacement sourceChildBound targetChildBound
    sourceChildAssignmentCode sourceChildAssignmentStep
    targetChildAssignmentCode targetChildAssignmentStep.
Proof.
  intros. unfold RawFormulaSubstitutionScheduledCompatibilityAt in *.
  eapply raw_codedFormulaSubstitutionBinderCompatibility_prepend;
    eassumption.
Qed.

Definition RawFormulaSubstitutionScheduledTransportBelowAt
    (M : RawPAModel)
    (replacementValue rootTargetAssignmentCode rootTargetAssignmentStep : M)
    (inputLevel : nat)
    (current replacement sourceRoot targetRoot sourceCode sourceStep
      targetCode targetStep depthCode depthStep : M) : Prop :=
  RawFormulaSubstitutionScheduledTransportBelow M inputLevel
    current replacement replacementValue sourceRoot targetRoot
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceCode sourceStep targetCode targetStep depthCode depthStep.

Lemma raw_formulaSubstitutionScheduledTransportBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacementValue rootTargetAssignmentCode rootTargetAssignmentStep
    inputLevel replacement sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound current,
  RawCodedFormulaOperationRows M (RawCodedFormulaSubstitutionAtom M)
    replacement sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound ->
  RawTermEvaluationCertificate M replacement replacementValue
    rootTargetAssignmentCode rootTargetAssignmentStep ->
  rawLt M current bound ->
  RawFormulaSubstitutionScheduledTransportBelowAt M
    replacementValue rootTargetAssignmentCode rootTargetAssignmentStep
    inputLevel current replacement sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep ->
  RawFormulaSubstitutionScheduledTransportBelowAt M
    replacementValue rootTargetAssignmentCode rootTargetAssignmentStep
    inputLevel (raw_succ M current) replacement sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep.
Proof.
  intros M hPA replacementValue rootTargetAssignmentCode
    rootTargetAssignmentStep inputLevel amount sourceRoot targetRoot
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound current hrows hreplacementEvaluation hcurrent hagree
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
    + destruct hcompat as
        [hreplacementCompatibility hopeningCompatibility].
      exact (raw_formulaSubstitutionEqOperationRow_scheduled_transport M hPA
        inputLevel amount replacementValue depth input output
        rootTargetAssignmentCode rootTargetAssignmentStep
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep
        heq hreplacementEvaluation hreplacementCompatibility
        hopeningCompatibility hsourceAdmissible htargetAdmissible).
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
          RawFormulaSubstitutionScheduledCompatibilityAt M
            replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep leftDepth amount
            inputLeft outputLeft
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep).
      {
        rewrite hleftDepth.
        exact (raw_formulaSubstitutionScheduledCompatibilityAt_restrict
          M hPA replacementValue rootTargetAssignmentCode
          rootTargetAssignmentStep depth amount
          (rawFormulaImpCode M inputLeft inputRight)
          (rawFormulaImpCode M outputLeft outputRight)
          inputLeft outputLeft
          sourceAssignmentCode sourceAssignmentStep
          targetAssignmentCode targetAssignmentStep
          hcompat hsourceLeftParent htargetLeftParent).
      }
      assert (hrightCompat :
          RawFormulaSubstitutionScheduledCompatibilityAt M
            replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep rightDepth amount
            inputRight outputRight
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep).
      {
        rewrite hrightDepth.
        exact (raw_formulaSubstitutionScheduledCompatibilityAt_restrict
          M hPA replacementValue rootTargetAssignmentCode
          rootTargetAssignmentStep depth amount
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
          RawFormulaSubstitutionScheduledCompatibilityAt M
            replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep leftDepth amount
            inputLeft outputLeft
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep).
      {
        rewrite hleftDepth.
        exact (raw_formulaSubstitutionScheduledCompatibilityAt_restrict
          M hPA replacementValue rootTargetAssignmentCode
          rootTargetAssignmentStep depth amount
          (rawFormulaAndCode M inputLeft inputRight)
          (rawFormulaAndCode M outputLeft outputRight)
          inputLeft outputLeft
          sourceAssignmentCode sourceAssignmentStep
          targetAssignmentCode targetAssignmentStep
          hcompat hsourceLeftParent htargetLeftParent).
      }
      assert (hrightCompat :
          RawFormulaSubstitutionScheduledCompatibilityAt M
            replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep rightDepth amount
            inputRight outputRight
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep).
      {
        rewrite hrightDepth.
        exact (raw_formulaSubstitutionScheduledCompatibilityAt_restrict
          M hPA replacementValue rootTargetAssignmentCode
          rootTargetAssignmentStep depth amount
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
          RawFormulaSubstitutionScheduledCompatibilityAt M
            replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep leftDepth amount
            inputLeft outputLeft
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep).
      {
        rewrite hleftDepth.
        exact (raw_formulaSubstitutionScheduledCompatibilityAt_restrict
          M hPA replacementValue rootTargetAssignmentCode
          rootTargetAssignmentStep depth amount
          (rawFormulaOrCode M inputLeft inputRight)
          (rawFormulaOrCode M outputLeft outputRight)
          inputLeft outputLeft
          sourceAssignmentCode sourceAssignmentStep
          targetAssignmentCode targetAssignmentStep
          hcompat hsourceLeftParent htargetLeftParent).
      }
      assert (hrightCompat :
          RawFormulaSubstitutionScheduledCompatibilityAt M
            replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep rightDepth amount
            inputRight outputRight
            sourceAssignmentCode sourceAssignmentStep
            targetAssignmentCode targetAssignmentStep).
      {
        rewrite hrightDepth.
        exact (raw_formulaSubstitutionScheduledCompatibilityAt_restrict
          M hPA replacementValue rootTargetAssignmentCode
          rootTargetAssignmentStep depth amount
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
          RawFormulaSubstitutionScheduledCompatibilityAt M
            replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep childDepth amount
            inputChild outputChild
            sourceChildAssignmentCode sourceChildAssignmentStep
            targetChildAssignmentCode targetChildAssignmentStep).
        {
          rewrite hchildDepth.
          apply (raw_formulaSubstitutionScheduledCompatibilityAt_prepend
            M hPA replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep depth amount
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
          RawFormulaSubstitutionScheduledCompatibilityAt M
            replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep childDepth amount
            inputChild outputChild
            sourceChildAssignmentCode sourceChildAssignmentStep
            targetChildAssignmentCode targetChildAssignmentStep).
        {
          rewrite hchildDepth.
          apply (raw_formulaSubstitutionScheduledCompatibilityAt_prepend
            M hPA replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep depth amount
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
          RawFormulaSubstitutionScheduledCompatibilityAt M
            replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep childDepth amount
            inputChild outputChild
            sourceChildAssignmentCode sourceChildAssignmentStep
            targetChildAssignmentCode targetChildAssignmentStep).
        {
          rewrite hchildDepth.
          apply (raw_formulaSubstitutionScheduledCompatibilityAt_prepend
            M hPA replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep depth amount
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
          RawFormulaSubstitutionScheduledCompatibilityAt M
            replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep childDepth amount
            inputChild outputChild
            sourceChildAssignmentCode sourceChildAssignmentStep
            targetChildAssignmentCode targetChildAssignmentStep).
        {
          rewrite hchildDepth.
          apply (raw_formulaSubstitutionScheduledCompatibilityAt_prepend
            M hPA replacementValue rootTargetAssignmentCode
            rootTargetAssignmentStep depth amount
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

Definition formulaSubstitutionScheduledTransportThroughTermAt
    (inputLevel : nat)
    (current limit replacement replacementValue sourceRoot targetRoot
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceCode sourceStep targetCode targetStep depthCode depthStep : term)
    : formula :=
  pImp (Formula.leTermAt current limit)
    (formulaSubstitutionScheduledTransportBelowTermAt inputLevel
      current replacement replacementValue sourceRoot targetRoot
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceCode sourceStep targetCode targetStep depthCode depthStep).

Definition RawFormulaSubstitutionScheduledTransportThrough
    (M : RawPAModel) (inputLevel : nat)
    (current limit replacement replacementValue sourceRoot targetRoot
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceCode sourceStep targetCode targetStep depthCode depthStep : M)
    : Prop :=
  rawLe M current limit ->
  RawFormulaSubstitutionScheduledTransportBelow M inputLevel
    current replacement replacementValue sourceRoot targetRoot
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceCode sourceStep targetCode targetStep depthCode depthStep.

Lemma raw_sat_formulaSubstitutionScheduledTransportThroughTermAt_iff : forall
    (M : RawPAModel) e inputLevel
    current limit replacement replacementValue sourceRoot targetRoot
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceCode sourceStep targetCode targetStep depthCode depthStep,
  raw_formula_sat M e
    (formulaSubstitutionScheduledTransportThroughTermAt inputLevel
      current limit replacement replacementValue sourceRoot targetRoot
      rootTargetAssignmentCode rootTargetAssignmentStep
      sourceCode sourceStep targetCode targetStep depthCode depthStep) <->
  RawFormulaSubstitutionScheduledTransportThrough M inputLevel
    (raw_term_eval M e current) (raw_term_eval M e limit)
    (raw_term_eval M e replacement)
    (raw_term_eval M e replacementValue)
    (raw_term_eval M e sourceRoot) (raw_term_eval M e targetRoot)
    (raw_term_eval M e rootTargetAssignmentCode)
    (raw_term_eval M e rootTargetAssignmentStep)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep).
Proof.
  intros. unfold formulaSubstitutionScheduledTransportThroughTermAt,
    RawFormulaSubstitutionScheduledTransportThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_traversal,
    raw_sat_formulaSubstitutionScheduledTransportBelowTermAt_iff.
  tauto.
Qed.

Theorem raw_formulaSubstitutionScheduledTransportBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
    replacement replacementValue sourceRoot targetRoot
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound,
  RawCodedFormulaOperationRows M (RawCodedFormulaSubstitutionAtom M)
    replacement sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound ->
  RawTermEvaluationCertificate M replacement replacementValue
    rootTargetAssignmentCode rootTargetAssignmentStep ->
  RawFormulaSubstitutionScheduledTransportBelow M inputLevel
    bound replacement replacementValue sourceRoot targetRoot
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceCode sourceStep targetCode targetStep depthCode depthStep.
Proof.
  intros M hPA inputLevel replacement replacementValue sourceRoot targetRoot
    rootTargetAssignmentCode rootTargetAssignmentStep
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound hrows hreplacementEvaluation.
  set (parameterEnv := scons M bound
    (scons M replacement (scons M replacementValue
      (scons M sourceRoot (scons M targetRoot
        (scons M rootTargetAssignmentCode
          (scons M rootTargetAssignmentStep
            (scons M sourceCode (scons M sourceStep
              (scons M targetCode (scons M targetStep
                (scons M depthCode (scons M depthStep
                  (fun _ : nat => raw_zero M)))))))))))))).
  set (phi := formulaSubstitutionScheduledTransportThroughTermAt inputLevel
    (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
    (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11)
    (tVar 12) (tVar 13)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_formulaSubstitutionScheduledTransportThroughTermAt_iff M
          (scons M (raw_zero M) parameterEnv) inputLevel
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11)
          (tVar 12) (tVar 13))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _ index input output depth
        sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep hindex.
      exfalso. exact (raw_not_lt_zero M hPA index hindex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_formulaSubstitutionScheduledTransportThroughTermAt_iff M
          (scons M current parameterEnv) inputLevel
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11)
          (tVar 12) (tVar 13)) hcurrent) as hcurrentRaw.
      apply (proj2
        (raw_sat_formulaSubstitutionScheduledTransportThroughTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) inputLevel
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11)
          (tVar 12) (tVar 13))).
      unfold parameterEnv in hcurrentRaw |- *.
      cbn [raw_term_eval scons] in hcurrentRaw |- *.
      intro hsuccLe.
      assert (hcurrentBound : rawLt M current bound).
      { exact (raw_lt_of_succ_le_traversal M hPA current bound hsuccLe). }
      exact (raw_formulaSubstitutionScheduledTransportBelow_succ M hPA
        replacementValue rootTargetAssignmentCode rootTargetAssignmentStep
        inputLevel replacement sourceRoot targetRoot
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound current hrows hreplacementEvaluation hcurrentBound
        (hcurrentRaw (raw_lt_to_le M current bound hcurrentBound))).
  }
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_formulaSubstitutionScheduledTransportThroughTermAt_iff M
      (scons M bound parameterEnv) inputLevel
      (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
      (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11)
      (tVar 12) (tVar 13)) (hall bound)) as hbound.
  unfold parameterEnv in hbound. cbn [raw_term_eval scons] in hbound.
  exact (hbound (raw_le_refl_traversal M hPA bound)).
Qed.

Theorem raw_formulaSubstitutionOperationTrace_scheduled_transport : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
    replacement replacementValue source target
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaOperationTrace M (RawCodedFormulaSubstitutionAtom M)
    replacement (raw_zero M)
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex source target ->
  RawTermEvaluationCertificate M replacement replacementValue
    targetAssignmentCode targetAssignmentStep ->
  RawCodedFormulaSubstitutionBinderCompatibility M
    replacement replacementValue (raw_zero M) source target
    targetAssignmentCode targetAssignmentStep
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    source sourceAssignmentCode sourceAssignmentStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    target targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA inputLevel replacement replacementValue source target
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    (_ & _ & _ & hroot & hrootLookup & hrows)
    hreplacementEvaluation hcompat hsource htarget.
  pose proof (raw_formulaSubstitutionScheduledTransportBelow_all M hPA
    inputLevel replacement replacementValue
    (raw_succ M source) (raw_succ M target)
    targetAssignmentCode targetAssignmentStep
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound hrows hreplacementEvaluation) as hall.
  exact (hall rootIndex source target (raw_zero M)
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hroot hrootLookup
    (raw_assignment_lt_self_succ M hPA source)
    (raw_assignment_lt_self_succ M hPA target)
    hcompat hsource htarget).
Qed.

Theorem raw_fixedLevelFormulaSingleSubstitutionTarskiStep_scheduled : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
    replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawFixedLevelFormulaSubstitutionTransportReady M inputLevel
    replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA inputLevel replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hready.
  pose proof
    (raw_fixedLevelFormulaSubstitutionTransportReady_target_admissible
      M hPA inputLevel replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep hready) as htarget.
  destruct hready as
    [(sourceCode & sourceStep & targetCode & targetStep &
      depthCode & depthStep & bound & rootIndex & htrace)
     [(replacementValue & hreplacementEvaluation & hprepend)
      [hsource [_ _]]]].
  apply (raw_formulaSubstitutionOperationTrace_scheduled_transport M hPA
    inputLevel replacement replacementValue source target
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep htrace
    hreplacementEvaluation).
  - exact (raw_codedFormulaSubstitutionBinderCompatibility_root M hPA
      replacement replacementValue source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep hprepend).
  - exact hsource.
  - exact htarget.
Qed.

Theorem raw_fixedLevelFormulaSingleSubstitutionTarskiStep_all : forall level
    (M : RawPAModel), RawPASatisfies M -> forall
    replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep,
  RawFixedLevelFormulaSubstitutionTarskiStep M level
    replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros level M hPA replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hready.
  pose proof hready as hreadyFull.
  pose proof
    (raw_fixedLevelFormulaSingleSubstitutionTarskiStep_scheduled M hPA level
      replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep hreadyFull) as hscheduled.
  pose proof
    (raw_fixedLevelFormulaSubstitutionTransportReady_target_admissible
      M hPA level replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep hreadyFull)
    as htargetAdmissible.
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

Definition fixedLevelFormulaSubstitutionTarskiStepFormula
    (level : nat) : formula :=
  fixedLevelFormulaSubstitutionTarskiStepTermAt level
    (tVar 0) (tVar 1) (tVar 2)
    (tVar 3) (tVar 4) (tVar 5) (tVar 6).

Theorem fixedLevelFormulaSubstitutionTarskiStepFormula_raw_valid :
  forall level (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (fixedLevelFormulaSubstitutionTarskiStepFormula level).
Proof.
  intros level M hPA e.
  unfold fixedLevelFormulaSubstitutionTarskiStepFormula.
  apply (proj2 (raw_sat_fixedLevelFormulaSubstitutionTarskiStepTermAt_iff
    M e level (tVar 0) (tVar 1) (tVar 2)
    (tVar 3) (tVar 4) (tVar 5) (tVar 6))).
  apply raw_fixedLevelFormulaSingleSubstitutionTarskiStep_all. exact hPA.
Qed.

Definition fixedLevelFormulaSubstitutionTarskiStepFormula_closed
    (level : nat) : formula :=
  Formula.sealPA (fixedLevelFormulaSubstitutionTarskiStepFormula level).

Theorem fixedLevelFormulaSubstitutionTarskiStepFormula_closed_sentence :
  forall level,
  Formula.Sentence
    (fixedLevelFormulaSubstitutionTarskiStepFormula_closed level).
Proof.
  intro level.
  unfold fixedLevelFormulaSubstitutionTarskiStepFormula_closed.
  apply Formula.sealPA_sentence.
Qed.

Theorem fixedLevelFormulaSubstitutionTarskiStepFormula_closed_raw_valid :
  forall level (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (fixedLevelFormulaSubstitutionTarskiStepFormula_closed level).
Proof.
  intros level M hPA e.
  unfold fixedLevelFormulaSubstitutionTarskiStepFormula_closed.
  apply (raw_formula_sat_sealPA_of_valid M). intro e'.
  exact (fixedLevelFormulaSubstitutionTarskiStepFormula_raw_valid
    level M hPA e').
Qed.

Theorem PA_proves_fixedLevelFormulaSubstitutionTarskiStepFormula_closed :
  forall level : nat,
  Formula.BProv Formula.Ax_s []
    (fixedLevelFormulaSubstitutionTarskiStepFormula_closed level).
Proof.
  intro level. apply PA_BProv_of_raw_valid.
  - apply fixedLevelFormulaSubstitutionTarskiStepFormula_closed_sentence.
  - apply fixedLevelFormulaSubstitutionTarskiStepFormula_closed_raw_valid.
Qed.

Theorem PA_proves_fixedLevelFormulaSubstitutionTarskiStepFormula :
  forall level : nat,
  Formula.BProv Formula.Ax_s []
    (fixedLevelFormulaSubstitutionTarskiStepFormula level).
Proof.
  intro level.
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s [] (fixedLevelFormulaSubstitutionTarskiStepFormula level)
    (fun n => n)
    (PA_proves_fixedLevelFormulaSubstitutionTarskiStepFormula_closed level))
    as h.
  now rewrite Formula.rename_id in h.
Qed.



End PABoundedRawCodedFixedLevelTruthOperationTarskiSubstitutionPositive.
