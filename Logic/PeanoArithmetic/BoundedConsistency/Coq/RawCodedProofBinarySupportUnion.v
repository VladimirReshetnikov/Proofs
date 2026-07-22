(**
  Exact union of two model-coded proof-support tables beneath one parent.

  Binary natural-deduction constructors must retain every node of both
  premise trees.  Their root codes and the gap up to the new parent may all
  be nonstandard, so an external finite loop cannot build the assignment.
  This module instead uses PA's definable induction to construct a beta table
  whose supported rows are exactly the old left tree, the old right tree,
  and the new parent.  Exactness prevents unsupported gap values from being
  mistaken for proof nodes by the global traversal.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedFixedLevelTruthTotality
  RawCodedProofTraversal.

Module PABoundedRawCodedProofBinarySupportUnion.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofTraversal.

Definition RawProofBinarySupportDesired (M : RawPAModel)
    (leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent index : M) : Prop :=
  (rawLt M index (raw_succ M leftRoot) /\
    rawProofCodeSupported M leftCode leftStep index) \/
  (rawLt M index (raw_succ M rightRoot) /\
    rawProofCodeSupported M rightCode rightStep index) \/
  index = parent.

Arguments RawProofBinarySupportDesired
  M leftRoot leftCode leftStep rightRoot rightCode rightStep parent index
  : clear implicits.

Definition proofBinarySupportDesiredTermAt
    (leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent index : term) : formula :=
  pOr
    (pAnd
      (Formula.ltTermAt index (tSucc leftRoot))
      (proofCodeSupportedTermAt leftCode leftStep index))
    (pOr
      (pAnd
        (Formula.ltTermAt index (tSucc rightRoot))
        (proofCodeSupportedTermAt rightCode rightStep index))
      (pEq index parent)).

Lemma raw_sat_proofBinarySupportDesiredTermAt_iff : forall
    (M : RawPAModel) e
      leftRoot leftCode leftStep rightRoot rightCode rightStep parent index,
  raw_formula_sat M e
    (proofBinarySupportDesiredTermAt
      leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent index) <->
  RawProofBinarySupportDesired M
    (raw_term_eval M e leftRoot)
    (raw_term_eval M e leftCode) (raw_term_eval M e leftStep)
    (raw_term_eval M e rightRoot)
    (raw_term_eval M e rightCode) (raw_term_eval M e rightStep)
    (raw_term_eval M e parent) (raw_term_eval M e index).
Proof.
  intros. unfold proofBinarySupportDesiredTermAt,
    RawProofBinarySupportDesired.
  cbn [raw_formula_sat raw_term_eval].
  rewrite !raw_sat_ltTermAt_iff,
    !raw_sat_proofCodeSupportedTermAt_iff.
  reflexivity.
Qed.

Definition RawProofBinarySupportPrefix (M : RawPAModel)
    (leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent current newCode newStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M newCode newStep current /\
  forall index,
    rawLt M index current ->
    (rawProofCodeSupported M newCode newStep index <->
      RawProofBinarySupportDesired M
        leftRoot leftCode leftStep rightRoot rightCode rightStep
        parent index).

Arguments RawProofBinarySupportPrefix
  M leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent current newCode newStep : clear implicits.

Definition proofBinarySupportIff (left right : formula) : formula :=
  pAnd (pImp left right) (pImp right left).

Definition proofBinarySupportPrefixTermAt
    (leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent current newCode newStep : term) : formula :=
  pAnd
    (codedAssignmentDefinedThroughTermAt newCode newStep current)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
        (proofBinarySupportIff
          (proofCodeSupportedTermAt
            (liftTerm 1 newCode) (liftTerm 1 newStep) (tVar 0))
          (proofBinarySupportDesiredTermAt
            (liftTerm 1 leftRoot)
            (liftTerm 1 leftCode) (liftTerm 1 leftStep)
            (liftTerm 1 rightRoot)
            (liftTerm 1 rightCode) (liftTerm 1 rightStep)
            (liftTerm 1 parent) (tVar 0))))).

Lemma raw_sat_proofBinarySupportPrefixTermAt_iff : forall
    (M : RawPAModel) e
      leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent current newCode newStep,
  raw_formula_sat M e
    (proofBinarySupportPrefixTermAt
      leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent current newCode newStep) <->
  RawProofBinarySupportPrefix M
    (raw_term_eval M e leftRoot)
    (raw_term_eval M e leftCode) (raw_term_eval M e leftStep)
    (raw_term_eval M e rightRoot)
    (raw_term_eval M e rightCode) (raw_term_eval M e rightStep)
    (raw_term_eval M e parent) (raw_term_eval M e current)
    (raw_term_eval M e newCode) (raw_term_eval M e newStep).
Proof.
  intros M e leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent current newCode newStep.
  unfold proofBinarySupportPrefixTermAt,
    proofBinarySupportIff, RawProofBinarySupportPrefix.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_proofCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_proofBinarySupportDesiredTermAt_iff.
  repeat setoid_rewrite raw_proofTraversal_eval_liftTerm_one.
  cbn [raw_term_eval scons]. tauto.
Qed.

Definition RawProofBinarySupportExists (M : RawPAModel)
    (leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent current : M) : Prop :=
  exists newCode newStep,
    RawProofBinarySupportPrefix M
      leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent current newCode newStep.

Arguments RawProofBinarySupportExists
  M leftRoot leftCode leftStep rightRoot rightCode rightStep parent current
  : clear implicits.

Definition proofBinarySupportExistsTermAt
    (leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent current : term) : formula :=
  pEx (pEx
    (proofBinarySupportPrefixTermAt
      (liftTerm 2 leftRoot)
      (liftTerm 2 leftCode) (liftTerm 2 leftStep)
      (liftTerm 2 rightRoot)
      (liftTerm 2 rightCode) (liftTerm 2 rightStep)
      (liftTerm 2 parent) (liftTerm 2 current)
      (tVar 1) (tVar 0))).

Lemma raw_sat_proofBinarySupportExistsTermAt_iff : forall
    (M : RawPAModel) e
      leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent current,
  raw_formula_sat M e
    (proofBinarySupportExistsTermAt
      leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent current) <->
  RawProofBinarySupportExists M
    (raw_term_eval M e leftRoot)
    (raw_term_eval M e leftCode) (raw_term_eval M e leftStep)
    (raw_term_eval M e rightRoot)
    (raw_term_eval M e rightCode) (raw_term_eval M e rightStep)
    (raw_term_eval M e parent) (raw_term_eval M e current).
Proof.
  intros M e leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent current.
  unfold proofBinarySupportExistsTermAt,
    RawProofBinarySupportExists.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofBinarySupportPrefixTermAt_iff.
  repeat setoid_rewrite raw_proofTraversal_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_proofBinarySupport_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftRoot leftCode leftStep rightRoot rightCode rightStep parent,
  RawProofBinarySupportExists M
    leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent (raw_zero M).
Proof.
  intros M hPA leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent.
  exists (raw_zero M), (raw_zero M). split.
  - exact (raw_codedAssignment_empty_defined M hPA).
  - intros index hindex. exfalso.
    exact (raw_not_lt_zero M hPA index hindex).
Qed.

Lemma raw_proofBinarySupport_append_old_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent current sourceCode sourceStep targetCode targetStep flag,
  RawProofBinarySupportPrefix M
    leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent current sourceCode sourceStep ->
  RawCodedAssignmentDefinedThrough M targetCode targetStep
    (raw_succ M current) ->
  (forall index value,
    rawLt M index current ->
    RawCodedAssignmentLookup M sourceCode sourceStep index value ->
    RawCodedAssignmentLookup M targetCode targetStep index value) ->
  RawCodedAssignmentLookup M targetCode targetStep current flag ->
  forall index,
    rawLt M index current ->
    (rawProofCodeSupported M targetCode targetStep index <->
      RawProofBinarySupportDesired M
        leftRoot leftCode leftStep rightRoot rightCode rightStep
        parent index).
Proof.
  intros M hPA leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent current sourceCode sourceStep targetCode targetStep flag
    [hsourceDefined hsourceExact] _ hprefix _ index hindex.
  split.
  - intro htargetSupported.
    destruct (hsourceDefined index hindex) as [sourceValue hsourceValue].
    pose proof (hprefix index sourceValue hindex hsourceValue)
      as htargetValue.
    unfold rawProofCodeSupported in htargetSupported.
    assert (hone : rawNumeralValue M 1 = sourceValue).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        targetCode targetStep index
        (rawNumeralValue M 1) sourceValue
        htargetSupported htargetValue).
    }
    rewrite <- hone in hsourceValue.
    exact (proj1 (hsourceExact index hindex) hsourceValue).
  - intro hdesired.
    pose proof (proj2 (hsourceExact index hindex) hdesired)
      as hsourceSupported.
    unfold rawProofCodeSupported in *.
    exact (hprefix index (rawNumeralValue M 1)
      hindex hsourceSupported).
Qed.

Lemma raw_proofBinarySupport_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent current,
  RawProofBinarySupportExists M
    leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent current ->
  RawProofBinarySupportExists M
    leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent (raw_succ M current).
Proof.
  intros M hPA leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent current (sourceCode & sourceStep & hsource).
  destruct (classic (RawProofBinarySupportDesired M
    leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent current)) as [hdesired | hnot].
  - destruct (raw_codedAssignmentAppend_defined_exists M hPA
      sourceCode sourceStep current (rawNumeralValue M 1)
      (proj1 hsource))
      as (targetCode & targetStep & hdefined & hprefix & hnew).
    exists targetCode, targetStep. split; [exact hdefined |].
    intros index hindex.
    destruct (raw_lt_succ_cases M hPA index current hindex)
      as [hold | ->].
    + exact (raw_proofBinarySupport_append_old_iff M hPA
        leftRoot leftCode leftStep rightRoot rightCode rightStep
        parent current sourceCode sourceStep targetCode targetStep
        (rawNumeralValue M 1) hsource hdefined hprefix hnew
        index hold).
    + split; intro; [exact hdesired |].
      unfold rawProofCodeSupported. exact hnew.
  - destruct (raw_codedAssignmentAppend_defined_exists M hPA
      sourceCode sourceStep current (raw_zero M)
      (proj1 hsource))
      as (targetCode & targetStep & hdefined & hprefix & hnew).
    exists targetCode, targetStep. split; [exact hdefined |].
    intros index hindex.
    destruct (raw_lt_succ_cases M hPA index current hindex)
      as [hold | ->].
    + exact (raw_proofBinarySupport_append_old_iff M hPA
        leftRoot leftCode leftStep rightRoot rightCode rightStep
        parent current sourceCode sourceStep targetCode targetStep
        (raw_zero M) hsource hdefined hprefix hnew
        index hold).
    + split.
      * intro hsupported. exfalso. apply hnot.
        unfold rawProofCodeSupported in hsupported.
        assert (honeZero : rawNumeralValue M 1 = raw_zero M).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            targetCode targetStep current
            (rawNumeralValue M 1) (raw_zero M)
            hsupported hnew).
        }
        change (rawNumeralValue M 1 = rawNumeralValue M 0) in honeZero.
        apply (rawNumeralValue_injective M hPA 1 0) in honeZero.
        discriminate.
      * intro hcontra. exfalso. exact (hnot hcontra).
Qed.

Theorem raw_proofBinarySupport_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent current,
  RawProofBinarySupportExists M
    leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent current.
Proof.
  intros M hPA leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent.
  set (parameterEnv :=
    scons M leftRoot
      (scons M leftCode
        (scons M leftStep
          (scons M rightRoot
            (scons M rightCode
              (scons M rightStep
                (scons M parent (fun _ : nat => raw_zero M)))))))).
  set (phi := proofBinarySupportExistsTermAt
    (tVar 1) (tVar 2) (tVar 3)
    (tVar 4) (tVar 5) (tVar 6) (tVar 7) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_proofBinarySupportExistsTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3)
        (tVar 4) (tVar 5) (tVar 6) (tVar 7) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_proofBinarySupport_zero M hPA
        leftRoot leftCode leftStep rightRoot rightCode rightStep parent).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_proofBinarySupportExistsTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3)
          (tVar 4) (tVar 5) (tVar 6) (tVar 7) (tVar 0))
        hcurrent) as hraw.
      apply (proj2
        (raw_sat_proofBinarySupportExistsTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3)
          (tVar 4) (tVar 5) (tVar 6) (tVar 7) (tVar 0))).
      unfold parameterEnv in hraw |- *.
      cbn [raw_term_eval scons] in hraw |- *.
      exact (raw_proofBinarySupport_succ M hPA
        leftRoot leftCode leftStep rightRoot rightCode rightStep
        parent current hraw).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_proofBinarySupportExistsTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3)
      (tVar 4) (tVar 5) (tVar 6) (tVar 7) (tVar 0))
    (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw.
  exact hraw.
Qed.

Corollary raw_proofBinarySupport_to_parent : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftRoot leftCode leftStep rightRoot rightCode rightStep parent,
  exists newCode newStep,
    RawProofBinarySupportPrefix M
      leftRoot leftCode leftStep rightRoot rightCode rightStep
      parent (raw_succ M parent) newCode newStep.
Proof.
  intros M hPA leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent.
  exact (raw_proofBinarySupport_all M hPA
    leftRoot leftCode leftStep rightRoot rightCode rightStep
    parent (raw_succ M parent)).
Qed.

End PABoundedRawCodedProofBinarySupportUnion.
