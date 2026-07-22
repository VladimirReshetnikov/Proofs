(**
  Extending a proof-support table by one model-coded parent node.

  A proof certificate stores support flags in a beta assignment indexed by
  raw proof codes.  To place a new constructor above an existing proof tree,
  it is not enough to append one flag: the parent code can be nonstandard and
  arbitrarily far above the child root.  This module uses a genuine PA
  induction instance to rebuild the assignment through the parent, copying
  exactly the old supported prefix and marking exactly the new parent.

  The exact characterization of the rebuilt table is important.  Merely
  preserving old [1] flags would permit accidental supported junk rows in the
  gap, which would make [RawProofRuleCoverage] demand local proof rules for
  numbers that are not nodes of the constructed proof.
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

Module PABoundedRawCodedProofSupportExtension.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofTraversal.

(** The desired flag at [index]: retain an old supported node only inside
    the old certificate's declared bound, or mark the new parent itself. *)
Definition RawProofSupportExtensionDesired (M : RawPAModel)
    (childRoot oldCode oldStep parent index : M) : Prop :=
  (rawLt M index (raw_succ M childRoot) /\
    rawProofCodeSupported M oldCode oldStep index) \/
  index = parent.

Arguments RawProofSupportExtensionDesired
  M childRoot oldCode oldStep parent index : clear implicits.

Definition proofSupportExtensionDesiredTermAt
    (childRoot oldCode oldStep parent index : term) : formula :=
  pOr
    (pAnd
      (Formula.ltTermAt index (tSucc childRoot))
      (proofCodeSupportedTermAt oldCode oldStep index))
    (pEq index parent).

Lemma raw_sat_proofSupportExtensionDesiredTermAt_iff : forall
    (M : RawPAModel) e childRoot oldCode oldStep parent index,
  raw_formula_sat M e
    (proofSupportExtensionDesiredTermAt
      childRoot oldCode oldStep parent index) <->
  RawProofSupportExtensionDesired M
    (raw_term_eval M e childRoot)
    (raw_term_eval M e oldCode) (raw_term_eval M e oldStep)
    (raw_term_eval M e parent) (raw_term_eval M e index).
Proof.
  intros. unfold proofSupportExtensionDesiredTermAt,
    RawProofSupportExtensionDesired.
  cbn [raw_formula_sat raw_term_eval].
  rewrite raw_sat_ltTermAt_iff,
    raw_sat_proofCodeSupportedTermAt_iff.
  reflexivity.
Qed.

(** Prefix correctness of a candidate rebuilt table. *)
Definition RawProofSupportExtensionPrefix (M : RawPAModel)
    (childRoot oldCode oldStep parent current newCode newStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M newCode newStep current /\
  forall index,
    rawLt M index current ->
    (rawProofCodeSupported M newCode newStep index <->
      RawProofSupportExtensionDesired M
        childRoot oldCode oldStep parent index).

Arguments RawProofSupportExtensionPrefix
  M childRoot oldCode oldStep parent current newCode newStep
  : clear implicits.

Definition proofSupportExtensionIff (left right : formula) : formula :=
  pAnd (pImp left right) (pImp right left).

Definition proofSupportExtensionPrefixTermAt
    (childRoot oldCode oldStep parent current newCode newStep : term)
    : formula :=
  pAnd
    (codedAssignmentDefinedThroughTermAt newCode newStep current)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
        (proofSupportExtensionIff
          (proofCodeSupportedTermAt
            (liftTerm 1 newCode) (liftTerm 1 newStep) (tVar 0))
          (proofSupportExtensionDesiredTermAt
            (liftTerm 1 childRoot)
            (liftTerm 1 oldCode) (liftTerm 1 oldStep)
            (liftTerm 1 parent) (tVar 0))))).

Lemma raw_sat_proofSupportExtensionPrefixTermAt_iff : forall
    (M : RawPAModel) e childRoot oldCode oldStep parent current
      newCode newStep,
  raw_formula_sat M e
    (proofSupportExtensionPrefixTermAt
      childRoot oldCode oldStep parent current newCode newStep) <->
  RawProofSupportExtensionPrefix M
    (raw_term_eval M e childRoot)
    (raw_term_eval M e oldCode) (raw_term_eval M e oldStep)
    (raw_term_eval M e parent) (raw_term_eval M e current)
    (raw_term_eval M e newCode) (raw_term_eval M e newStep).
Proof.
  intros M e childRoot oldCode oldStep parent current newCode newStep.
  unfold proofSupportExtensionPrefixTermAt,
    proofSupportExtensionIff, RawProofSupportExtensionPrefix.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_proofCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_proofSupportExtensionDesiredTermAt_iff.
  repeat setoid_rewrite raw_proofTraversal_eval_liftTerm_one.
  cbn [raw_term_eval scons]. tauto.
Qed.

Definition RawProofSupportExtensionExists (M : RawPAModel)
    (childRoot oldCode oldStep parent current : M) : Prop :=
  exists newCode newStep,
    RawProofSupportExtensionPrefix M
      childRoot oldCode oldStep parent current newCode newStep.

Arguments RawProofSupportExtensionExists
  M childRoot oldCode oldStep parent current : clear implicits.

Definition proofSupportExtensionExistsTermAt
    (childRoot oldCode oldStep parent current : term) : formula :=
  pEx (pEx
    (proofSupportExtensionPrefixTermAt
      (liftTerm 2 childRoot)
      (liftTerm 2 oldCode) (liftTerm 2 oldStep)
      (liftTerm 2 parent) (liftTerm 2 current)
      (tVar 1) (tVar 0))).

Lemma raw_sat_proofSupportExtensionExistsTermAt_iff : forall
    (M : RawPAModel) e childRoot oldCode oldStep parent current,
  raw_formula_sat M e
    (proofSupportExtensionExistsTermAt
      childRoot oldCode oldStep parent current) <->
  RawProofSupportExtensionExists M
    (raw_term_eval M e childRoot)
    (raw_term_eval M e oldCode) (raw_term_eval M e oldStep)
    (raw_term_eval M e parent) (raw_term_eval M e current).
Proof.
  intros M e childRoot oldCode oldStep parent current.
  unfold proofSupportExtensionExistsTermAt,
    RawProofSupportExtensionExists.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofSupportExtensionPrefixTermAt_iff.
  repeat setoid_rewrite raw_proofTraversal_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_proofSupportExtension_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      childRoot oldCode oldStep parent,
  RawProofSupportExtensionExists M
    childRoot oldCode oldStep parent (raw_zero M).
Proof.
  intros M hPA childRoot oldCode oldStep parent.
  exists (raw_zero M), (raw_zero M).
  split.
  - exact (raw_codedAssignment_empty_defined M hPA).
  - intros index hindex. exfalso.
    exact (raw_not_lt_zero M hPA index hindex).
Qed.

(** Appending a row preserves the exact support characterization at every
    old index.  The reverse direction uses beta-lookup functionality; prefix
    preservation alone would not rule out a second value at that index. *)
Lemma raw_proofSupportExtension_append_old_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      childRoot oldCode oldStep parent current sourceCode sourceStep
      targetCode targetStep flag,
  RawProofSupportExtensionPrefix M
    childRoot oldCode oldStep parent current sourceCode sourceStep ->
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
      RawProofSupportExtensionDesired M
        childRoot oldCode oldStep parent index).
Proof.
  intros M hPA childRoot oldCode oldStep parent current
    sourceCode sourceStep targetCode targetStep flag
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
    apply (proj1 (hsourceExact index hindex)).
    exact hsourceValue.
  - intro hdesired.
    pose proof (proj2 (hsourceExact index hindex) hdesired)
      as hsourceSupported.
    unfold rawProofCodeSupported in *.
    exact (hprefix index (rawNumeralValue M 1)
      hindex hsourceSupported).
Qed.

Lemma raw_proofSupportExtension_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      childRoot oldCode oldStep parent current,
  RawProofSupportExtensionExists M
    childRoot oldCode oldStep parent current ->
  RawProofSupportExtensionExists M
    childRoot oldCode oldStep parent (raw_succ M current).
Proof.
  intros M hPA childRoot oldCode oldStep parent current
    (sourceCode & sourceStep & hsource).
  destruct (classic (RawProofSupportExtensionDesired M
    childRoot oldCode oldStep parent current)) as [hdesired | hnot].
  - destruct (raw_codedAssignmentAppend_defined_exists M hPA
      sourceCode sourceStep current (rawNumeralValue M 1)
      (proj1 hsource))
      as (targetCode & targetStep & hdefined & hprefix & hnew).
    exists targetCode, targetStep. split; [exact hdefined |].
    intros index hindex.
    destruct (raw_lt_succ_cases M hPA index current hindex)
      as [hold | ->].
    + exact (raw_proofSupportExtension_append_old_iff M hPA
        childRoot oldCode oldStep parent current
        sourceCode sourceStep targetCode targetStep
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
    + exact (raw_proofSupportExtension_append_old_iff M hPA
        childRoot oldCode oldStep parent current
        sourceCode sourceStep targetCode targetStep
        (raw_zero M) hsource hdefined hprefix hnew
        index hold).
    + split.
      * intro hsupported.
        exfalso. apply hnot.
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

(** Definable induction performs the extension through arbitrary model
    bounds; no host-language decoding of [current] occurs. *)
Theorem raw_proofSupportExtension_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      childRoot oldCode oldStep parent current,
  RawProofSupportExtensionExists M
    childRoot oldCode oldStep parent current.
Proof.
  intros M hPA childRoot oldCode oldStep parent.
  set (parameterEnv :=
    scons M childRoot
      (scons M oldCode
        (scons M oldStep
          (scons M parent (fun _ : nat => raw_zero M))))).
  set (phi := proofSupportExtensionExistsTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_proofSupportExtensionExistsTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_proofSupportExtension_zero M hPA
        childRoot oldCode oldStep parent).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_proofSupportExtensionExistsTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))
        hcurrent) as hraw.
      apply (proj2
        (raw_sat_proofSupportExtensionExistsTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))).
      unfold parameterEnv in hraw |- *.
      cbn [raw_term_eval scons] in hraw |- *.
      exact (raw_proofSupportExtension_succ M hPA
        childRoot oldCode oldStep parent current hraw).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_proofSupportExtensionExistsTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))
    (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw.
  exact hraw.
Qed.

(** Public form used by a unary proof constructor. *)
Corollary raw_proofSupportExtension_to_parent : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      childRoot oldCode oldStep parent,
  exists newCode newStep,
    RawProofSupportExtensionPrefix M
      childRoot oldCode oldStep parent (raw_succ M parent)
      newCode newStep.
Proof.
  intros M hPA childRoot oldCode oldStep parent.
  exact (raw_proofSupportExtension_all M hPA
    childRoot oldCode oldStep parent (raw_succ M parent)).
Qed.

End PABoundedRawCodedProofSupportExtension.
