(**
  Structural closure of model-internal coded contexts.

  The traversal interface in [RawCodedContextLists] is intentionally only a
  graph definition.  Natural-deduction rules additionally need to know that
  the empty context is realizable and that adjoining one formula preserves
  realizability, membership, and the all-occurrences rank bound.

  The cons construction is nontrivial for a nonstandard context length.  It
  uses PA's beta-prepend theorem twice: once to put the new public list node in
  front of the tail-code table, and once to put the new formula in front of
  the head table.  The old traversal may have a nonstandard number of rows;
  no Rocq recursion over that bound occurs.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedProofDescent
  RawCodedContextLists RawCodedContextBounds.

Import ListNotations.

Module PABoundedRawCodedContextStructure.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextBounds.

(** A complete tail traversal defines every tail slot through and including
    its terminal zero, hence through [S bound] in the strict-prefix idiom. *)
Lemma raw_contextListTraversal_tail_defined : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root bound tailCode tailStep headCode headStep,
  RawContextListTraversal M
    root bound tailCode tailStep headCode headStep ->
  RawCodedAssignmentDefinedThrough M
    tailCode tailStep (raw_succ M bound).
Proof.
  intros M hPA root bound tailCode tailStep headCode headStep
    [hroot [hend [hhead hrows]]] index hindex.
  destruct (raw_lt_succ_cases M hPA index bound hindex)
    as [hbelow | ->].
  - destruct (hrows index hbelow)
      as (currentTail & nextTail & head & hcurrent & _).
    exists currentTail. exact hcurrent.
  - exists (raw_zero M). exact hend.
Qed.

(** Data retained from the two beta-prepend operations.  Keeping these graph
    witnesses visible makes the membership and boundedness corollaries use
    exactly the newly constructed tables. *)
Definition RawContextListConsExtension (M : RawPAModel)
    (root head bound tailCode tailStep headCode headStep
      newTailCode newTailStep newHeadCode newHeadStep : M) : Prop :=
  RawCodedAssignmentPrepend M tailCode tailStep
    (rawListNode M head root) (raw_succ M bound)
    newTailCode newTailStep /\
  RawCodedAssignmentPrepend M headCode headStep head bound
    newHeadCode newHeadStep /\
  RawContextListTraversal M
    (rawListNode M head root) (raw_succ M bound)
    newTailCode newTailStep newHeadCode newHeadStep.

Arguments RawContextListConsExtension
  M root head bound tailCode tailStep headCode headStep
    newTailCode newTailStep newHeadCode newHeadStep : clear implicits.

Theorem raw_contextListConsExtension_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root head bound tailCode tailStep headCode headStep,
  RawContextListTraversal M
    root bound tailCode tailStep headCode headStep ->
  exists newTailCode newTailStep newHeadCode newHeadStep : M,
    RawContextListConsExtension M root head bound
      tailCode tailStep headCode headStep
      newTailCode newTailStep newHeadCode newHeadStep.
Proof.
  intros M hPA root head bound tailCode tailStep headCode headStep
    htraversal.
  destruct htraversal as [hroot [hend [hheadDefined hrows]]].
  assert (htailDefined : RawCodedAssignmentDefinedThrough M
      tailCode tailStep (raw_succ M bound)).
  {
    apply (raw_contextListTraversal_tail_defined M hPA
      root bound tailCode tailStep headCode headStep).
    repeat split; assumption.
  }
  destruct (raw_codedAssignmentPrepend_exists M hPA
    tailCode tailStep (rawListNode M head root) (raw_succ M bound))
    as [newTailCode [newTailStep htailPrepend]].
  destruct (raw_codedAssignmentPrepend_defined_exists M hPA
    headCode headStep head bound hheadDefined)
    as [newHeadCode [newHeadStep [hheadPrepend hnewHeadDefined]]].
  exists newTailCode, newTailStep, newHeadCode, newHeadStep.
  split; [exact htailPrepend |]. split; [exact hheadPrepend |].
  repeat split.
  - exact (raw_codedAssignmentPrepend_head
      M tailCode tailStep (rawListNode M head root) (raw_succ M bound)
      newTailCode newTailStep htailPrepend).
  - apply (raw_codedAssignmentPrepend_tail M
      tailCode tailStep (rawListNode M head root) (raw_succ M bound)
      newTailCode newTailStep bound (raw_zero M) htailPrepend).
    + exact (raw_assignment_lt_self_succ M hPA bound).
    + exact hend.
  - exact hnewHeadDefined.
  - intros index hindex.
    destruct (raw_assignment_zero_or_successor M hPA index)
      as [-> | [predecessor ->]].
    + exists (rawListNode M head root), root, head.
      repeat split.
      * exact (raw_codedAssignmentPrepend_head
          M tailCode tailStep (rawListNode M head root) (raw_succ M bound)
          newTailCode newTailStep htailPrepend).
      * apply (raw_codedAssignmentPrepend_tail M
          tailCode tailStep (rawListNode M head root) (raw_succ M bound)
          newTailCode newTailStep (raw_zero M) root htailPrepend).
        -- apply raw_lt_succ_of_le; [exact hPA |].
           apply raw_proof_zero_le. exact hPA.
        -- exact hroot.
      * exact (raw_codedAssignmentPrepend_head
          M headCode headStep head bound newHeadCode newHeadStep
          hheadPrepend).
    + assert (hpredSelf : rawLt M predecessor (raw_succ M predecessor)).
      { exact (raw_assignment_lt_self_succ M hPA predecessor). }
      assert (hpredBound : rawLt M predecessor bound).
      {
        destruct (raw_lt_succ_cases M hPA
          (raw_succ M predecessor) bound hindex) as [hlt | heq].
        - exact (raw_assignment_lt_trans M hPA predecessor
            (raw_succ M predecessor) bound hpredSelf hlt).
        - rewrite <- heq. exact hpredSelf.
      }
      destruct (hrows predecessor hpredBound)
        as (currentTail & nextTail & oldHead &
          hcurrent & hnext & holdHead & hequation).
      exists currentTail, nextTail, oldHead.
      repeat split.
      * apply (raw_codedAssignmentPrepend_tail M
          tailCode tailStep (rawListNode M head root) (raw_succ M bound)
          newTailCode newTailStep predecessor currentTail htailPrepend).
        -- exact (raw_assignment_lt_trans M hPA predecessor bound
             (raw_succ M bound) hpredBound
             (raw_assignment_lt_self_succ M hPA bound)).
        -- exact hcurrent.
      * apply (raw_codedAssignmentPrepend_tail M
          tailCode tailStep (rawListNode M head root) (raw_succ M bound)
          newTailCode newTailStep (raw_succ M predecessor) nextTail
          htailPrepend hindex hnext).
      * apply (raw_codedAssignmentPrepend_tail M
          headCode headStep head bound newHeadCode newHeadStep
          predecessor oldHead hheadPrepend hpredBound holdHead).
      * exact hequation.
Qed.

Corollary raw_contextList_empty_realizable : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawContextListRealizable M (raw_zero M).
Proof.
  intros M hPA.
  destruct (raw_codedAssignmentPrepend_exists M hPA
    (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M))
    as [tailCode [tailStep htail]].
  exists (raw_zero M), tailCode, tailStep,
    (raw_zero M), (raw_zero M).
  repeat split.
  - exact (proj1 htail).
  - exact (proj1 htail).
  - exact (raw_codedAssignment_empty_defined M hPA).
  - intros index hindex.
    exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Corollary raw_contextList_cons_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall root head,
  RawContextListRealizable M root ->
  RawContextListRealizable M (rawListNode M head root).
Proof.
  intros M hPA root head
    (bound & tailCode & tailStep & headCode & headStep & htraversal).
  destruct (raw_contextListConsExtension_exists M hPA
    root head bound tailCode tailStep headCode headStep htraversal)
    as (newTailCode & newTailStep & newHeadCode & newHeadStep &
      _ & _ & hnewTraversal).
  exists (raw_succ M bound), newTailCode, newTailStep,
    newHeadCode, newHeadStep.
  exact hnewTraversal.
Qed.

Corollary raw_contextList_cons_head_member : forall
    (M : RawPAModel), RawPASatisfies M -> forall root head,
  RawContextListRealizable M root ->
  RawContextListMember M (rawListNode M head root) head.
Proof.
  intros M hPA root head
    (bound & tailCode & tailStep & headCode & headStep & htraversal).
  destruct (raw_contextListConsExtension_exists M hPA
    root head bound tailCode tailStep headCode headStep htraversal)
    as (newTailCode & newTailStep & newHeadCode & newHeadStep &
      _ & hheadPrepend & hnewTraversal).
  exists (raw_succ M bound), newTailCode, newTailStep,
    newHeadCode, newHeadStep.
  split; [exact hnewTraversal |].
  exists (raw_zero M). split.
  - apply raw_lt_succ_of_le; [exact hPA |].
    apply raw_proof_zero_le. exact hPA.
  - exact (proj1 hheadPrepend).
Qed.

Corollary raw_contextList_cons_tail_member : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root head member,
  RawContextListMember M root member ->
  RawContextListMember M (rawListNode M head root) member.
Proof.
  intros M hPA root head member
    (bound & tailCode & tailStep & headCode & headStep & htraversal &
      [index [hindex hmember]]).
  destruct (raw_contextListConsExtension_exists M hPA
    root head bound tailCode tailStep headCode headStep htraversal)
    as (newTailCode & newTailStep & newHeadCode & newHeadStep &
      _ & hheadPrepend & hnewTraversal).
  exists (raw_succ M bound), newTailCode, newTailStep,
    newHeadCode, newHeadStep.
  split; [exact hnewTraversal |].
  exists (raw_succ M index). split.
  - apply raw_lt_succ_of_le; [exact hPA |].
    exact (raw_succ_le_of_lt_pair M hPA index bound hindex).
  - exact (raw_codedAssignmentPrepend_tail M
      headCode headStep head bound newHeadCode newHeadStep
      index member hheadPrepend hindex hmember).
Qed.

(** All-occurrences boundedness is closed under canonical context cons. *)
Theorem raw_contextAllBounded_cons : forall
    (M : RawPAModel), RawPASatisfies M -> forall level root head,
  RawContextAllBounded M level root ->
  RawFormulaQuantifierBounded M level head ->
  RawContextAllBounded M level (rawListNode M head root).
Proof.
  intros M hPA level root head
    (bound & tailCode & tailStep & headCode & headStep &
      htraversal & hall) hheadBounded.
  destruct htraversal as [hroot [hend [hheadDefined hrows]]].
  assert (holdTraversal : RawContextListTraversal M
      root bound tailCode tailStep headCode headStep).
  { repeat split; assumption. }
  destruct (raw_contextListConsExtension_exists M hPA
    root head bound tailCode tailStep headCode headStep holdTraversal)
    as (newTailCode & newTailStep & newHeadCode & newHeadStep &
      _ & hheadPrepend & hnewTraversal).
  exists (raw_succ M bound), newTailCode, newTailStep,
    newHeadCode, newHeadStep.
  split; [exact hnewTraversal |].
  intros index hindex code hlookup.
  destruct (raw_assignment_zero_or_successor M hPA index)
    as [-> | [predecessor ->]].
  - apply (proj1 (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
      headCode headStep head bound newHeadCode newHeadStep code
      hheadPrepend)) in hlookup.
    subst code. exact hheadBounded.
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
    apply (proj1 (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
      headCode headStep head bound newHeadCode newHeadStep
      hheadDefined hheadPrepend predecessor hpredBound code)) in hlookup.
    exact (hall predecessor hpredBound code hlookup).
Qed.

End PABoundedRawCodedContextStructure.
