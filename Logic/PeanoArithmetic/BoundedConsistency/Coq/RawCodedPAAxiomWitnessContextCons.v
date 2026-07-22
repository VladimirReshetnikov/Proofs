(**
  Extending a model-coded witnessed PA-axiom context by one axiom.

  The two lists in [RawCodedPAAxiomWitnessContext] are traversed by separate
  beta tables but share one (possibly nonstandard) length.  This theorem
  prepends a witness and its axiom to those traversals in lockstep.  At row
  zero the supplied witness relation is used; successor rows are recovered
  from the old total tables and transported through beta-prepend.

  This is the context-building operation needed by proof compilers which
  generate an induction axiom for a nonstandard formula code.  No decoding of
  either list and no metatheoretic recursion over its length occurs.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedContextLists RawCodedContextStructure
  RawCodedPAAxiomWitness RawCodedRestrictedPAProof.

Module PABoundedRawCodedPAAxiomWitnessContextCons.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.

Theorem raw_codedPAAxiomWitnessContext_cons : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context witness axiom,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCodedPAAxiomWitness M witness axiom ->
  RawCodedPAAxiomWitnessContext M
    (rawListNode M witness witnessList)
    (rawListNode M axiom context).
Proof.
  intros M hPA witnessList context witness axiom
    (bound & witnessTailCode & witnessTailStep &
      witnessHeadCode & witnessHeadStep &
      axiomTailCode & axiomTailStep & axiomHeadCode & axiomHeadStep &
      hwitnessTraversal & haxiomTraversal & hrows)
    hwitness.
  destruct (raw_contextListConsExtension_exists M hPA
    witnessList witness bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    hwitnessTraversal) as
    (newWitnessTailCode & newWitnessTailStep &
      newWitnessHeadCode & newWitnessHeadStep &
      hwitnessTailPrepend & hwitnessHeadPrepend &
      hnewWitnessTraversal).
  destruct (raw_contextListConsExtension_exists M hPA
    context axiom bound
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
    haxiomTraversal) as
    (newAxiomTailCode & newAxiomTailStep &
      newAxiomHeadCode & newAxiomHeadStep &
      haxiomTailPrepend & haxiomHeadPrepend &
      hnewAxiomTraversal).
  exists (raw_succ M bound),
    newWitnessTailCode, newWitnessTailStep,
    newWitnessHeadCode, newWitnessHeadStep,
    newAxiomTailCode, newAxiomTailStep,
    newAxiomHeadCode, newAxiomHeadStep.
  split; [exact hnewWitnessTraversal |].
  split; [exact hnewAxiomTraversal |].
  intros index witnessAt axiomAt hindex
    hwitnessAt haxiomAt.
  destruct (raw_assignment_zero_or_successor M hPA index)
    as [-> | [predecessor ->]].
  - assert (hwitnessAtEq : witnessAt = witness).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        newWitnessHeadCode newWitnessHeadStep (raw_zero M)
        witnessAt witness hwitnessAt
        (raw_codedAssignmentPrepend_head M
          witnessHeadCode witnessHeadStep witness bound
          newWitnessHeadCode newWitnessHeadStep hwitnessHeadPrepend)).
    }
    assert (haxiomAtEq : axiomAt = axiom).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        newAxiomHeadCode newAxiomHeadStep (raw_zero M)
        axiomAt axiom haxiomAt
        (raw_codedAssignmentPrepend_head M
          axiomHeadCode axiomHeadStep axiom bound
          newAxiomHeadCode newAxiomHeadStep haxiomHeadPrepend)).
    }
    now subst witnessAt; subst axiomAt.
  - assert (hpredecessor : rawLt M predecessor bound).
    {
      destruct (raw_lt_succ_cases M hPA
        (raw_succ M predecessor) bound hindex) as [hstrict | hequal].
      + exact (raw_assignment_lt_trans M hPA predecessor
          (raw_succ M predecessor) bound
          (raw_assignment_lt_self_succ M hPA predecessor) hstrict).
      + rewrite <- hequal.
        exact (raw_assignment_lt_self_succ M hPA predecessor).
    }
    destruct (proj1 (proj2 (proj2 hwitnessTraversal))
      predecessor hpredecessor)
      as [oldWitness holdWitness].
    destruct (proj1 (proj2 (proj2 haxiomTraversal))
      predecessor hpredecessor)
      as [oldAxiom holdAxiom].
    assert (hwitnessAtEq : witnessAt = oldWitness).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        newWitnessHeadCode newWitnessHeadStep (raw_succ M predecessor)
        witnessAt oldWitness hwitnessAt
        (raw_codedAssignmentPrepend_tail M
          witnessHeadCode witnessHeadStep witness bound
          newWitnessHeadCode newWitnessHeadStep predecessor oldWitness
          hwitnessHeadPrepend hpredecessor holdWitness)).
    }
    assert (haxiomAtEq : axiomAt = oldAxiom).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        newAxiomHeadCode newAxiomHeadStep (raw_succ M predecessor)
        axiomAt oldAxiom haxiomAt
        (raw_codedAssignmentPrepend_tail M
          axiomHeadCode axiomHeadStep axiom bound
          newAxiomHeadCode newAxiomHeadStep predecessor oldAxiom
          haxiomHeadPrepend hpredecessor holdAxiom)).
    }
    subst witnessAt. subst axiomAt.
    exact (hrows predecessor oldWitness oldAxiom
      hpredecessor holdWitness holdAxiom).
Qed.

End PABoundedRawCodedPAAxiomWitnessContextCons.
