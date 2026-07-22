(**
  Exact constructors for the syntax side of closure unsealing.

  [RawCodedUniversalClosureSelfInstantiationThrough] contains no proof-tree
  data: it is only a bounded family of represented formula-substitution
  graphs.  These lemmas show how to assemble that family one prefix at a
  time.  At a successor, functionality of universal closure identifies any
  advertised prefix at the boundary with the concrete prefix certificate
  supplied by the caller.
*)

From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations
  RawCodedPAUniversalClosureProofReduction.

Module PABoundedRawCodedPAUniversalClosureSelfInstantiation.

Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedPAUniversalClosureProofReduction.

(** There are no strict closure prefixes below zero. *)
Lemma raw_codedUniversalClosureSelfInstantiationThrough_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement body,
  RawCodedUniversalClosureSelfInstantiationThrough M
    replacement body (raw_zero M).
Proof.
  intros M hPA replacement body count prefix hcount _.
  exfalso. exact (raw_not_lt_zero M hPA count hcount).
Qed.

(** Extend the bounded family by one exact prefix substitution graph.

    The boundary prefix is supplied explicitly rather than selected by an
    existential callback.  If another closure trace advertises a prefix at
    the same count, graph functionality proves that it is this same code. *)
Theorem raw_codedUniversalClosureSelfInstantiationThrough_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement body limit limitPrefix,
  RawCodedUniversalClosureSelfInstantiationThrough M
    replacement body limit ->
  RawCodedUniversalClosure M limit body limitPrefix ->
  RawCodedFormulaSingleSubstitution M
    replacement limitPrefix limitPrefix ->
  RawCodedUniversalClosureSelfInstantiationThrough M
    replacement body (raw_succ M limit).
Proof.
  intros M hPA replacement body limit limitPrefix
    hthrough hlimitPrefix hlimitSubstitution.
  intros count prefix hcount hprefix.
  destruct (raw_lt_succ_cases M hPA count limit hcount)
    as [hbelow | hboundary].
  - exact (hthrough count prefix hbelow hprefix).
  - subst count.
    assert (hprefixEq : prefix = limitPrefix).
    {
      exact (raw_codedUniversalClosure_functional M hPA
        limit body prefix limitPrefix hprefix hlimitPrefix).
    }
    subst prefix. exact hlimitSubstitution.
Qed.

End PABoundedRawCodedPAUniversalClosureSelfInstantiation.
