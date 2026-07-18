(**
  Pointwise fixed-level truth for model-internal coded contexts.

  Soundness of a natural-deduction node is conditional on truth of every
  formula in its context.  The context length and its entries may be
  nonstandard elements of an arbitrary PA model, so this condition must use
  the same certified list-spine traversal as [RawCodedContextLists]; decoding
  the public context code in Rocq would only cover standard naturals.

  We deliberately use Sigma truth one level above the advertised proof bound
  as the unified notion of truth.  The rank-gap and coherence modules later
  show that every formula bounded at the proof level has this orientation.
  This file is structural: it defines the pointwise predicate, proves exact
  formula semantics, and establishes the empty/cons laws needed by the
  assumption, implication-introduction, disjunction-elimination, and
  existential-elimination rules.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedContextLists RawCodedContextStructure RawCodedContextFunctionality
  RawCodedFixedLevelTruthTraversal.

Import ListNotations.

Module PABoundedRawCodedFixedLevelContextTruth.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextFunctionality.
Import PABoundedRawCodedFixedLevelTruthTraversal.

(** A table-relative condition is the useful induction interface: every
    value read from a live head slot has a complete Sigma-truth certificate
    under the one fixed coded assignment.  Quantifying over all lookup values
    avoids silently relying on beta functionality in the definition. *)
Definition RawContextAllSigmaTrueWithTables (M : RawPAModel)
    (level : nat)
    (bound headCode headStep assignmentCode assignmentStep : M) : Prop :=
  forall index,
    rawLt M index bound ->
    forall code,
      RawCodedAssignmentLookup M headCode headStep index code ->
      RawFixedLevelSigmaTruthCertificate M level
        code assignmentCode assignmentStep.

Arguments RawContextAllSigmaTrueWithTables
  M level bound headCode headStep assignmentCode assignmentStep
  : clear implicits.

Definition contextAllSigmaTrueWithTablesTermAt (level : nat)
    (bound headCode headStep assignmentCode assignmentStep : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (pAll
        (pImp
          (codedAssignmentLookupTermAt
            (liftTerm 2 headCode) (liftTerm 2 headStep)
            (tVar 1) (tVar 0))
          (fixedLevelSigmaTruthCertificateTermAt level
            (tVar 0) (liftTerm 2 assignmentCode)
            (liftTerm 2 assignmentStep))))).

Lemma raw_fixedContextTruth_eval_liftTerm_two : forall
    (M : RawPAModel) a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M a b e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 2) with (S (S i)) by lia. reflexivity.
Qed.

Lemma raw_sat_contextAllSigmaTrueWithTablesTermAt_iff : forall
    (M : RawPAModel) e level bound headCode headStep
      assignmentCode assignmentStep,
  raw_formula_sat M e
    (contextAllSigmaTrueWithTablesTermAt level
      bound headCode headStep assignmentCode assignmentStep) <->
  RawContextAllSigmaTrueWithTables M level
    (raw_term_eval M e bound)
    (raw_term_eval M e headCode) (raw_term_eval M e headStep)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intros M e level bound headCode headStep assignmentCode assignmentStep.
  unfold contextAllSigmaTrueWithTablesTermAt,
    RawContextAllSigmaTrueWithTables.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_one.
  repeat setoid_rewrite raw_fixedContextTruth_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The public predicate existentially hides one complete context traversal.
    Sharing its head table with the pointwise truth condition prevents a
    malformed context code from satisfying the latter vacuously. *)
Definition RawContextAllSigmaTrue (M : RawPAModel)
    (level : nat) (root assignmentCode assignmentStep : M) : Prop :=
  exists bound tailCode tailStep headCode headStep : M,
    RawContextListTraversal M
      root bound tailCode tailStep headCode headStep /\
    RawContextAllSigmaTrueWithTables M level
      bound headCode headStep assignmentCode assignmentStep.

Arguments RawContextAllSigmaTrue
  M level root assignmentCode assignmentStep : clear implicits.

Definition contextAllSigmaTrueTermAt (level : nat)
    (root assignmentCode assignmentStep : term) : formula :=
  contextListEx5
    (pAnd
      (contextListTraversalTermAt
        (liftTerm 5 root) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0))
      (contextAllSigmaTrueWithTablesTermAt level
        (tVar 4) (tVar 1) (tVar 0)
        (liftTerm 5 assignmentCode) (liftTerm 5 assignmentStep))).

Lemma raw_sat_contextAllSigmaTrueTermAt_iff : forall
    (M : RawPAModel) e level root assignmentCode assignmentStep,
  raw_formula_sat M e
    (contextAllSigmaTrueTermAt level root assignmentCode assignmentStep) <->
  RawContextAllSigmaTrue M level
    (raw_term_eval M e root)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intros M e level root assignmentCode assignmentStep.
  unfold contextAllSigmaTrueTermAt, contextListEx5,
    RawContextAllSigmaTrue.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextListTraversalTermAt_iff.
  setoid_rewrite raw_sat_contextAllSigmaTrueWithTablesTermAt_iff.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_contextAllSigmaTrue_realizable : forall
    (M : RawPAModel) level root assignmentCode assignmentStep,
  RawContextAllSigmaTrue M level root assignmentCode assignmentStep ->
  RawContextListRealizable M root.
Proof.
  intros M level root assignmentCode assignmentStep
    (bound & tailCode & tailStep & headCode & headStep & htraversal & _).
  exists bound, tailCode, tailStep, headCode, headStep.
  exact htraversal.
Qed.

(** Membership and pointwise truth must refer to the same head table.  This
    is the table-relative elimination rule used inside proof-code induction;
    the public form follows later from the already proved traversal
    functionality when independently packaged context witnesses meet. *)
Lemma raw_contextAllSigmaTrueWithTables_member : forall
    (M : RawPAModel) level bound headCode headStep
      assignmentCode assignmentStep member,
  RawContextAllSigmaTrueWithTables M level
    bound headCode headStep assignmentCode assignmentStep ->
  RawContextListMemberWithTables M member bound headCode headStep ->
  RawFixedLevelSigmaTruthCertificate M level
    member assignmentCode assignmentStep.
Proof.
  intros M level bound headCode headStep assignmentCode assignmentStep
    member hall [index [hindex hlookup]].
  exact (hall index hindex member hlookup).
Qed.

(** The empty list uses the already constructed honest zero-length context
    traversal; its pointwise truth condition has no live index. *)
Theorem raw_contextAllSigmaTrue_empty : forall
    (M : RawPAModel), RawPASatisfies M -> forall level assignmentCode assignmentStep,
  RawContextAllSigmaTrue M level (raw_zero M)
    assignmentCode assignmentStep.
Proof.
  intros M hPA level assignmentCode assignmentStep.
  destruct (raw_contextList_zero_traversal_exists M hPA)
    as (tailCode & tailStep & htraversal).
  exists (raw_zero M), tailCode, tailStep, (raw_zero M), (raw_zero M).
  split; [exact htraversal |].
  intros index hindex code _.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

(** Adjoining a true head preserves pointwise truth.  The proof uses the
    exact head-table beta prepend supplied by the context-structure module;
    it works for an arbitrary, possibly nonstandard old length. *)
Theorem raw_contextAllSigmaTrue_cons : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      level root head assignmentCode assignmentStep,
  RawContextAllSigmaTrue M level root assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M level
    head assignmentCode assignmentStep ->
  RawContextAllSigmaTrue M level (rawListNode M head root)
    assignmentCode assignmentStep.
Proof.
  intros M hPA level root head assignmentCode assignmentStep
    (bound & tailCode & tailStep & headCode & headStep &
      htraversal & hall) hhead.
  destruct (raw_contextListConsExtension_exists M hPA
    root head bound tailCode tailStep headCode headStep htraversal)
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
    subst code. exact hhead.
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
      (proj1 (proj2 (proj2 htraversal))) hheadPrepend
      predecessor hpredBound code)) in hlookup.
    exact (hall predecessor hpredBound code hlookup).
Qed.

End PABoundedRawCodedFixedLevelContextTruth.
