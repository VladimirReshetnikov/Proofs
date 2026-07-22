(**
  All-occurrences hierarchy bounds for model-internal proof contexts.

  The user-facing restriction is not merely a bound on the final formula.
  Every formula displayed in every proof-node context must have at most the
  fixed external number of quantifier groups.  For a formula code this means
  that at least one polarity rank is bounded: either it lies in the Sigma
  domain or it lies in the Pi domain at that external level.

  This file applies that disjunction to every head in one honest context-list
  traversal.  The universal formula ranges over model elements and therefore
  also covers nonstandard context lengths.  No external list decoder is used.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedContextLists RawCodedFixedLevelTruth.

Import ListNotations.

Module PABoundedRawCodedContextBounds.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedFixedLevelTruth.

Definition RawFormulaQuantifierBounded (M : RawPAModel)
    (level : nat) (code : M) : Prop :=
  RawFixedLevelSigmaDomain M level code \/
  RawFixedLevelPiDomain M level code.

Arguments RawFormulaQuantifierBounded M level code : clear implicits.

Definition formulaQuantifierBoundedTermAt
    (level : nat) (code : term) : formula :=
  pOr
    (fixedLevelSigmaDomainTermAt level code)
    (fixedLevelPiDomainTermAt level code).

Lemma raw_sat_formulaQuantifierBoundedTermAt_iff : forall
    (M : RawPAModel) e level code,
  raw_formula_sat M e
    (formulaQuantifierBoundedTermAt level code) <->
  RawFormulaQuantifierBounded M level (raw_term_eval M e code).
Proof.
  intros M e level code.
  unfold formulaQuantifierBoundedTermAt, RawFormulaQuantifierBounded.
  cbn [raw_formula_sat].
  rewrite raw_sat_fixedLevelSigmaDomainTermAt_iff,
    raw_sat_fixedLevelPiDomainTermAt_iff.
  reflexivity.
Qed.

Lemma raw_contextBound_eval_liftTerm_two : forall (M : RawPAModel)
    a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M a b e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 2) with (S (S i)) by lia. reflexivity.
Qed.

(** The condition is stated functionally in [code]: every value read from a
    live head slot is bounded.  Complete traversal separately guarantees that
    each live slot has such a value. *)
Definition RawContextAllBoundedWithTables (M : RawPAModel)
    (level : nat) (bound headCode headStep : M) : Prop :=
  forall index,
    rawLt M index bound ->
    forall code,
      RawCodedAssignmentLookup M headCode headStep index code ->
      RawFormulaQuantifierBounded M level code.

Arguments RawContextAllBoundedWithTables
  M level bound headCode headStep : clear implicits.

Definition contextAllBoundedWithTablesTermAt
    (level : nat) (bound headCode headStep : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (pAll
        (pImp
          (codedAssignmentLookupTermAt
            (liftTerm 2 headCode) (liftTerm 2 headStep)
            (tVar 1) (tVar 0))
          (formulaQuantifierBoundedTermAt level (tVar 0))))).

Lemma raw_sat_contextAllBoundedWithTablesTermAt_iff : forall
    (M : RawPAModel) e level bound headCode headStep,
  raw_formula_sat M e
    (contextAllBoundedWithTablesTermAt level bound headCode headStep) <->
  RawContextAllBoundedWithTables M level
    (raw_term_eval M e bound)
    (raw_term_eval M e headCode) (raw_term_eval M e headStep).
Proof.
  intros M e level bound headCode headStep.
  unfold contextAllBoundedWithTablesTermAt,
    RawContextAllBoundedWithTables.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_formulaQuantifierBoundedTermAt_iff.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_one.
  repeat setoid_rewrite raw_contextBound_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Public all-boundedness deliberately shares the traversal tables with the
    universal head condition.  This prevents a malformed code from satisfying
    the restriction vacuously by supplying no list entries. *)
Definition RawContextAllBounded (M : RawPAModel)
    (level : nat) (root : M) : Prop :=
  exists bound tailCode tailStep headCode headStep : M,
    RawContextListTraversal M
      root bound tailCode tailStep headCode headStep /\
    RawContextAllBoundedWithTables M level bound headCode headStep.

Arguments RawContextAllBounded M level root : clear implicits.

Definition contextAllBoundedTermAt
    (level : nat) (root : term) : formula :=
  contextListEx5
    (pAnd
      (contextListTraversalTermAt
        (liftTerm 5 root) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0))
      (contextAllBoundedWithTablesTermAt
        level (tVar 4) (tVar 1) (tVar 0))).

Lemma raw_sat_contextAllBoundedTermAt_iff : forall
    (M : RawPAModel) e level root,
  raw_formula_sat M e (contextAllBoundedTermAt level root) <->
  RawContextAllBounded M level (raw_term_eval M e root).
Proof.
  intros M e level root.
  unfold contextAllBoundedTermAt, contextListEx5,
    RawContextAllBounded.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextListTraversalTermAt_iff.
  setoid_rewrite raw_sat_contextAllBoundedWithTablesTermAt_iff.
  setoid_rewrite raw_contextList_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_contextAllBounded_realizable : forall
    (M : RawPAModel) level root,
  RawContextAllBounded M level root ->
  RawContextListRealizable M root.
Proof.
  intros M level root
    (bound & tailCode & tailStep & headCode & headStep & htraversal & _).
  exists bound, tailCode, tailStep, headCode, headStep.
  exact htraversal.
Qed.

(** With a shared table, the all-bounded condition immediately applies to an
    indexed member.  The public version will later follow from traversal
    functionality; keeping this table-relative lemma explicit avoids silently
    assuming that still-separate structural theorem. *)
Lemma raw_contextAllBoundedWithTables_member : forall
    (M : RawPAModel) level bound headCode headStep member,
  RawContextAllBoundedWithTables M level bound headCode headStep ->
  RawContextListMemberWithTables M member bound headCode headStep ->
  RawFormulaQuantifierBounded M level member.
Proof.
  intros M level bound headCode headStep member hall
    [index [hindex hlookup]].
  exact (hall index hindex member hlookup).
Qed.

End PABoundedRawCodedContextBounds.
