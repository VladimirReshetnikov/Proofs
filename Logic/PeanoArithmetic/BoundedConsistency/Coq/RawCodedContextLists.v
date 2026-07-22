(**
  Model-internal traversal of canonically coded formula contexts.

  A natural-deduction proof node stores its context as the same polynomial
  list code used everywhere else in this development.  An external call to
  [decode] would say nothing about a nonstandard carrier element, so this
  module gives the list spine an honest arithmetic certificate instead.

  Two beta tables are synchronized along a model-valued length.  The first
  stores successive tail codes, beginning at the public context code and
  ending at zero; the second stores the corresponding heads.  Every live row
  asserts the transparent equation

      currentTail = node(head, nextTail).

  Membership is then witnessed by a model-internal index into the head table.
  All definitions below are genuine PA formulae, and the semantic theorems
  hold in arbitrary raw arithmetic structures.  No standard decoder and no
  metatheoretic recursion over a raw-model element is used.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment.

Import ListNotations.

Module PABoundedRawCodedContextLists.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.

Definition contextListAnd4 (a b c d : formula) : formula :=
  pAnd a (pAnd b (pAnd c d)).

Definition contextListEx3 (body : formula) : formula :=
  pEx (pEx (pEx body)).

Definition contextListEx5 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx body)))).

(** Small lift lemmas are kept local so this context interface does not need
    to import any term-evaluation traversal merely for binder bookkeeping. *)
Lemma raw_contextList_eval_liftTerm_one : forall (M : RawPAModel)
    a (e : nat -> M) t,
  raw_term_eval M (scons M a e) (liftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M a e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 1) with (S i) by lia. reflexivity.
Qed.

Lemma raw_contextList_eval_liftTerm_three : forall (M : RawPAModel)
    a b c (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b (scons M c e)))
    (liftTerm 3 t) = raw_term_eval M e t.
Proof.
  intros M a b c e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 3) with (S (S (S i))) by lia. reflexivity.
Qed.

Lemma raw_contextList_eval_liftTerm_five : forall (M : RawPAModel)
    a b c d f (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d (scons M f e)))))
    (liftTerm 5 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 5) with (S (S (S (S (S i))))) by lia. reflexivity.
Qed.

(** ------------------------------------------------------------------
    One synchronized list-spine row. *)

(** The three witnesses are [currentTail], [nextTail], and [head], in that
    order.  At the body they occupy variables two, one, and zero. *)
Definition contextListRowTermAt
    (tailCode tailStep headCode headStep index : term) : formula :=
  contextListEx3
    (contextListAnd4
      (codedAssignmentLookupTermAt
        (liftTerm 3 tailCode) (liftTerm 3 tailStep)
        (liftTerm 3 index) (tVar 2))
      (codedAssignmentLookupTermAt
        (liftTerm 3 tailCode) (liftTerm 3 tailStep)
        (liftTerm 3 (tSucc index)) (tVar 1))
      (codedAssignmentLookupTermAt
        (liftTerm 3 headCode) (liftTerm 3 headStep)
        (liftTerm 3 index) (tVar 0))
      (pEq (tVar 2) (nodeTerm (tVar 0) (tVar 1)))).

Definition RawContextListRow (M : RawPAModel)
    (tailCode tailStep headCode headStep index : M) : Prop :=
  exists currentTail nextTail head : M,
    RawCodedAssignmentLookup M tailCode tailStep index currentTail /\
    RawCodedAssignmentLookup M tailCode tailStep
      (raw_succ M index) nextTail /\
    RawCodedAssignmentLookup M headCode headStep index head /\
    currentTail = rawListNode M head nextTail.

Arguments RawContextListRow
  M tailCode tailStep headCode headStep index : clear implicits.

Lemma raw_sat_contextListRowTermAt_iff : forall
    (M : RawPAModel) e tailCode tailStep headCode headStep index,
  raw_formula_sat M e
    (contextListRowTermAt tailCode tailStep headCode headStep index) <->
  RawContextListRow M
    (raw_term_eval M e tailCode) (raw_term_eval M e tailStep)
    (raw_term_eval M e headCode) (raw_term_eval M e headStep)
    (raw_term_eval M e index).
Proof.
  intros M e tailCode tailStep headCode headStep index.
  unfold contextListRowTermAt, contextListEx3, contextListAnd4,
    RawContextListRow.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  repeat setoid_rewrite raw_eval_nodeTerm.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    A complete context-list traversal. *)

Definition RawContextListTraversal (M : RawPAModel)
    (root bound tailCode tailStep headCode headStep : M) : Prop :=
  RawCodedAssignmentLookup M tailCode tailStep (raw_zero M) root /\
  RawCodedAssignmentLookup M tailCode tailStep bound (raw_zero M) /\
  RawCodedAssignmentDefinedThrough M headCode headStep bound /\
  forall index,
    rawLt M index bound ->
    RawContextListRow M tailCode tailStep headCode headStep index.

Arguments RawContextListTraversal
  M root bound tailCode tailStep headCode headStep : clear implicits.

Definition contextListTraversalTermAt
    (root bound tailCode tailStep headCode headStep : term) : formula :=
  contextListAnd4
    (codedAssignmentLookupTermAt tailCode tailStep tZero root)
    (codedAssignmentLookupTermAt tailCode tailStep bound tZero)
    (codedAssignmentDefinedThroughTermAt headCode headStep bound)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
        (contextListRowTermAt
          (liftTerm 1 tailCode) (liftTerm 1 tailStep)
          (liftTerm 1 headCode) (liftTerm 1 headStep) (tVar 0)))).

Lemma raw_sat_contextListTraversalTermAt_iff : forall
    (M : RawPAModel) e root bound tailCode tailStep headCode headStep,
  raw_formula_sat M e
    (contextListTraversalTermAt
      root bound tailCode tailStep headCode headStep) <->
  RawContextListTraversal M
    (raw_term_eval M e root) (raw_term_eval M e bound)
    (raw_term_eval M e tailCode) (raw_term_eval M e tailStep)
    (raw_term_eval M e headCode) (raw_term_eval M e headStep).
Proof.
  intros M e root bound tailCode tailStep headCode headStep.
  unfold contextListTraversalTermAt, contextListAnd4,
    RawContextListTraversal.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentLookupTermAt_iff,
    raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_contextListRowTermAt_iff.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Membership relative to one complete traversal. *)

Definition RawContextListMemberWithTables (M : RawPAModel)
    (member bound headCode headStep : M) : Prop :=
  exists index : M,
    rawLt M index bound /\
    RawCodedAssignmentLookup M headCode headStep index member.

Arguments RawContextListMemberWithTables
  M member bound headCode headStep : clear implicits.

Definition contextListMemberWithTablesTermAt
    (member bound headCode headStep : term) : formula :=
  pEx
    (pAnd
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (codedAssignmentLookupTermAt
        (liftTerm 1 headCode) (liftTerm 1 headStep)
        (tVar 0) (liftTerm 1 member))).

Lemma raw_sat_contextListMemberWithTablesTermAt_iff : forall
    (M : RawPAModel) e member bound headCode headStep,
  raw_formula_sat M e
    (contextListMemberWithTablesTermAt member bound headCode headStep) <->
  RawContextListMemberWithTables M
    (raw_term_eval M e member) (raw_term_eval M e bound)
    (raw_term_eval M e headCode) (raw_term_eval M e headStep).
Proof.
  intros M e member bound headCode headStep.
  unfold contextListMemberWithTablesTermAt,
    RawContextListMemberWithTables.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The public context domain existentially hides the model-internal length
    and both synchronized beta tables. *)
Definition RawContextListRealizable (M : RawPAModel) (root : M) : Prop :=
  exists bound tailCode tailStep headCode headStep : M,
    RawContextListTraversal M
      root bound tailCode tailStep headCode headStep.

Arguments RawContextListRealizable M root : clear implicits.

Definition contextListRealizableTermAt (root : term) : formula :=
  contextListEx5
    (contextListTraversalTermAt
      (liftTerm 5 root) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0)).

Lemma raw_sat_contextListRealizableTermAt_iff : forall
    (M : RawPAModel) e root,
  raw_formula_sat M e (contextListRealizableTermAt root) <->
  RawContextListRealizable M (raw_term_eval M e root).
Proof.
  intros M e root.
  unfold contextListRealizableTermAt, contextListEx5,
    RawContextListRealizable.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextListTraversalTermAt_iff.
  setoid_rewrite raw_contextList_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Public membership uses one and the same traversal both to establish that
    the context code really terminates and to expose the indexed head. *)
Definition RawContextListMember (M : RawPAModel)
    (root member : M) : Prop :=
  exists bound tailCode tailStep headCode headStep : M,
    RawContextListTraversal M
      root bound tailCode tailStep headCode headStep /\
    RawContextListMemberWithTables M member bound headCode headStep.

Arguments RawContextListMember M root member : clear implicits.

Definition contextListMemberTermAt (root member : term) : formula :=
  contextListEx5
    (pAnd
      (contextListTraversalTermAt
        (liftTerm 5 root) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0))
      (contextListMemberWithTablesTermAt
        (liftTerm 5 member) (tVar 4) (tVar 1) (tVar 0))).

Lemma raw_sat_contextListMemberTermAt_iff : forall
    (M : RawPAModel) e root member,
  raw_formula_sat M e (contextListMemberTermAt root member) <->
  RawContextListMember M
    (raw_term_eval M e root) (raw_term_eval M e member).
Proof.
  intros M e root member.
  unfold contextListMemberTermAt, contextListEx5,
    RawContextListMember.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextListTraversalTermAt_iff.
  setoid_rewrite raw_sat_contextListMemberWithTablesTermAt_iff.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** A member witness automatically supplies the honest context domain. *)
Lemma raw_contextListMember_realizable : forall
    (M : RawPAModel) root member,
  RawContextListMember M root member ->
  RawContextListRealizable M root.
Proof.
  intros M root member
    (bound & tailCode & tailStep & headCode & headStep & htraversal & _).
  exists bound, tailCode, tailStep, headCode, headStep.
  exact htraversal.
Qed.

End PABoundedRawCodedContextLists.
