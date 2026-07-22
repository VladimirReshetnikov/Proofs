(**
  Local evaluation rows for nonstandard codes of PA terms.

  A later partial-truth predicate must evaluate a term code inside an
  arbitrary (and possibly nonstandard) model of PA.  Recursing in Rocq over a
  carrier element would only cover standard codes, so this file exposes one
  evaluator row as a genuine PA formula.  Recursive child values are read
  from a beta-coded table; variables are read from the independent beta-coded
  de Bruijn assignment supplied by [RawCodedAssignment].

  The rows below are intentionally local.  They prove the exact Tarski
  equations for each of the five constructors without assuming that a global
  table exists.  Totality of a model-internal traversal is a separate theorem
  and therefore cannot be hidden in the definition of a row.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment.

Import ListNotations.

Module PABoundedRawCodedTermEvaluationStep.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.

(** ------------------------------------------------------------------
    Raw semantic rows. *)

Definition RawTermVarEvaluationRow (M : RawPAModel)
    (code value assignmentCode assignmentStep index : M) : Prop :=
  code = rawTermVarCode M index /\
  RawCodedAssignmentLookup M assignmentCode assignmentStep index value.

Definition RawTermZeroEvaluationRow (M : RawPAModel)
    (code value : M) : Prop :=
  code = rawTermZeroCode M /\ value = raw_zero M.

Definition RawTermSuccEvaluationRow (M : RawPAModel)
    (code value tableCode tableStep child childValue : M) : Prop :=
  code = rawTermSuccCode M child /\
  RawCodedAssignmentLookup M tableCode tableStep child childValue /\
  value = raw_succ M childValue.

Definition RawTermAddEvaluationRow (M : RawPAModel)
    (code value tableCode tableStep
      left leftValue right rightValue : M) : Prop :=
  code = rawTermAddCode M left right /\
  RawCodedAssignmentLookup M tableCode tableStep left leftValue /\
  RawCodedAssignmentLookup M tableCode tableStep right rightValue /\
  value = raw_add M leftValue rightValue.

Definition RawTermMulEvaluationRow (M : RawPAModel)
    (code value tableCode tableStep
      left leftValue right rightValue : M) : Prop :=
  code = rawTermMulCode M left right /\
  RawCodedAssignmentLookup M tableCode tableStep left leftValue /\
  RawCodedAssignmentLookup M tableCode tableStep right rightValue /\
  value = raw_mul M leftValue rightValue.

Arguments RawTermVarEvaluationRow
  M code value assignmentCode assignmentStep index : clear implicits.
Arguments RawTermZeroEvaluationRow M code value : clear implicits.
Arguments RawTermSuccEvaluationRow
  M code value tableCode tableStep child childValue : clear implicits.
Arguments RawTermAddEvaluationRow
  M code value tableCode tableStep left leftValue right rightValue
  : clear implicits.
Arguments RawTermMulEvaluationRow
  M code value tableCode tableStep left leftValue right rightValue
  : clear implicits.

(** ------------------------------------------------------------------
    Term-parametric PA formulae for the five rows. *)

Definition termVarEvaluationRowTermAt
    (code value assignmentCode assignmentStep index : term) : formula :=
  pAnd
    (termVarCodeTermAt code index)
    (codedAssignmentLookupTermAt
      assignmentCode assignmentStep index value).

Definition termZeroEvaluationRowTermAt
    (code value : term) : formula :=
  pAnd
    (termZeroCodeTermAt code)
    (pEq value tZero).

Definition termSuccEvaluationRowTermAt
    (code value tableCode tableStep child childValue : term) : formula :=
  pAnd3
    (termSuccCodeTermAt code child)
    (codedAssignmentLookupTermAt tableCode tableStep child childValue)
    (pEq value (tSucc childValue)).

Definition termAddEvaluationRowTermAt
    (code value tableCode tableStep
      left leftValue right rightValue : term) : formula :=
  pAnd4
    (termAddCodeTermAt code left right)
    (codedAssignmentLookupTermAt tableCode tableStep left leftValue)
    (codedAssignmentLookupTermAt tableCode tableStep right rightValue)
    (pEq value (tAdd leftValue rightValue)).

Definition termMulEvaluationRowTermAt
    (code value tableCode tableStep
      left leftValue right rightValue : term) : formula :=
  pAnd4
    (termMulCodeTermAt code left right)
    (codedAssignmentLookupTermAt tableCode tableStep left leftValue)
    (codedAssignmentLookupTermAt tableCode tableStep right rightValue)
    (pEq value (tMul leftValue rightValue)).

Lemma raw_sat_termVarEvaluationRowTermAt_iff :
  forall (M : RawPAModel) e code value assignmentCode assignmentStep index,
  raw_formula_sat M e
    (termVarEvaluationRowTermAt
      code value assignmentCode assignmentStep index) <->
  RawTermVarEvaluationRow M
    (raw_term_eval M e code) (raw_term_eval M e value)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)
    (raw_term_eval M e index).
Proof.
  intros. unfold termVarEvaluationRowTermAt, RawTermVarEvaluationRow.
  cbn [raw_formula_sat].
  rewrite raw_sat_termVarCodeTermAt_iff,
    raw_sat_codedAssignmentLookupTermAt_iff.
  reflexivity.
Qed.

Lemma raw_sat_termZeroEvaluationRowTermAt_iff :
  forall (M : RawPAModel) e code value,
  raw_formula_sat M e (termZeroEvaluationRowTermAt code value) <->
  RawTermZeroEvaluationRow M
    (raw_term_eval M e code) (raw_term_eval M e value).
Proof.
  intros. unfold termZeroEvaluationRowTermAt, RawTermZeroEvaluationRow.
  cbn [raw_formula_sat]. rewrite raw_sat_termZeroCodeTermAt_iff.
  reflexivity.
Qed.

Lemma raw_sat_termSuccEvaluationRowTermAt_iff :
  forall (M : RawPAModel) e code value tableCode tableStep child childValue,
  raw_formula_sat M e
    (termSuccEvaluationRowTermAt
      code value tableCode tableStep child childValue) <->
  RawTermSuccEvaluationRow M
    (raw_term_eval M e code) (raw_term_eval M e value)
    (raw_term_eval M e tableCode) (raw_term_eval M e tableStep)
    (raw_term_eval M e child) (raw_term_eval M e childValue).
Proof.
  intros. unfold termSuccEvaluationRowTermAt,
    RawTermSuccEvaluationRow, pAnd3.
  cbn [raw_formula_sat].
  rewrite raw_sat_termSuccCodeTermAt_iff,
    raw_sat_codedAssignmentLookupTermAt_iff.
  reflexivity.
Qed.

Lemma raw_sat_termAddEvaluationRowTermAt_iff :
  forall (M : RawPAModel) e code value tableCode tableStep
    left leftValue right rightValue,
  raw_formula_sat M e
    (termAddEvaluationRowTermAt code value tableCode tableStep
      left leftValue right rightValue) <->
  RawTermAddEvaluationRow M
    (raw_term_eval M e code) (raw_term_eval M e value)
    (raw_term_eval M e tableCode) (raw_term_eval M e tableStep)
    (raw_term_eval M e left) (raw_term_eval M e leftValue)
    (raw_term_eval M e right) (raw_term_eval M e rightValue).
Proof.
  intros. unfold termAddEvaluationRowTermAt,
    RawTermAddEvaluationRow, pAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_termAddCodeTermAt_iff,
    !raw_sat_codedAssignmentLookupTermAt_iff.
  reflexivity.
Qed.

Lemma raw_sat_termMulEvaluationRowTermAt_iff :
  forall (M : RawPAModel) e code value tableCode tableStep
    left leftValue right rightValue,
  raw_formula_sat M e
    (termMulEvaluationRowTermAt code value tableCode tableStep
      left leftValue right rightValue) <->
  RawTermMulEvaluationRow M
    (raw_term_eval M e code) (raw_term_eval M e value)
    (raw_term_eval M e tableCode) (raw_term_eval M e tableStep)
    (raw_term_eval M e left) (raw_term_eval M e leftValue)
    (raw_term_eval M e right) (raw_term_eval M e rightValue).
Proof.
  intros. unfold termMulEvaluationRowTermAt,
    RawTermMulEvaluationRow, pAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_termMulCodeTermAt_iff,
    !raw_sat_codedAssignmentLookupTermAt_iff.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    One row with existentially hidden constructor witnesses. *)

Definition termEvaluationWitnessRowTermAt
    (code value assignmentCode assignmentStep tableCode tableStep
      left leftValue right rightValue : term) : formula :=
  pOr
    (termVarEvaluationRowTermAt
      code value assignmentCode assignmentStep left)
    (pOr
      (termZeroEvaluationRowTermAt code value)
      (pOr
        (termSuccEvaluationRowTermAt
          code value tableCode tableStep left leftValue)
        (pOr
          (termAddEvaluationRowTermAt
            code value tableCode tableStep
            left leftValue right rightValue)
          (termMulEvaluationRowTermAt
            code value tableCode tableStep
            left leftValue right rightValue)))).

Definition RawTermEvaluationWitnessRow (M : RawPAModel)
    (code value assignmentCode assignmentStep tableCode tableStep
      left leftValue right rightValue : M) : Prop :=
  RawTermVarEvaluationRow M
      code value assignmentCode assignmentStep left \/
  RawTermZeroEvaluationRow M code value \/
  RawTermSuccEvaluationRow M
      code value tableCode tableStep left leftValue \/
  RawTermAddEvaluationRow M
      code value tableCode tableStep left leftValue right rightValue \/
  RawTermMulEvaluationRow M
      code value tableCode tableStep left leftValue right rightValue.

Arguments RawTermEvaluationWitnessRow
  M code value assignmentCode assignmentStep tableCode tableStep
    left leftValue right rightValue : clear implicits.

Lemma raw_sat_termEvaluationWitnessRowTermAt_iff :
  forall (M : RawPAModel) e
    code value assignmentCode assignmentStep tableCode tableStep
    left leftValue right rightValue,
  raw_formula_sat M e
    (termEvaluationWitnessRowTermAt
      code value assignmentCode assignmentStep tableCode tableStep
      left leftValue right rightValue) <->
  RawTermEvaluationWitnessRow M
    (raw_term_eval M e code) (raw_term_eval M e value)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)
    (raw_term_eval M e tableCode) (raw_term_eval M e tableStep)
    (raw_term_eval M e left) (raw_term_eval M e leftValue)
    (raw_term_eval M e right) (raw_term_eval M e rightValue).
Proof.
  intros. unfold termEvaluationWitnessRowTermAt,
    RawTermEvaluationWitnessRow.
  cbn [raw_formula_sat].
  rewrite raw_sat_termVarEvaluationRowTermAt_iff,
    raw_sat_termZeroEvaluationRowTermAt_iff,
    raw_sat_termSuccEvaluationRowTermAt_iff,
    raw_sat_termAddEvaluationRowTermAt_iff,
    raw_sat_termMulEvaluationRowTermAt_iff.
  reflexivity.
Qed.

(** Four witnesses suffice for every constructor.  Unary and nullary rows
    simply ignore the unused right-hand slots.  Under [pEx4], the outermost
    witness is variable three and the innermost witness is variable zero. *)
Definition termEvaluationStepTermAt
    (code value assignmentCode assignmentStep tableCode tableStep : term)
    : formula :=
  pEx4
    (termEvaluationWitnessRowTermAt
      (liftTerm 4 code) (liftTerm 4 value)
      (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
      (liftTerm 4 tableCode) (liftTerm 4 tableStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)).

Definition RawTermEvaluationStep (M : RawPAModel)
    (code value assignmentCode assignmentStep tableCode tableStep : M)
    : Prop :=
  exists left leftValue right rightValue : M,
    RawTermEvaluationWitnessRow M
      code value assignmentCode assignmentStep tableCode tableStep
      left leftValue right rightValue.

Arguments RawTermEvaluationStep
  M code value assignmentCode assignmentStep tableCode tableStep
  : clear implicits.

Lemma raw_term_eval_liftTerm_four_step : forall (M : RawPAModel)
    a b c d (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d e))))
    (liftTerm 4 t) = raw_term_eval M e t.
Proof.
  intros M a b c d e t. unfold liftTerm.
  rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro i.
  replace (i + 4) with (S (S (S (S i)))) by lia.
  reflexivity.
Qed.

Lemma raw_sat_termEvaluationStepTermAt_iff :
  forall (M : RawPAModel) e
    code value assignmentCode assignmentStep tableCode tableStep,
  raw_formula_sat M e
    (termEvaluationStepTermAt
      code value assignmentCode assignmentStep tableCode tableStep) <->
  RawTermEvaluationStep M
    (raw_term_eval M e code) (raw_term_eval M e value)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)
    (raw_term_eval M e tableCode) (raw_term_eval M e tableStep).
Proof.
  intros M e code value assignmentCode assignmentStep tableCode tableStep.
  unfold termEvaluationStepTermAt, RawTermEvaluationStep, pEx4.
  cbn [raw_formula_sat].
  split.
  - intros [left [leftValue [right [rightValue hrow]]]].
    exists left, leftValue, right, rightValue.
    apply (proj1 (raw_sat_termEvaluationWitnessRowTermAt_iff
      M (scons M rightValue
        (scons M right (scons M leftValue (scons M left e))))
      (liftTerm 4 code) (liftTerm 4 value)
      (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
      (liftTerm 4 tableCode) (liftTerm 4 tableStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))) in hrow.
    rewrite !raw_term_eval_liftTerm_four_step in hrow.
    cbn [raw_term_eval scons] in hrow.
    exact hrow.
  - intros [left [leftValue [right [rightValue hrow]]]].
    exists left, leftValue, right, rightValue.
    apply (proj2 (raw_sat_termEvaluationWitnessRowTermAt_iff
      M (scons M rightValue
        (scons M right (scons M leftValue (scons M left e))))
      (liftTerm 4 code) (liftTerm 4 value)
      (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
      (liftTerm 4 tableCode) (liftTerm 4 tableStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))).
    rewrite !raw_term_eval_liftTerm_four_step.
    cbn [raw_term_eval scons].
    exact hrow.
Qed.

(** Within any fixed constructor row, the output equation is deterministic
    once the referenced table/assignment entries are fixed.  Constructor
    disjointness and a total table traversal are deliberately not assumed. *)
Lemma raw_termVarEvaluationRow_value_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code assignmentCode assignmentStep index left right : M,
  RawTermVarEvaluationRow M
    code left assignmentCode assignmentStep index ->
  RawTermVarEvaluationRow M
    code right assignmentCode assignmentStep index ->
  left = right.
Proof.
  intros M hPA code assignmentCode assignmentStep index left right
    [_ hleft] [_ hright].
  exact (raw_codedAssignmentLookup_functional M hPA
    assignmentCode assignmentStep index left right hleft hright).
Qed.

Lemma raw_termZeroEvaluationRow_value_functional :
  forall (M : RawPAModel) code left right,
  RawTermZeroEvaluationRow M code left ->
  RawTermZeroEvaluationRow M code right ->
  left = right.
Proof.
  intros M code left right [_ hleft] [_ hright].
  now rewrite hleft, hright.
Qed.

Lemma raw_termSuccEvaluationRow_value_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code tableCode tableStep child childValue left right : M,
  RawTermSuccEvaluationRow M
    code left tableCode tableStep child childValue ->
  RawTermSuccEvaluationRow M
    code right tableCode tableStep child childValue ->
  left = right.
Proof.
  intros M hPA code tableCode tableStep child childValue left right
    [_ [_ hleft]] [_ [_ hright]].
  now rewrite hleft, hright.
Qed.

Lemma raw_termAddEvaluationRow_value_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code tableCode tableStep
    l lv r rv left right : M,
  RawTermAddEvaluationRow M
    code left tableCode tableStep l lv r rv ->
  RawTermAddEvaluationRow M
    code right tableCode tableStep l lv r rv ->
  left = right.
Proof.
  intros M hPA code tableCode tableStep l lv r rv left right
    [_ [_ [_ hleft]]] [_ [_ [_ hright]]].
  now rewrite hleft, hright.
Qed.

Lemma raw_termMulEvaluationRow_value_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code tableCode tableStep
    l lv r rv left right : M,
  RawTermMulEvaluationRow M
    code left tableCode tableStep l lv r rv ->
  RawTermMulEvaluationRow M
    code right tableCode tableStep l lv r rv ->
  left = right.
Proof.
  intros M hPA code tableCode tableStep l lv r rv left right
    [_ [_ [_ hleft]]] [_ [_ [_ hright]]].
  now rewrite hleft, hright.
Qed.

End PABoundedRawCodedTermEvaluationStep.
