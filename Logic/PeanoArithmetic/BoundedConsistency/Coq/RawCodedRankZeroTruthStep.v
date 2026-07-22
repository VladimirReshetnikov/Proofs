(**
  Local rank-zero truth rows over arbitrary raw PA models.

  Equality atoms read their two term values from a beta-coded term table.
  Boolean constructors read the truth bits of their child formulae from a
  second beta table.  Every row is a genuine first-order PA formula and has
  exact semantics for arbitrary carrier elements, including nonstandard
  codes.  Quantifier constructors deliberately have no row at rank zero.

  As with coded-term evaluation, this file isolates the local Tarski clauses
  from the later model-internal traversal that constructs a complete table.
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

Module PABoundedRawCodedRankZeroTruthStep.

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
    Truth bits and their Boolean operations. *)

Definition rawTruthOne (M : RawPAModel) : M := rawNumeralValue M 1.

Definition RawTruthBit (M : RawPAModel) (value : M) : Prop :=
  value = raw_zero M \/ value = rawTruthOne M.

Definition truthBitTermAt (value : term) : formula :=
  pOr (pEq value tZero) (pEq value (Term.numeral 1)).

Definition RawEqualityTruth (M : RawPAModel)
    (output leftValue rightValue : M) : Prop :=
  (leftValue = rightValue /\ output = rawTruthOne M) \/
  (leftValue <> rightValue /\ output = raw_zero M).

Definition RawImpTruth (M : RawPAModel)
    (output left right : M) : Prop :=
  RawTruthBit M left /\ RawTruthBit M right /\ RawTruthBit M output /\
  (((left = rawTruthOne M /\ right = raw_zero M) /\
      output = raw_zero M) \/
   ((left = raw_zero M \/ right = rawTruthOne M) /\
      output = rawTruthOne M)).

Definition RawAndTruth (M : RawPAModel)
    (output left right : M) : Prop :=
  RawTruthBit M left /\ RawTruthBit M right /\ RawTruthBit M output /\
  (((left = rawTruthOne M /\ right = rawTruthOne M) /\
      output = rawTruthOne M) \/
   ((left = raw_zero M \/ right = raw_zero M) /\
      output = raw_zero M)).

Definition RawOrTruth (M : RawPAModel)
    (output left right : M) : Prop :=
  RawTruthBit M left /\ RawTruthBit M right /\ RawTruthBit M output /\
  (((left = rawTruthOne M \/ right = rawTruthOne M) /\
      output = rawTruthOne M) \/
   ((left = raw_zero M /\ right = raw_zero M) /\
      output = raw_zero M)).

Arguments rawTruthOne M : clear implicits.
Arguments RawTruthBit M value : clear implicits.
Arguments RawEqualityTruth M output leftValue rightValue : clear implicits.
Arguments RawImpTruth M output left right : clear implicits.
Arguments RawAndTruth M output left right : clear implicits.
Arguments RawOrTruth M output left right : clear implicits.

Definition equalityTruthTermAt
    (output leftValue rightValue : term) : formula :=
  pOr
    (pAnd (pEq leftValue rightValue)
      (pEq output (Term.numeral 1)))
    (pAnd (pImp (pEq leftValue rightValue) pBot)
      (pEq output tZero)).

Definition impTruthTermAt (output left right : term) : formula :=
  pAnd4
    (truthBitTermAt left)
    (truthBitTermAt right)
    (truthBitTermAt output)
    (pOr
      (pAnd (pAnd
        (pEq left (Term.numeral 1)) (pEq right tZero))
        (pEq output tZero))
      (pAnd (pOr
        (pEq left tZero) (pEq right (Term.numeral 1)))
        (pEq output (Term.numeral 1)))).

Definition andTruthTermAt (output left right : term) : formula :=
  pAnd4
    (truthBitTermAt left)
    (truthBitTermAt right)
    (truthBitTermAt output)
    (pOr
      (pAnd (pAnd
        (pEq left (Term.numeral 1))
        (pEq right (Term.numeral 1)))
        (pEq output (Term.numeral 1)))
      (pAnd (pOr (pEq left tZero) (pEq right tZero))
        (pEq output tZero))).

Definition orTruthTermAt (output left right : term) : formula :=
  pAnd4
    (truthBitTermAt left)
    (truthBitTermAt right)
    (truthBitTermAt output)
    (pOr
      (pAnd (pOr
        (pEq left (Term.numeral 1))
        (pEq right (Term.numeral 1)))
        (pEq output (Term.numeral 1)))
      (pAnd (pAnd (pEq left tZero) (pEq right tZero))
        (pEq output tZero))).

Lemma raw_sat_truthBitTermAt_iff : forall (M : RawPAModel) e value,
  raw_formula_sat M e (truthBitTermAt value) <->
  RawTruthBit M (raw_term_eval M e value).
Proof.
  intros. unfold truthBitTermAt, RawTruthBit, rawTruthOne.
  cbn [raw_formula_sat]. rewrite raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_sat_equalityTruthTermAt_iff :
  forall (M : RawPAModel) e output leftValue rightValue,
  raw_formula_sat M e
    (equalityTruthTermAt output leftValue rightValue) <->
  RawEqualityTruth M
    (raw_term_eval M e output)
    (raw_term_eval M e leftValue) (raw_term_eval M e rightValue).
Proof.
  intros. unfold equalityTruthTermAt, RawEqualityTruth, rawTruthOne.
  cbn [raw_formula_sat]. rewrite raw_term_eval_numeral.
  tauto.
Qed.

Lemma raw_sat_impTruthTermAt_iff :
  forall (M : RawPAModel) e output left right,
  raw_formula_sat M e (impTruthTermAt output left right) <->
  RawImpTruth M
    (raw_term_eval M e output)
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold impTruthTermAt, RawImpTruth, pAnd4.
  cbn [raw_formula_sat].
  rewrite !raw_sat_truthBitTermAt_iff, !raw_term_eval_numeral.
  reflexivity.
Qed.

Lemma raw_sat_andTruthTermAt_iff :
  forall (M : RawPAModel) e output left right,
  raw_formula_sat M e (andTruthTermAt output left right) <->
  RawAndTruth M
    (raw_term_eval M e output)
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold andTruthTermAt, RawAndTruth, pAnd4.
  cbn [raw_formula_sat].
  rewrite !raw_sat_truthBitTermAt_iff, !raw_term_eval_numeral.
  reflexivity.
Qed.

Lemma raw_sat_orTruthTermAt_iff :
  forall (M : RawPAModel) e output left right,
  raw_formula_sat M e (orTruthTermAt output left right) <->
  RawOrTruth M
    (raw_term_eval M e output)
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold orTruthTermAt, RawOrTruth, pAnd4.
  cbn [raw_formula_sat].
  rewrite !raw_sat_truthBitTermAt_iff, !raw_term_eval_numeral.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Constructor rows. *)

Definition RawFormulaEqTruthRow (M : RawPAModel)
    (code output termTableCode termTableStep
      left leftValue right rightValue : M) : Prop :=
  code = rawFormulaEqCode M left right /\
  RawCodedAssignmentLookup M termTableCode termTableStep left leftValue /\
  RawCodedAssignmentLookup M termTableCode termTableStep right rightValue /\
  RawEqualityTruth M output leftValue rightValue.

Definition RawFormulaBotTruthRow (M : RawPAModel)
    (code output : M) : Prop :=
  code = rawFormulaBotCode M /\ output = raw_zero M.

Definition RawFormulaImpTruthRow (M : RawPAModel)
    (code output truthTableCode truthTableStep
      left leftTruth right rightTruth : M) : Prop :=
  code = rawFormulaImpCode M left right /\
  RawCodedAssignmentLookup M truthTableCode truthTableStep left leftTruth /\
  RawCodedAssignmentLookup M truthTableCode truthTableStep right rightTruth /\
  RawImpTruth M output leftTruth rightTruth.

Definition RawFormulaAndTruthRow (M : RawPAModel)
    (code output truthTableCode truthTableStep
      left leftTruth right rightTruth : M) : Prop :=
  code = rawFormulaAndCode M left right /\
  RawCodedAssignmentLookup M truthTableCode truthTableStep left leftTruth /\
  RawCodedAssignmentLookup M truthTableCode truthTableStep right rightTruth /\
  RawAndTruth M output leftTruth rightTruth.

Definition RawFormulaOrTruthRow (M : RawPAModel)
    (code output truthTableCode truthTableStep
      left leftTruth right rightTruth : M) : Prop :=
  code = rawFormulaOrCode M left right /\
  RawCodedAssignmentLookup M truthTableCode truthTableStep left leftTruth /\
  RawCodedAssignmentLookup M truthTableCode truthTableStep right rightTruth /\
  RawOrTruth M output leftTruth rightTruth.

Arguments RawFormulaEqTruthRow
  M code output termTableCode termTableStep left leftValue right rightValue
  : clear implicits.
Arguments RawFormulaBotTruthRow M code output : clear implicits.
Arguments RawFormulaImpTruthRow
  M code output truthTableCode truthTableStep left leftTruth right rightTruth
  : clear implicits.
Arguments RawFormulaAndTruthRow
  M code output truthTableCode truthTableStep left leftTruth right rightTruth
  : clear implicits.
Arguments RawFormulaOrTruthRow
  M code output truthTableCode truthTableStep left leftTruth right rightTruth
  : clear implicits.

Definition formulaEqTruthRowTermAt
    (code output termTableCode termTableStep
      left leftValue right rightValue : term) : formula :=
  pAnd4
    (formulaEqCodeTermAt code left right)
    (codedAssignmentLookupTermAt termTableCode termTableStep left leftValue)
    (codedAssignmentLookupTermAt termTableCode termTableStep right rightValue)
    (equalityTruthTermAt output leftValue rightValue).

Definition formulaBotTruthRowTermAt (code output : term) : formula :=
  pAnd (formulaBotCodeTermAt code) (pEq output tZero).

Definition formulaImpTruthRowTermAt
    (code output truthTableCode truthTableStep
      left leftTruth right rightTruth : term) : formula :=
  pAnd4
    (formulaImpCodeTermAt code left right)
    (codedAssignmentLookupTermAt truthTableCode truthTableStep left leftTruth)
    (codedAssignmentLookupTermAt truthTableCode truthTableStep right rightTruth)
    (impTruthTermAt output leftTruth rightTruth).

Definition formulaAndTruthRowTermAt
    (code output truthTableCode truthTableStep
      left leftTruth right rightTruth : term) : formula :=
  pAnd4
    (formulaAndCodeTermAt code left right)
    (codedAssignmentLookupTermAt truthTableCode truthTableStep left leftTruth)
    (codedAssignmentLookupTermAt truthTableCode truthTableStep right rightTruth)
    (andTruthTermAt output leftTruth rightTruth).

Definition formulaOrTruthRowTermAt
    (code output truthTableCode truthTableStep
      left leftTruth right rightTruth : term) : formula :=
  pAnd4
    (formulaOrCodeTermAt code left right)
    (codedAssignmentLookupTermAt truthTableCode truthTableStep left leftTruth)
    (codedAssignmentLookupTermAt truthTableCode truthTableStep right rightTruth)
    (orTruthTermAt output leftTruth rightTruth).

Lemma raw_sat_formulaEqTruthRowTermAt_iff :
  forall (M : RawPAModel) e code output termTableCode termTableStep
    left leftValue right rightValue,
  raw_formula_sat M e
    (formulaEqTruthRowTermAt code output termTableCode termTableStep
      left leftValue right rightValue) <->
  RawFormulaEqTruthRow M
    (raw_term_eval M e code) (raw_term_eval M e output)
    (raw_term_eval M e termTableCode) (raw_term_eval M e termTableStep)
    (raw_term_eval M e left) (raw_term_eval M e leftValue)
    (raw_term_eval M e right) (raw_term_eval M e rightValue).
Proof.
  intros. unfold formulaEqTruthRowTermAt, RawFormulaEqTruthRow, pAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaEqCodeTermAt_iff,
    !raw_sat_codedAssignmentLookupTermAt_iff,
    raw_sat_equalityTruthTermAt_iff.
  reflexivity.
Qed.

Lemma raw_sat_formulaBotTruthRowTermAt_iff :
  forall (M : RawPAModel) e code output,
  raw_formula_sat M e (formulaBotTruthRowTermAt code output) <->
  RawFormulaBotTruthRow M
    (raw_term_eval M e code) (raw_term_eval M e output).
Proof.
  intros. unfold formulaBotTruthRowTermAt, RawFormulaBotTruthRow.
  cbn [raw_formula_sat]. rewrite raw_sat_formulaBotCodeTermAt_iff.
  reflexivity.
Qed.

Lemma raw_sat_formulaImpTruthRowTermAt_iff :
  forall (M : RawPAModel) e code output truthTableCode truthTableStep
    left leftTruth right rightTruth,
  raw_formula_sat M e
    (formulaImpTruthRowTermAt code output truthTableCode truthTableStep
      left leftTruth right rightTruth) <->
  RawFormulaImpTruthRow M
    (raw_term_eval M e code) (raw_term_eval M e output)
    (raw_term_eval M e truthTableCode) (raw_term_eval M e truthTableStep)
    (raw_term_eval M e left) (raw_term_eval M e leftTruth)
    (raw_term_eval M e right) (raw_term_eval M e rightTruth).
Proof.
  intros. unfold formulaImpTruthRowTermAt, RawFormulaImpTruthRow, pAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaImpCodeTermAt_iff,
    !raw_sat_codedAssignmentLookupTermAt_iff,
    raw_sat_impTruthTermAt_iff.
  reflexivity.
Qed.

Lemma raw_sat_formulaAndTruthRowTermAt_iff :
  forall (M : RawPAModel) e code output truthTableCode truthTableStep
    left leftTruth right rightTruth,
  raw_formula_sat M e
    (formulaAndTruthRowTermAt code output truthTableCode truthTableStep
      left leftTruth right rightTruth) <->
  RawFormulaAndTruthRow M
    (raw_term_eval M e code) (raw_term_eval M e output)
    (raw_term_eval M e truthTableCode) (raw_term_eval M e truthTableStep)
    (raw_term_eval M e left) (raw_term_eval M e leftTruth)
    (raw_term_eval M e right) (raw_term_eval M e rightTruth).
Proof.
  intros. unfold formulaAndTruthRowTermAt, RawFormulaAndTruthRow, pAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaAndCodeTermAt_iff,
    !raw_sat_codedAssignmentLookupTermAt_iff,
    raw_sat_andTruthTermAt_iff.
  reflexivity.
Qed.

Lemma raw_sat_formulaOrTruthRowTermAt_iff :
  forall (M : RawPAModel) e code output truthTableCode truthTableStep
    left leftTruth right rightTruth,
  raw_formula_sat M e
    (formulaOrTruthRowTermAt code output truthTableCode truthTableStep
      left leftTruth right rightTruth) <->
  RawFormulaOrTruthRow M
    (raw_term_eval M e code) (raw_term_eval M e output)
    (raw_term_eval M e truthTableCode) (raw_term_eval M e truthTableStep)
    (raw_term_eval M e left) (raw_term_eval M e leftTruth)
    (raw_term_eval M e right) (raw_term_eval M e rightTruth).
Proof.
  intros. unfold formulaOrTruthRowTermAt, RawFormulaOrTruthRow, pAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaOrCodeTermAt_iff,
    !raw_sat_codedAssignmentLookupTermAt_iff,
    raw_sat_orTruthTermAt_iff.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Unified rank-zero row.  The four generic witnesses are interpreted as
    term values in the equality branch and as truth bits in Boolean branches. *)

Definition rankZeroTruthWitnessRowTermAt
    (code output termTableCode termTableStep truthTableCode truthTableStep
      left leftValue right rightValue : term) : formula :=
  pOr
    (formulaEqTruthRowTermAt code output termTableCode termTableStep
      left leftValue right rightValue)
    (pOr
      (formulaBotTruthRowTermAt code output)
      (pOr
        (formulaImpTruthRowTermAt code output truthTableCode truthTableStep
          left leftValue right rightValue)
        (pOr
          (formulaAndTruthRowTermAt code output truthTableCode truthTableStep
            left leftValue right rightValue)
          (formulaOrTruthRowTermAt code output truthTableCode truthTableStep
            left leftValue right rightValue)))).

Definition RawRankZeroTruthWitnessRow (M : RawPAModel)
    (code output termTableCode termTableStep truthTableCode truthTableStep
      left leftValue right rightValue : M) : Prop :=
  RawFormulaEqTruthRow M code output termTableCode termTableStep
      left leftValue right rightValue \/
  RawFormulaBotTruthRow M code output \/
  RawFormulaImpTruthRow M code output truthTableCode truthTableStep
      left leftValue right rightValue \/
  RawFormulaAndTruthRow M code output truthTableCode truthTableStep
      left leftValue right rightValue \/
  RawFormulaOrTruthRow M code output truthTableCode truthTableStep
      left leftValue right rightValue.

Arguments RawRankZeroTruthWitnessRow
  M code output termTableCode termTableStep truthTableCode truthTableStep
    left leftValue right rightValue : clear implicits.

Lemma raw_sat_rankZeroTruthWitnessRowTermAt_iff :
  forall (M : RawPAModel) e
    code output termTableCode termTableStep truthTableCode truthTableStep
    left leftValue right rightValue,
  raw_formula_sat M e
    (rankZeroTruthWitnessRowTermAt
      code output termTableCode termTableStep truthTableCode truthTableStep
      left leftValue right rightValue) <->
  RawRankZeroTruthWitnessRow M
    (raw_term_eval M e code) (raw_term_eval M e output)
    (raw_term_eval M e termTableCode) (raw_term_eval M e termTableStep)
    (raw_term_eval M e truthTableCode) (raw_term_eval M e truthTableStep)
    (raw_term_eval M e left) (raw_term_eval M e leftValue)
    (raw_term_eval M e right) (raw_term_eval M e rightValue).
Proof.
  intros. unfold rankZeroTruthWitnessRowTermAt,
    RawRankZeroTruthWitnessRow.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaEqTruthRowTermAt_iff,
    raw_sat_formulaBotTruthRowTermAt_iff,
    raw_sat_formulaImpTruthRowTermAt_iff,
    raw_sat_formulaAndTruthRowTermAt_iff,
    raw_sat_formulaOrTruthRowTermAt_iff.
  reflexivity.
Qed.

Definition rankZeroTruthStepTermAt
    (code output termTableCode termTableStep truthTableCode truthTableStep
      : term) : formula :=
  pEx4
    (rankZeroTruthWitnessRowTermAt
      (liftTerm 4 code) (liftTerm 4 output)
      (liftTerm 4 termTableCode) (liftTerm 4 termTableStep)
      (liftTerm 4 truthTableCode) (liftTerm 4 truthTableStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)).

Definition RawRankZeroTruthStep (M : RawPAModel)
    (code output termTableCode termTableStep truthTableCode truthTableStep : M)
    : Prop :=
  exists left leftValue right rightValue : M,
    RawRankZeroTruthWitnessRow M
      code output termTableCode termTableStep truthTableCode truthTableStep
      left leftValue right rightValue.

Arguments RawRankZeroTruthStep
  M code output termTableCode termTableStep truthTableCode truthTableStep
  : clear implicits.

Lemma raw_term_eval_liftTerm_four_truth : forall (M : RawPAModel)
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

Lemma raw_sat_rankZeroTruthStepTermAt_iff :
  forall (M : RawPAModel) e
    code output termTableCode termTableStep truthTableCode truthTableStep,
  raw_formula_sat M e
    (rankZeroTruthStepTermAt code output
      termTableCode termTableStep truthTableCode truthTableStep) <->
  RawRankZeroTruthStep M
    (raw_term_eval M e code) (raw_term_eval M e output)
    (raw_term_eval M e termTableCode) (raw_term_eval M e termTableStep)
    (raw_term_eval M e truthTableCode) (raw_term_eval M e truthTableStep).
Proof.
  intros M e code output termTableCode termTableStep
    truthTableCode truthTableStep.
  unfold rankZeroTruthStepTermAt, RawRankZeroTruthStep, pEx4.
  cbn [raw_formula_sat]. split.
  - intros [left [leftValue [right [rightValue hrow]]]].
    exists left, leftValue, right, rightValue.
    apply (proj1 (raw_sat_rankZeroTruthWitnessRowTermAt_iff
      M (scons M rightValue
        (scons M right (scons M leftValue (scons M left e))))
      (liftTerm 4 code) (liftTerm 4 output)
      (liftTerm 4 termTableCode) (liftTerm 4 termTableStep)
      (liftTerm 4 truthTableCode) (liftTerm 4 truthTableStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))) in hrow.
    rewrite !raw_term_eval_liftTerm_four_truth in hrow.
    cbn [raw_term_eval scons] in hrow. exact hrow.
  - intros [left [leftValue [right [rightValue hrow]]]].
    exists left, leftValue, right, rightValue.
    apply (proj2 (raw_sat_rankZeroTruthWitnessRowTermAt_iff
      M (scons M rightValue
        (scons M right (scons M leftValue (scons M left e))))
      (liftTerm 4 code) (liftTerm 4 output)
      (liftTerm 4 termTableCode) (liftTerm 4 termTableStep)
      (liftTerm 4 truthTableCode) (liftTerm 4 truthTableStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))).
    rewrite !raw_term_eval_liftTerm_four_truth.
    cbn [raw_term_eval scons]. exact hrow.
Qed.

(** Every successful local row proposes an actual Boolean bit. *)
Theorem raw_rankZeroTruthStep_output_bit : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall code output termTableCode termTableStep truthTableCode truthTableStep,
  RawRankZeroTruthStep M code output
    termTableCode termTableStep truthTableCode truthTableStep ->
  RawTruthBit M output.
Proof.
  intros M hPA code output termTableCode termTableStep
    truthTableCode truthTableStep
    [left [leftValue [right [rightValue hrow]]]].
  destruct hrow as [heq | [hbot | [himp | [hand | hor]]]].
  - destruct heq as [_ [_ [_ [[_ hout] | [_ hout]]]]];
      unfold RawTruthBit; [right | left]; exact hout.
  - destruct hbot as [_ hout]. unfold RawTruthBit. left. exact hout.
  - destruct himp as [_ [_ [_ himpTruth]]].
    destruct himpTruth as [_ [_ [hout _]]]. exact hout.
  - destruct hand as [_ [_ [_ handTruth]]].
    destruct handTruth as [_ [_ [hout _]]]. exact hout.
  - destruct hor as [_ [_ [_ horTruth]]].
    destruct horTruth as [_ [_ [hout _]]]. exact hout.
Qed.

End PABoundedRawCodedRankZeroTruthStep.
