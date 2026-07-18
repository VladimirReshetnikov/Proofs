(**
  Beta-coded global traversal for evaluation of nonstandard PA term codes.

  A value beta table is arithmetically total, so it cannot itself distinguish
  genuine term codes from malformed numbers.  We therefore carry a second
  beta table of support flags.  Flag one means that the code belongs to the
  finite dependency closure of the requested root.  Every supported code
  below the traversal bound has a local evaluation row, and every recursive
  child named by that row is supported as well.

  The formulae below are transparent first-order PA formulae.  Their semantic
  characterizations hold in every law-free raw arithmetic structure.  The
  main functionality theorem then uses a genuine PA induction instance to
  compare two possibly nonstandard traversals; it never performs Rocq
  induction over a carrier element.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedSyntaxConstructors RawCodedSyntaxConstructorSeparation
  RawCodedAssignment RawCodedTermEvaluationStep
  PolynomialPairInjectivity RawCodedTermEvaluationStepFunctionality.

Import ListNotations.

Module PABoundedRawCodedTermEvaluationTraversal.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedTermEvaluationStep.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedTermEvaluationStepFunctionality.

(** ------------------------------------------------------------------
    Supported local rows. *)

Definition rawTermCodeSupported (M : RawPAModel)
    (supportCode supportStep code : M) : Prop :=
  RawCodedAssignmentLookup M supportCode supportStep code
    (rawNumeralValue M 1).

Arguments rawTermCodeSupported M supportCode supportStep code
  : clear implicits.

Definition termCodeSupportedTermAt
    (supportCode supportStep code : term) : formula :=
  codedAssignmentLookupTermAt supportCode supportStep code
    (Term.numeral 1).

Lemma raw_sat_termCodeSupportedTermAt_iff : forall (M : RawPAModel)
    e supportCode supportStep code,
  raw_formula_sat M e
    (termCodeSupportedTermAt supportCode supportStep code) <->
  rawTermCodeSupported M
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e code).
Proof.
  intros. unfold termCodeSupportedTermAt, rawTermCodeSupported.
  rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  rewrite raw_term_eval_numeral. reflexivity.
Qed.

Definition termSuccEvaluationClosedRowTermAt
    (code value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep child childValue : term) : formula :=
  pAnd3
    (termSuccEvaluationRowTermAt
      code value tableCode tableStep child childValue)
    (termCodeSupportedTermAt supportCode supportStep child)
    (Formula.ltTermAt child code).

Definition termAddEvaluationClosedRowTermAt
    (code value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep left leftValue right rightValue : term)
    : formula :=
  pAnd
    (termAddEvaluationRowTermAt code value tableCode tableStep
      left leftValue right rightValue)
    (pAnd4
      (termCodeSupportedTermAt supportCode supportStep left)
      (termCodeSupportedTermAt supportCode supportStep right)
      (Formula.ltTermAt left code)
      (Formula.ltTermAt right code)).

Definition termMulEvaluationClosedRowTermAt
    (code value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep left leftValue right rightValue : term)
    : formula :=
  pAnd
    (termMulEvaluationRowTermAt code value tableCode tableStep
      left leftValue right rightValue)
    (pAnd4
      (termCodeSupportedTermAt supportCode supportStep left)
      (termCodeSupportedTermAt supportCode supportStep right)
      (Formula.ltTermAt left code)
      (Formula.ltTermAt right code)).

Definition termEvaluationClosedWitnessRowTermAt
    (code value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep left leftValue right rightValue : term)
    : formula :=
  pOr
    (termVarEvaluationRowTermAt
      code value assignmentCode assignmentStep left)
    (pOr
      (termZeroEvaluationRowTermAt code value)
      (pOr
        (termSuccEvaluationClosedRowTermAt
          code value assignmentCode assignmentStep tableCode tableStep
          supportCode supportStep left leftValue)
        (pOr
          (termAddEvaluationClosedRowTermAt
            code value assignmentCode assignmentStep tableCode tableStep
            supportCode supportStep left leftValue right rightValue)
          (termMulEvaluationClosedRowTermAt
            code value assignmentCode assignmentStep tableCode tableStep
            supportCode supportStep left leftValue right rightValue)))).

Definition RawTermEvaluationClosedWitnessRow (M : RawPAModel)
    (code value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep left leftValue right rightValue : M) : Prop :=
  RawTermVarEvaluationRow M
      code value assignmentCode assignmentStep left \/
  RawTermZeroEvaluationRow M code value \/
  (RawTermSuccEvaluationRow M
      code value tableCode tableStep left leftValue /\
    rawTermCodeSupported M supportCode supportStep left /\
    rawLt M left code) \/
  (RawTermAddEvaluationRow M
      code value tableCode tableStep left leftValue right rightValue /\
    rawTermCodeSupported M supportCode supportStep left /\
    rawTermCodeSupported M supportCode supportStep right /\
    rawLt M left code /\
    rawLt M right code) \/
  (RawTermMulEvaluationRow M
      code value tableCode tableStep left leftValue right rightValue /\
    rawTermCodeSupported M supportCode supportStep left /\
    rawTermCodeSupported M supportCode supportStep right /\
    rawLt M left code /\
    rawLt M right code).

Arguments RawTermEvaluationClosedWitnessRow
  M code value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep left leftValue right rightValue : clear implicits.

Lemma raw_sat_termEvaluationClosedWitnessRowTermAt_iff : forall
    (M : RawPAModel) e code value assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep
    left leftValue right rightValue,
  raw_formula_sat M e
    (termEvaluationClosedWitnessRowTermAt
      code value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep left leftValue right rightValue) <->
  RawTermEvaluationClosedWitnessRow M
    (raw_term_eval M e code) (raw_term_eval M e value)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)
    (raw_term_eval M e tableCode) (raw_term_eval M e tableStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e left) (raw_term_eval M e leftValue)
    (raw_term_eval M e right) (raw_term_eval M e rightValue).
Proof.
  intros. unfold termEvaluationClosedWitnessRowTermAt,
    termSuccEvaluationClosedRowTermAt,
    termAddEvaluationClosedRowTermAt,
    termMulEvaluationClosedRowTermAt,
    RawTermEvaluationClosedWitnessRow, pAnd3, pAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_termVarEvaluationRowTermAt_iff,
    raw_sat_termZeroEvaluationRowTermAt_iff,
    raw_sat_termSuccEvaluationRowTermAt_iff,
    raw_sat_termAddEvaluationRowTermAt_iff,
    raw_sat_termMulEvaluationRowTermAt_iff,
    !raw_sat_termCodeSupportedTermAt_iff,
    !raw_sat_ltTermAt_iff.
  tauto.
Qed.

Definition termEvaluationClosedStepTermAt
    (code value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep : term) : formula :=
  pEx4
    (termEvaluationClosedWitnessRowTermAt
      (liftTerm 4 code) (liftTerm 4 value)
      (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
      (liftTerm 4 tableCode) (liftTerm 4 tableStep)
      (liftTerm 4 supportCode) (liftTerm 4 supportStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)).

Definition RawTermEvaluationClosedStep (M : RawPAModel)
    (code value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep : M) : Prop :=
  exists left leftValue right rightValue : M,
    RawTermEvaluationClosedWitnessRow M
      code value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep left leftValue right rightValue.

Arguments RawTermEvaluationClosedStep
  M code value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep : clear implicits.

Lemma raw_sat_termEvaluationClosedStepTermAt_iff : forall
    (M : RawPAModel) e code value assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep,
  raw_formula_sat M e
    (termEvaluationClosedStepTermAt
      code value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep) <->
  RawTermEvaluationClosedStep M
    (raw_term_eval M e code) (raw_term_eval M e value)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)
    (raw_term_eval M e tableCode) (raw_term_eval M e tableStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e code value assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep.
  unfold termEvaluationClosedStepTermAt,
    RawTermEvaluationClosedStep, pEx4.
  cbn [raw_formula_sat]. split.
  - intros [left [leftValue [right [rightValue hrow]]]].
    exists left, leftValue, right, rightValue.
    apply (proj1 (raw_sat_termEvaluationClosedWitnessRowTermAt_iff M
      (scons M rightValue
        (scons M right (scons M leftValue (scons M left e))))
      (liftTerm 4 code) (liftTerm 4 value)
      (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
      (liftTerm 4 tableCode) (liftTerm 4 tableStep)
      (liftTerm 4 supportCode) (liftTerm 4 supportStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))) in hrow.
    rewrite !raw_term_eval_liftTerm_four_step in hrow.
    cbn [raw_term_eval scons] in hrow. exact hrow.
  - intros [left [leftValue [right [rightValue hrow]]]].
    exists left, leftValue, right, rightValue.
    apply (proj2 (raw_sat_termEvaluationClosedWitnessRowTermAt_iff M
      (scons M rightValue
        (scons M right (scons M leftValue (scons M left e))))
      (liftTerm 4 code) (liftTerm 4 value)
      (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
      (liftTerm 4 tableCode) (liftTerm 4 tableStep)
      (liftTerm 4 supportCode) (liftTerm 4 supportStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))).
    rewrite !raw_term_eval_liftTerm_four_step.
    cbn [raw_term_eval scons]. exact hrow.
Qed.

(** Erasing the support flags and strict-child certificates recovers the
    local evaluator relation from [RawCodedTermEvaluationStep]. *)
Lemma raw_termEvaluationClosedWitnessRow_forget_support : forall
    (M : RawPAModel) code value assignmentCode assignmentStep
      tableCode tableStep supportCode supportStep
      left leftValue right rightValue,
  RawTermEvaluationClosedWitnessRow M
    code value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep left leftValue right rightValue ->
  RawTermEvaluationWitnessRow M
    code value assignmentCode assignmentStep tableCode tableStep
    left leftValue right rightValue.
Proof.
  intros M code value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep left leftValue right rightValue hrow.
  destruct hrow as
    [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - left. exact hvar.
  - right. left. exact hzero.
  - right. right. left. exact (proj1 hsucc).
  - right. right. right. left. exact (proj1 hadd).
  - right. right. right. right. exact (proj1 hmul).
Qed.

Lemma raw_termEvaluationClosedStep_forget_support : forall
    (M : RawPAModel) code value assignmentCode assignmentStep
      tableCode tableStep supportCode supportStep,
  RawTermEvaluationClosedStep M
    code value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep ->
  RawTermEvaluationStep M
    code value assignmentCode assignmentStep tableCode tableStep.
Proof.
  intros M code value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep
    [left [leftValue [right [rightValue hrow]]]].
  exists left, leftValue, right, rightValue.
  exact (raw_termEvaluationClosedWitnessRow_forget_support M
    code value assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep left leftValue right rightValue hrow).
Qed.

(** ------------------------------------------------------------------
    A globally certified pair of support/value beta tables. *)

Definition RawTermEvaluationTraversal (M : RawPAModel)
    (bound assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M supportCode supportStep bound /\
  RawCodedAssignmentDefinedThrough M tableCode tableStep bound /\
  forall code,
    rawLt M code bound ->
    rawTermCodeSupported M supportCode supportStep code ->
    exists value,
      RawCodedAssignmentLookup M tableCode tableStep code value /\
      RawTermEvaluationClosedStep M
        code value assignmentCode assignmentStep tableCode tableStep
        supportCode supportStep.

Arguments RawTermEvaluationTraversal
  M bound assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep : clear implicits.

Definition termEvaluationTraversalTermAt
    (bound assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep : term) : formula :=
  pAnd3
    (codedAssignmentDefinedThroughTermAt supportCode supportStep bound)
    (codedAssignmentDefinedThroughTermAt tableCode tableStep bound)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
        (pImp
          (termCodeSupportedTermAt
            (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
          (pEx
            (pAnd
              (codedAssignmentLookupTermAt
                (liftTerm 2 tableCode) (liftTerm 2 tableStep)
                (tVar 1) (tVar 0))
              (termEvaluationClosedStepTermAt
                (tVar 1) (tVar 0)
                (liftTerm 2 assignmentCode) (liftTerm 2 assignmentStep)
                (liftTerm 2 tableCode) (liftTerm 2 tableStep)
                (liftTerm 2 supportCode) (liftTerm 2 supportStep))))))).

Lemma raw_term_eval_liftTerm_one_traversal : forall (M : RawPAModel)
    x (e : nat -> M) t,
  raw_term_eval M (scons M x e) (liftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M x e t. unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro i.
  replace (i + 1) with (S i) by lia. reflexivity.
Qed.

Lemma raw_term_eval_liftTerm_two_traversal : forall (M : RawPAModel)
    x y (e : nat -> M) t,
  raw_term_eval M (scons M x (scons M y e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M x y e t. unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro i.
  replace (i + 2) with (S (S i)) by lia. reflexivity.
Qed.

Lemma raw_sat_termEvaluationTraversalTermAt_iff : forall
    (M : RawPAModel) e bound assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep,
  raw_formula_sat M e
    (termEvaluationTraversalTermAt
      bound assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep) <->
  RawTermEvaluationTraversal M
    (raw_term_eval M e bound)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e tableCode) (raw_term_eval M e tableStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e bound assignmentCode assignmentStep
    tableCode tableStep supportCode supportStep.
  unfold termEvaluationTraversalTermAt,
    RawTermEvaluationTraversal, pAnd3.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  split.
  - intros [hsupport [htable hall]].
    split; [exact hsupport |]. split; [exact htable |].
    intros code hcode hsupported.
    assert (hltSat : raw_formula_sat M (scons M code e)
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hcode.
    }
    assert (hsupportedSat : raw_formula_sat M (scons M code e)
        (termCodeSupportedTermAt
          (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))).
    {
      apply (proj2 (raw_sat_termCodeSupportedTermAt_iff M _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hsupported.
    }
    destruct (hall code hltSat hsupportedSat) as [value [hlookup hstep]].
    exists value. split.
    + apply (proj1 (raw_sat_codedAssignmentLookupTermAt_iff
        M _ _ _ _ _)) in hlookup.
      rewrite !raw_term_eval_liftTerm_two_traversal in hlookup.
      cbn [raw_term_eval scons] in hlookup. exact hlookup.
    + apply (proj1 (raw_sat_termEvaluationClosedStepTermAt_iff
        M _ _ _ _ _ _ _ _ _)) in hstep.
      rewrite !raw_term_eval_liftTerm_two_traversal in hstep.
      cbn [raw_term_eval scons] in hstep. exact hstep.
  - intros [hsupport [htable hall]].
    split; [exact hsupport |]. split; [exact htable |].
    intros code hltSat hsupportedSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat) as hcode.
    rewrite raw_term_eval_liftTerm_one_traversal in hcode.
    cbn [raw_term_eval scons] in hcode.
    pose proof (proj1 (raw_sat_termCodeSupportedTermAt_iff M _ _ _ _)
      hsupportedSat) as hsupported.
    rewrite !raw_term_eval_liftTerm_one_traversal in hsupported.
    cbn [raw_term_eval scons] in hsupported.
    destruct (hall code hcode hsupported) as [value [hlookup hstep]].
    exists value. split.
    + apply (proj2 (raw_sat_codedAssignmentLookupTermAt_iff
        M _ _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_two_traversal.
      cbn [raw_term_eval scons]. exact hlookup.
    + apply (proj2 (raw_sat_termEvaluationClosedStepTermAt_iff
        M _ _ _ _ _ _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_two_traversal.
      cbn [raw_term_eval scons]. exact hstep.
Qed.

(** A root certificate exposes both the support bit and the evaluated value.
    Its traversal bound is [succ root], so the universal row condition covers
    the root itself and every smaller child code. *)
Definition RawTermEvaluationCertificateWithTables (M : RawPAModel)
    (root value assignmentCode assignmentStep
      tableCode tableStep supportCode supportStep : M) : Prop :=
  RawTermEvaluationTraversal M (raw_succ M root)
    assignmentCode assignmentStep tableCode tableStep
    supportCode supportStep /\
  rawTermCodeSupported M supportCode supportStep root /\
  RawCodedAssignmentLookup M tableCode tableStep root value.

Definition termEvaluationCertificateWithTablesTermAt
    (root value assignmentCode assignmentStep
      tableCode tableStep supportCode supportStep : term) : formula :=
  pAnd3
    (termEvaluationTraversalTermAt (tSucc root)
      assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep)
    (termCodeSupportedTermAt supportCode supportStep root)
    (codedAssignmentLookupTermAt tableCode tableStep root value).

Lemma raw_sat_termEvaluationCertificateWithTablesTermAt_iff : forall
    (M : RawPAModel) e root value assignmentCode assignmentStep
      tableCode tableStep supportCode supportStep,
  raw_formula_sat M e
    (termEvaluationCertificateWithTablesTermAt
      root value assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep) <->
  RawTermEvaluationCertificateWithTables M
    (raw_term_eval M e root) (raw_term_eval M e value)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e tableCode) (raw_term_eval M e tableStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros. unfold termEvaluationCertificateWithTablesTermAt,
    RawTermEvaluationCertificateWithTables, pAnd3.
  cbn [raw_formula_sat].
  rewrite raw_sat_termEvaluationTraversalTermAt_iff,
    raw_sat_termCodeSupportedTermAt_iff,
    raw_sat_codedAssignmentLookupTermAt_iff.
  reflexivity.
Qed.

Definition termEvaluationCertificateTermAt
    (root value assignmentCode assignmentStep : term) : formula :=
  pEx4
    (termEvaluationCertificateWithTablesTermAt
      (liftTerm 4 root) (liftTerm 4 value)
      (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
      (tVar 1) (tVar 0) (tVar 3) (tVar 2)).

Definition RawTermEvaluationCertificate (M : RawPAModel)
    (root value assignmentCode assignmentStep : M) : Prop :=
  exists supportCode supportStep tableCode tableStep : M,
    RawTermEvaluationCertificateWithTables M
      root value assignmentCode assignmentStep
      tableCode tableStep supportCode supportStep.

Arguments RawTermEvaluationCertificate
  M root value assignmentCode assignmentStep : clear implicits.

Lemma raw_sat_termEvaluationCertificateTermAt_iff : forall
    (M : RawPAModel) e root value assignmentCode assignmentStep,
  raw_formula_sat M e
    (termEvaluationCertificateTermAt
      root value assignmentCode assignmentStep) <->
  RawTermEvaluationCertificate M
    (raw_term_eval M e root) (raw_term_eval M e value)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep).
Proof.
  intros M e root value assignmentCode assignmentStep.
  unfold termEvaluationCertificateTermAt,
    RawTermEvaluationCertificate, pEx4.
  cbn [raw_formula_sat]. split.
  - intros [supportCode [supportStep [tableCode [tableStep hcert]]]].
    exists supportCode, supportStep, tableCode, tableStep.
    apply (proj1 (raw_sat_termEvaluationCertificateWithTablesTermAt_iff
      M (scons M tableStep
        (scons M tableCode (scons M supportStep (scons M supportCode e))))
      (liftTerm 4 root) (liftTerm 4 value)
      (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
      (tVar 1) (tVar 0) (tVar 3) (tVar 2))) in hcert.
    rewrite !raw_term_eval_liftTerm_four_step in hcert.
    cbn [raw_term_eval scons] in hcert. exact hcert.
  - intros [supportCode [supportStep [tableCode [tableStep hcert]]]].
    exists supportCode, supportStep, tableCode, tableStep.
    apply (proj2 (raw_sat_termEvaluationCertificateWithTablesTermAt_iff
      M (scons M tableStep
        (scons M tableCode (scons M supportStep (scons M supportCode e))))
      (liftTerm 4 root) (liftTerm 4 value)
      (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
      (tVar 1) (tVar 0) (tVar 3) (tVar 2))).
    rewrite !raw_term_eval_liftTerm_four_step.
    cbn [raw_term_eval scons]. exact hcert.
Qed.

(** ------------------------------------------------------------------
    PA-definable prefix agreement of two traversals. *)

Definition RawTermEvaluationTablesAgreeBelow (M : RawPAModel)
    (bound leftTableCode leftTableStep leftSupportCode leftSupportStep
      rightTableCode rightTableStep rightSupportCode rightSupportStep : M)
    : Prop :=
  forall code,
    rawLt M code bound ->
    rawTermCodeSupported M leftSupportCode leftSupportStep code ->
    rawTermCodeSupported M rightSupportCode rightSupportStep code ->
    forall leftValue rightValue,
      RawCodedAssignmentLookup M leftTableCode leftTableStep code leftValue ->
      RawCodedAssignmentLookup M rightTableCode rightTableStep code rightValue ->
      leftValue = rightValue.

Arguments RawTermEvaluationTablesAgreeBelow
  M bound leftTableCode leftTableStep leftSupportCode leftSupportStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep
  : clear implicits.

Definition termEvaluationTablesAgreeBelowTermAt
    (bound leftTableCode leftTableStep leftSupportCode leftSupportStep
      rightTableCode rightTableStep rightSupportCode rightSupportStep : term)
    : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (pImp
        (termCodeSupportedTermAt
          (liftTerm 1 leftSupportCode) (liftTerm 1 leftSupportStep) (tVar 0))
        (pImp
          (termCodeSupportedTermAt
            (liftTerm 1 rightSupportCode) (liftTerm 1 rightSupportStep)
            (tVar 0))
          (pAll
            (pImp
              (codedAssignmentLookupTermAt
                (liftTerm 2 leftTableCode) (liftTerm 2 leftTableStep)
                (tVar 1) (tVar 0))
              (pAll
                (pImp
                  (codedAssignmentLookupTermAt
                    (liftTerm 3 rightTableCode)
                    (liftTerm 3 rightTableStep) (tVar 2) (tVar 0))
                  (pEq (tVar 1) (tVar 0))))))))).

Lemma raw_term_eval_liftTerm_three_traversal : forall (M : RawPAModel)
    x y z (e : nat -> M) t,
  raw_term_eval M (scons M x (scons M y (scons M z e)))
    (liftTerm 3 t) = raw_term_eval M e t.
Proof.
  intros M x y z e t. unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro i.
  replace (i + 3) with (S (S (S i))) by lia. reflexivity.
Qed.

Lemma raw_sat_termEvaluationTablesAgreeBelowTermAt_iff : forall
    (M : RawPAModel) e bound
      leftTableCode leftTableStep leftSupportCode leftSupportStep
      rightTableCode rightTableStep rightSupportCode rightSupportStep,
  raw_formula_sat M e
    (termEvaluationTablesAgreeBelowTermAt bound
      leftTableCode leftTableStep leftSupportCode leftSupportStep
      rightTableCode rightTableStep rightSupportCode rightSupportStep) <->
  RawTermEvaluationTablesAgreeBelow M (raw_term_eval M e bound)
    (raw_term_eval M e leftTableCode) (raw_term_eval M e leftTableStep)
    (raw_term_eval M e leftSupportCode) (raw_term_eval M e leftSupportStep)
    (raw_term_eval M e rightTableCode) (raw_term_eval M e rightTableStep)
    (raw_term_eval M e rightSupportCode)
    (raw_term_eval M e rightSupportStep).
Proof.
  intros M e bound leftTableCode leftTableStep
    leftSupportCode leftSupportStep rightTableCode rightTableStep
    rightSupportCode rightSupportStep.
  unfold termEvaluationTablesAgreeBelowTermAt,
    RawTermEvaluationTablesAgreeBelow.
  cbn [raw_formula_sat]. split.
  - intros hall code hcode hleftSupport hrightSupport leftValue rightValue
      hleft hright.
    assert (hltSat : raw_formula_sat M (scons M code e)
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hcode.
    }
    assert (hleftSupportSat : raw_formula_sat M (scons M code e)
        (termCodeSupportedTermAt
          (liftTerm 1 leftSupportCode) (liftTerm 1 leftSupportStep)
          (tVar 0))).
    {
      apply (proj2 (raw_sat_termCodeSupportedTermAt_iff M _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hleftSupport.
    }
    assert (hrightSupportSat : raw_formula_sat M (scons M code e)
        (termCodeSupportedTermAt
          (liftTerm 1 rightSupportCode) (liftTerm 1 rightSupportStep)
          (tVar 0))).
    {
      apply (proj2 (raw_sat_termCodeSupportedTermAt_iff M _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hrightSupport.
    }
    pose proof (hall code hltSat hleftSupportSat hrightSupportSat
      leftValue) as hleftImp.
    assert (hleftSat : raw_formula_sat M
        (scons M leftValue (scons M code e))
        (codedAssignmentLookupTermAt
          (liftTerm 2 leftTableCode) (liftTerm 2 leftTableStep)
          (tVar 1) (tVar 0))).
    {
      apply (proj2 (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_two_traversal.
      cbn [raw_term_eval scons]. exact hleft.
    }
    pose proof (hleftImp hleftSat rightValue) as hrightImp.
    assert (hrightSat : raw_formula_sat M
        (scons M rightValue (scons M leftValue (scons M code e)))
        (codedAssignmentLookupTermAt
          (liftTerm 3 rightTableCode) (liftTerm 3 rightTableStep)
          (tVar 2) (tVar 0))).
    {
      apply (proj2 (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_three_traversal.
      cbn [raw_term_eval scons]. exact hright.
    }
    exact (hrightImp hrightSat).
  - intros hagree code hltSat hleftSupportSat hrightSupportSat leftValue
      hleftSat rightValue hrightSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat) as hcode.
    rewrite raw_term_eval_liftTerm_one_traversal in hcode.
    cbn [raw_term_eval scons] in hcode.
    pose proof (proj1 (raw_sat_termCodeSupportedTermAt_iff M _ _ _ _)
      hleftSupportSat) as hleftSupport.
    rewrite !raw_term_eval_liftTerm_one_traversal in hleftSupport.
    cbn [raw_term_eval scons] in hleftSupport.
    pose proof (proj1 (raw_sat_termCodeSupportedTermAt_iff M _ _ _ _)
      hrightSupportSat) as hrightSupport.
    rewrite !raw_term_eval_liftTerm_one_traversal in hrightSupport.
    cbn [raw_term_eval scons] in hrightSupport.
    pose proof (proj1 (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)
      hleftSat) as hleft.
    rewrite !raw_term_eval_liftTerm_two_traversal in hleft.
    cbn [raw_term_eval scons] in hleft.
    pose proof (proj1 (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)
      hrightSat) as hright.
    rewrite !raw_term_eval_liftTerm_three_traversal in hright.
    cbn [raw_term_eval scons] in hright.
    exact (hagree code hcode hleftSupport hrightSupport
      leftValue rightValue hleft hright).
Qed.

(** Extensionality is the local theorem consumed by the global induction.
    Its premise says that the two tables already agree on supported children
    below the current code.  The explicit child bounds in closed recursive
    rows make precisely those induction hypotheses available. *)
Definition RawTermEvaluationClosedStepExtensionality
    (M : RawPAModel) : Prop :=
  forall assignmentCode assignmentStep
    leftTableCode leftTableStep leftSupportCode leftSupportStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep
    code leftValue rightValue,
  (forall child,
    rawLt M child code ->
    rawTermCodeSupported M leftSupportCode leftSupportStep child ->
    rawTermCodeSupported M rightSupportCode rightSupportStep child ->
    forall leftChildValue rightChildValue,
      RawCodedAssignmentLookup M
        leftTableCode leftTableStep child leftChildValue ->
      RawCodedAssignmentLookup M
        rightTableCode rightTableStep child rightChildValue ->
      leftChildValue = rightChildValue) ->
  RawTermEvaluationClosedStep M
    code leftValue assignmentCode assignmentStep
    leftTableCode leftTableStep leftSupportCode leftSupportStep ->
  RawTermEvaluationClosedStep M
    code rightValue assignmentCode assignmentStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep ->
  leftValue = rightValue.

(** Constructor separation first forces two rows for the same code into the
    same branch.  Polynomial-pair injectivity then identifies their children;
    recursive values are equal by the prefix premise.  Notice that the two
    beta tables may be completely different above the current code. *)
Theorem raw_termEvaluationClosedStep_extensional : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawTermEvaluationClosedStepExtensionality M.
Proof.
  intros M hPA assignmentCode assignmentStep
    leftTableCode leftTableStep leftSupportCode leftSupportStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep
    code leftValue rightValue hchildren
    [l1 [lv1 [r1 [rv1 hleft]]]]
    [l2 [lv2 [r2 [rv2 hright]]]].
  destruct hleft as
    [hvar1 | [hzero1 | [hsucc1 | [hadd1 | hmul1]]]];
  destruct hright as
    [hvar2 | [hzero2 | [hsucc2 | [hadd2 | hmul2]]]].
  - exact (raw_termVarEvaluationRows_value_functional M hPA
      code assignmentCode assignmentStep l1 l2 leftValue rightValue
      hvar1 hvar2).
  - destruct hvar1 as [hc1 _]. destruct hzero2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termZeroCode M hPA l1
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hvar1 as [hc1 _]. destruct hsucc2 as [hsucc2 _].
    destruct hsucc2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termSuccCode M hPA l1 l2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hvar1 as [hc1 _]. destruct hadd2 as [hadd2 _].
    destruct hadd2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termAddCode M hPA l1 l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hvar1 as [hc1 _]. destruct hmul2 as [hmul2 _].
    destruct hmul2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termMulCode M hPA l1 l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hzero1 as [hc1 _]. destruct hvar2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termZeroCode M hPA l2
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hzero1 as [_ hv1]. destruct hzero2 as [_ hv2].
    now rewrite hv1, hv2.
  - destruct hzero1 as [hc1 _]. destruct hsucc2 as [hsucc2 _].
    destruct hsucc2 as [hc2 _].
    exfalso. exact (raw_termZeroCode_neq_termSuccCode M hPA l2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hzero1 as [hc1 _]. destruct hadd2 as [hadd2 _].
    destruct hadd2 as [hc2 _].
    exfalso. exact (raw_termZeroCode_neq_termAddCode M hPA l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hzero1 as [hc1 _]. destruct hmul2 as [hmul2 _].
    destruct hmul2 as [hc2 _].
    exfalso. exact (raw_termZeroCode_neq_termMulCode M hPA l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hsucc1 as [hsucc1 _]. destruct hsucc1 as [hc1 _].
    destruct hvar2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termSuccCode M hPA l2 l1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hsucc1 as [hsucc1 _]. destruct hsucc1 as [hc1 _].
    destruct hzero2 as [hc2 _].
    exfalso. exact (raw_termZeroCode_neq_termSuccCode M hPA l1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hsucc1 as [hsucc1 [hsupport1 hlt1]].
    destruct hsucc2 as [hsucc2 [hsupport2 hlt2]].
    destruct hsucc1 as [hc1 [hlookup1 hvalue1]].
    destruct hsucc2 as [hc2 [hlookup2 hvalue2]].
    assert (hcodes : rawTermSuccCode M l1 = rawTermSuccCode M l2).
    { exact (eq_trans (eq_sym hc1) hc2). }
    unfold rawTermSuccCode in hcodes.
    destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
      _ _ _ _ hcodes) as [_ hchild].
    subst l2.
    assert (hchildValue : lv1 = lv2).
    {
      exact (hchildren l1 hlt1 hsupport1 hsupport2
        lv1 lv2 hlookup1 hlookup2).
    }
    now rewrite hvalue1, hvalue2, hchildValue.
  - destruct hsucc1 as [hsucc1 _]. destruct hsucc1 as [hc1 _].
    destruct hadd2 as [hadd2 _]. destruct hadd2 as [hc2 _].
    exfalso. exact (raw_termSuccCode_neq_termAddCode M hPA l1 l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hsucc1 as [hsucc1 _]. destruct hsucc1 as [hc1 _].
    destruct hmul2 as [hmul2 _]. destruct hmul2 as [hc2 _].
    exfalso. exact (raw_termSuccCode_neq_termMulCode M hPA l1 l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hadd1 as [hadd1 _]. destruct hadd1 as [hc1 _].
    destruct hvar2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termAddCode M hPA l2 l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hadd1 as [hadd1 _]. destruct hadd1 as [hc1 _].
    destruct hzero2 as [hc2 _].
    exfalso. exact (raw_termZeroCode_neq_termAddCode M hPA l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hadd1 as [hadd1 _]. destruct hadd1 as [hc1 _].
    destruct hsucc2 as [hsucc2 _]. destruct hsucc2 as [hc2 _].
    exfalso. exact (raw_termSuccCode_neq_termAddCode M hPA l2 l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hadd1 as
      [hadd1 [hleftSupport1 [hrightSupport1 [hleftLt1 hrightLt1]]]].
    destruct hadd2 as
      [hadd2 [hleftSupport2 [hrightSupport2 [hleftLt2 hrightLt2]]]].
    destruct hadd1 as
      [hc1 [hleftLookup1 [hrightLookup1 hvalue1]]].
    destruct hadd2 as
      [hc2 [hleftLookup2 [hrightLookup2 hvalue2]]].
    assert (hcodes : rawTermAddCode M l1 r1 = rawTermAddCode M l2 r2).
    { exact (eq_trans (eq_sym hc1) hc2). }
    unfold rawTermAddCode in hcodes.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcodes) as [_ [hleftCode hrightCode]].
    subst l2. subst r2.
    assert (hleftValue : lv1 = lv2).
    {
      exact (hchildren l1 hleftLt1 hleftSupport1 hleftSupport2
        lv1 lv2 hleftLookup1 hleftLookup2).
    }
    assert (hrightValue : rv1 = rv2).
    {
      exact (hchildren r1 hrightLt1 hrightSupport1 hrightSupport2
        rv1 rv2 hrightLookup1 hrightLookup2).
    }
    now rewrite hvalue1, hvalue2, hleftValue, hrightValue.
  - destruct hadd1 as [hadd1 _]. destruct hadd1 as [hc1 _].
    destruct hmul2 as [hmul2 _]. destruct hmul2 as [hc2 _].
    exfalso. exact (raw_termAddCode_neq_termMulCode M hPA l1 r1 l2 r2
      (eq_trans (eq_sym hc1) hc2)).
  - destruct hmul1 as [hmul1 _]. destruct hmul1 as [hc1 _].
    destruct hvar2 as [hc2 _].
    exfalso. exact (raw_termVarCode_neq_termMulCode M hPA l2 l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hmul1 as [hmul1 _]. destruct hmul1 as [hc1 _].
    destruct hzero2 as [hc2 _].
    exfalso. exact (raw_termZeroCode_neq_termMulCode M hPA l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hmul1 as [hmul1 _]. destruct hmul1 as [hc1 _].
    destruct hsucc2 as [hsucc2 _]. destruct hsucc2 as [hc2 _].
    exfalso. exact (raw_termSuccCode_neq_termMulCode M hPA l2 l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hmul1 as [hmul1 _]. destruct hmul1 as [hc1 _].
    destruct hadd2 as [hadd2 _]. destruct hadd2 as [hc2 _].
    exfalso. exact (raw_termAddCode_neq_termMulCode M hPA l2 r2 l1 r1
      (eq_trans (eq_sym hc2) hc1)).
  - destruct hmul1 as
      [hmul1 [hleftSupport1 [hrightSupport1 [hleftLt1 hrightLt1]]]].
    destruct hmul2 as
      [hmul2 [hleftSupport2 [hrightSupport2 [hleftLt2 hrightLt2]]]].
    destruct hmul1 as
      [hc1 [hleftLookup1 [hrightLookup1 hvalue1]]].
    destruct hmul2 as
      [hc2 [hleftLookup2 [hrightLookup2 hvalue2]]].
    assert (hcodes : rawTermMulCode M l1 r1 = rawTermMulCode M l2 r2).
    { exact (eq_trans (eq_sym hc1) hc2). }
    unfold rawTermMulCode in hcodes.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcodes) as [_ [hleftCode hrightCode]].
    subst l2. subst r2.
    assert (hleftValue : lv1 = lv2).
    {
      exact (hchildren l1 hleftLt1 hleftSupport1 hleftSupport2
        lv1 lv2 hleftLookup1 hleftLookup2).
    }
    assert (hrightValue : rv1 = rv2).
    {
      exact (hchildren r1 hrightLt1 hrightSupport1 hrightSupport2
        rv1 rv2 hrightLookup1 hrightLookup2).
    }
    now rewrite hvalue1, hvalue2, hleftValue, hrightValue.
Qed.

(** Guarded prefix agreement is the PA induction predicate. *)
Definition termEvaluationTablesAgreeThroughTermAt
    (current limit
      leftTableCode leftTableStep leftSupportCode leftSupportStep
      rightTableCode rightTableStep rightSupportCode rightSupportStep : term)
    : formula :=
  pImp (Formula.leTermAt current limit)
    (termEvaluationTablesAgreeBelowTermAt current
      leftTableCode leftTableStep leftSupportCode leftSupportStep
      rightTableCode rightTableStep rightSupportCode rightSupportStep).

Definition RawTermEvaluationTablesAgreeThrough (M : RawPAModel)
    (current limit
      leftTableCode leftTableStep leftSupportCode leftSupportStep
      rightTableCode rightTableStep rightSupportCode rightSupportStep : M)
    : Prop :=
  rawLe M current limit ->
  RawTermEvaluationTablesAgreeBelow M current
    leftTableCode leftTableStep leftSupportCode leftSupportStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep.

Lemma raw_sat_leTermAt_iff_traversal : forall (M : RawPAModel)
    (a b : term) (e : nat -> M),
  raw_formula_sat M e (Formula.leTermAt a b) <->
  rawLe M (raw_term_eval M e a) (raw_term_eval M e b).
Proof.
  intros M a b e. unfold Formula.leTermAt, rawLe.
  cbn [raw_formula_sat raw_term_eval]. split.
  - intros [d h]. exists d.
    repeat rewrite raw_term_eval_rename_succ in h.
    cbn [raw_term_eval scons] in h. exact h.
  - intros [d h]. exists d.
    repeat rewrite raw_term_eval_rename_succ.
    cbn [raw_term_eval scons]. exact h.
Qed.

Lemma raw_sat_termEvaluationTablesAgreeThroughTermAt_iff : forall
    (M : RawPAModel) e current limit
      leftTableCode leftTableStep leftSupportCode leftSupportStep
      rightTableCode rightTableStep rightSupportCode rightSupportStep,
  raw_formula_sat M e
    (termEvaluationTablesAgreeThroughTermAt current limit
      leftTableCode leftTableStep leftSupportCode leftSupportStep
      rightTableCode rightTableStep rightSupportCode rightSupportStep) <->
  RawTermEvaluationTablesAgreeThrough M
    (raw_term_eval M e current) (raw_term_eval M e limit)
    (raw_term_eval M e leftTableCode) (raw_term_eval M e leftTableStep)
    (raw_term_eval M e leftSupportCode) (raw_term_eval M e leftSupportStep)
    (raw_term_eval M e rightTableCode) (raw_term_eval M e rightTableStep)
    (raw_term_eval M e rightSupportCode)
    (raw_term_eval M e rightSupportStep).
Proof.
  intros. unfold termEvaluationTablesAgreeThroughTermAt,
    RawTermEvaluationTablesAgreeThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_traversal,
    raw_sat_termEvaluationTablesAgreeBelowTermAt_iff.
  tauto.
Qed.

Lemma raw_lt_of_succ_le_traversal : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y,
  rawLe M (raw_succ M x) y -> rawLt M x y.
Proof.
  intros M hPA x y [gap hgap]. exists gap.
  rewrite raw_add_succ by exact hPA.
  rewrite <- raw_succ_add_pair by exact hPA.
  exact hgap.
Qed.

Lemma raw_le_refl_traversal : forall (M : RawPAModel),
  RawPASatisfies M -> forall x, rawLe M x x.
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (Formula.BProv_Ax_s_leTermAt_refl [] (tVar 0)) e) as h.
  change (rawLe M x x) in h. exact h.
Qed.

(** Semantic successor step for the prefix-agreement induction. *)
Lemma raw_termEvaluationTablesAgreeBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep
    leftTableCode leftTableStep leftSupportCode leftSupportStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep current,
  RawTermEvaluationTraversal M limit assignmentCode assignmentStep
    leftTableCode leftTableStep leftSupportCode leftSupportStep ->
  RawTermEvaluationTraversal M limit assignmentCode assignmentStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep ->
  rawLt M current limit ->
  RawTermEvaluationTablesAgreeBelow M current
    leftTableCode leftTableStep leftSupportCode leftSupportStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep ->
  RawTermEvaluationTablesAgreeBelow M (raw_succ M current)
    leftTableCode leftTableStep leftSupportCode leftSupportStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep
    leftTableCode leftTableStep leftSupportCode leftSupportStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep current
    hleftTraversal hrightTraversal hcurrentLimit hagree
    code hcodeSucc hleftSupport hrightSupport leftValue rightValue
    hleftLookup hrightLookup.
  destruct (raw_lt_succ_cases M hPA code current hcodeSucc)
    as [hcodeCurrent | hcodeEq].
  - exact (hagree code hcodeCurrent hleftSupport hrightSupport
      leftValue rightValue hleftLookup hrightLookup).
  - subst code.
    destruct hleftTraversal as [_ [_ hleftRows]].
    destruct hrightTraversal as [_ [_ hrightRows]].
    destruct (hleftRows current hcurrentLimit hleftSupport) as
      [leftCanonical [hleftCanonicalLookup hleftStep]].
    destruct (hrightRows current hcurrentLimit hrightSupport) as
      [rightCanonical [hrightCanonicalLookup hrightStep]].
    assert (hleftEq : leftValue = leftCanonical).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        leftTableCode leftTableStep current leftValue leftCanonical
        hleftLookup hleftCanonicalLookup).
    }
    assert (hrightEq : rightValue = rightCanonical).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        rightTableCode rightTableStep current rightValue rightCanonical
        hrightLookup hrightCanonicalLookup).
    }
    rewrite hleftEq, hrightEq.
    exact (raw_termEvaluationClosedStep_extensional M hPA
      assignmentCode assignmentStep
      leftTableCode leftTableStep leftSupportCode leftSupportStep
      rightTableCode rightTableStep rightSupportCode rightSupportStep
      current leftCanonical rightCanonical hagree hleftStep hrightStep).
Qed.

(** Genuine PA induction over an arbitrary carrier bound. *)
Theorem raw_termEvaluationTraversals_agree_below : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep
    leftTableCode leftTableStep leftSupportCode leftSupportStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep,
  RawTermEvaluationTraversal M limit assignmentCode assignmentStep
    leftTableCode leftTableStep leftSupportCode leftSupportStep ->
  RawTermEvaluationTraversal M limit assignmentCode assignmentStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep ->
  RawTermEvaluationTablesAgreeBelow M limit
    leftTableCode leftTableStep leftSupportCode leftSupportStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep
    leftTableCode leftTableStep leftSupportCode leftSupportStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep
    hleftTraversal hrightTraversal.
  set (parameterEnv := scons M limit
    (scons M leftTableCode (scons M leftTableStep
      (scons M leftSupportCode (scons M leftSupportStep
        (scons M rightTableCode (scons M rightTableStep
          (scons M rightSupportCode (scons M rightSupportStep
            (fun _ : nat => raw_zero M)))))))))).
  set (phi := termEvaluationTablesAgreeThroughTermAt
    (tVar 0) (tVar 1)
    (tVar 2) (tVar 3) (tVar 4) (tVar 5)
    (tVar 6) (tVar 7) (tVar 8) (tVar 9)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_termEvaluationTablesAgreeThroughTermAt_iff
        M (scons M (raw_zero M) parameterEnv)
        (tVar 0) (tVar 1)
        (tVar 2) (tVar 3) (tVar 4) (tVar 5)
        (tVar 6) (tVar 7) (tVar 8) (tVar 9))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _. intros code hcode.
      exfalso. exact (raw_not_lt_zero M hPA code hcode).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_termEvaluationTablesAgreeThroughTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1)
          (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9)) hcurrent) as hcurrentRaw.
      apply (proj2
        (raw_sat_termEvaluationTablesAgreeThroughTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 0) (tVar 1)
          (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9))).
      unfold parameterEnv in hcurrentRaw |- *.
      cbn [raw_term_eval scons] in hcurrentRaw |- *.
      intro hsuccLe.
      assert (hcurrentLimit : rawLt M current limit).
      { exact (raw_lt_of_succ_le_traversal M hPA current limit hsuccLe). }
      assert (hcurrentLe : rawLe M current limit).
      { exact (raw_lt_to_le M current limit hcurrentLimit). }
      exact (raw_termEvaluationTablesAgreeBelow_succ M hPA
        limit assignmentCode assignmentStep
        leftTableCode leftTableStep leftSupportCode leftSupportStep
        rightTableCode rightTableStep rightSupportCode rightSupportStep
        current hleftTraversal hrightTraversal hcurrentLimit
        (hcurrentRaw hcurrentLe)).
  }
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_termEvaluationTablesAgreeThroughTermAt_iff M
      (scons M limit parameterEnv)
      (tVar 0) (tVar 1)
      (tVar 2) (tVar 3) (tVar 4) (tVar 5)
      (tVar 6) (tVar 7) (tVar 8) (tVar 9))
    (hall limit)) as hlimit.
  unfold parameterEnv in hlimit.
  cbn [raw_term_eval scons] in hlimit.
  exact (hlimit (raw_le_refl_traversal M hPA limit)).
Qed.

Theorem raw_termEvaluationCertificate_value_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep leftValue rightValue,
  RawTermEvaluationCertificate M
    root leftValue assignmentCode assignmentStep ->
  RawTermEvaluationCertificate M
    root rightValue assignmentCode assignmentStep ->
  leftValue = rightValue.
Proof.
  intros M hPA root assignmentCode assignmentStep leftValue rightValue
    hleft hright.
  destruct hleft as [leftSupportCode hleft].
  destruct hleft as [leftSupportStep hleft].
  destruct hleft as [leftTableCode hleft].
  destruct hleft as [leftTableStep hleft].
  destruct hleft as [hleftTraversal [hleftSupport hleftLookup]].
  destruct hright as [rightSupportCode hright].
  destruct hright as [rightSupportStep hright].
  destruct hright as [rightTableCode hright].
  destruct hright as [rightTableStep hright].
  destruct hright as [hrightTraversal [hrightSupport hrightLookup]].
  pose proof (raw_termEvaluationTraversals_agree_below M hPA
    (raw_succ M root) assignmentCode assignmentStep
    leftTableCode leftTableStep leftSupportCode leftSupportStep
    rightTableCode rightTableStep rightSupportCode rightSupportStep
    hleftTraversal hrightTraversal) as hagree.
  assert (hrootLt : rawLt M root (raw_succ M root)).
  {
    apply raw_lt_succ_of_le. exact hPA.
    exact (raw_le_refl_traversal M hPA root).
  }
  exact (hagree root hrootLt hleftSupport hrightSupport
    leftValue rightValue hleftLookup hrightLookup).
Qed.

Corollary raw_sat_termEvaluationCertificateTermAt_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep leftValue rightValue e,
  raw_formula_sat M e
    (termEvaluationCertificateTermAt
      root leftValue assignmentCode assignmentStep) ->
  raw_formula_sat M e
    (termEvaluationCertificateTermAt
      root rightValue assignmentCode assignmentStep) ->
  raw_term_eval M e leftValue = raw_term_eval M e rightValue.
Proof.
  intros M hPA root assignmentCode assignmentStep
    leftValue rightValue e hleft hright.
  apply (raw_termEvaluationCertificate_value_functional M hPA
    (raw_term_eval M e root)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)).
  - apply (proj1 (raw_sat_termEvaluationCertificateTermAt_iff
      M e root leftValue assignmentCode assignmentStep)). exact hleft.
  - apply (proj1 (raw_sat_termEvaluationCertificateTermAt_iff
      M e root rightValue assignmentCode assignmentStep)). exact hright.
Qed.

(** The semantic functionality result is itself closed back into PA.  The
    five binders, from outside to inside, are root, assignment code,
    assignment step, left value, and right value. *)
Definition termEvaluationCertificateFunctionalFormula : formula :=
  pAll (pAll (pAll (pAll (pAll
    (pImp
      (pAnd
        (termEvaluationCertificateTermAt
          (tVar 4) (tVar 1) (tVar 3) (tVar 2))
        (termEvaluationCertificateTermAt
          (tVar 4) (tVar 0) (tVar 3) (tVar 2)))
      (pEq (tVar 1) (tVar 0))))))).

Lemma raw_sat_termEvaluationCertificateFunctionalFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e termEvaluationCertificateFunctionalFormula <->
  forall root assignmentCode assignmentStep leftValue rightValue : M,
    (RawTermEvaluationCertificate M
      root leftValue assignmentCode assignmentStep /\
    RawTermEvaluationCertificate M
      root rightValue assignmentCode assignmentStep) ->
    leftValue = rightValue.
Proof.
  intros M e.
  unfold termEvaluationCertificateFunctionalFormula.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_termEvaluationCertificateTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem termEvaluationCertificateFunctionalFormula_sentence :
  Formula.Sentence termEvaluationCertificateFunctionalFormula.
Proof.
  intros k hfree.
  unfold termEvaluationCertificateFunctionalFormula,
    termEvaluationCertificateTermAt,
    termEvaluationCertificateWithTablesTermAt,
    termEvaluationTraversalTermAt,
    termEvaluationClosedStepTermAt,
    termEvaluationClosedWitnessRowTermAt,
    termSuccEvaluationClosedRowTermAt,
    termAddEvaluationClosedRowTermAt,
    termMulEvaluationClosedRowTermAt,
    termCodeSupportedTermAt,
    codedAssignmentDefinedThroughTermAt,
    codedAssignmentLookupTermAt,
    pEx4, pAnd3, pAnd4 in hfree.
  cbn in hfree. lia.
Qed.

Theorem termEvaluationCertificateFunctionalFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e termEvaluationCertificateFunctionalFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_termEvaluationCertificateFunctionalFormula_iff M e)).
  intros root assignmentCode assignmentStep leftValue rightValue
    [hleft hright].
  exact (raw_termEvaluationCertificate_value_functional M hPA
    root assignmentCode assignmentStep leftValue rightValue hleft hright).
Qed.

Theorem PA_proves_termEvaluationCertificateFunctionalFormula :
  Formula.BProv Formula.Ax_s []
    termEvaluationCertificateFunctionalFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact termEvaluationCertificateFunctionalFormula_sentence.
  - exact termEvaluationCertificateFunctionalFormula_raw_valid.
Qed.

(** ------------------------------------------------------------------
    CRT append interface for future totality proofs. *)

Definition RawTermEvaluationTableAppendCapacity (M : RawPAModel)
    (target value supportStep tableStep : M) : Prop :=
  RawCommonMultipleThrough M target supportStep /\
  rawLt M (rawNumeralValue M 1)
    (rawBetaModulus M supportStep target) /\
  RawCommonMultipleThrough M target tableStep /\
  rawLt M value (rawBetaModulus M tableStep target).

Theorem raw_termEvaluationTables_append_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall target value supportCode supportStep tableCode tableStep,
  RawTermEvaluationTableAppendCapacity M target value supportStep tableStep ->
  exists newSupportCode newTableCode,
    RawBetaCodeExtension M supportCode supportStep target
      (rawNumeralValue M 1) newSupportCode /\
    RawBetaCodeExtension M tableCode tableStep target value newTableCode.
Proof.
  intros M hPA target value supportCode supportStep tableCode tableStep
    [hsupportCommon [hsupportBound [htableCommon hvalueBound]]].
  destruct (raw_betaCodeExtension_exists M hPA supportCode supportStep
    target (rawNumeralValue M 1) hsupportCommon hsupportBound)
    as [newSupportCode hsupport].
  destruct (raw_betaCodeExtension_exists M hPA tableCode tableStep
    target value htableCommon hvalueBound) as [newTableCode htable].
  exists newSupportCode, newTableCode. split; assumption.
Qed.

End PABoundedRawCodedTermEvaluationTraversal.
