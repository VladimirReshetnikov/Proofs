(**
  Beta-coded global traversal for rank-zero truth in arbitrary PA models.

  A support beta table records which formula codes belong to the dependency
  closure of the requested root.  A second beta table records their truth
  bits.  Recursive Boolean rows explicitly certify that both children are
  supported and have smaller codes, so PA induction over a possibly
  nonstandard bound can compare two traversals.

  Equality is deliberately different from the older local step interface:
  its two term values must come from [RawTermEvaluationCertificate]s for the
  same coded assignment.  Thus no unconstrained auxiliary beta table can
  decide atomic truth.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation PolynomialPairInjectivity
  RawCodedAssignment RawCodedRankZeroTruthStep
  RawCodedTermEvaluationStepFunctionality
  RawCodedRankZeroTruthStepFunctionality
  RawCodedTermEvaluationTraversal.

Import ListNotations.

Module PABoundedRawCodedRankZeroTruthTraversal.

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
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedRankZeroTruthStep.
Import PABoundedRawCodedTermEvaluationStepFunctionality.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedTermEvaluationTraversal.

(** ------------------------------------------------------------------
    Support flags and closed local rows. *)

Definition rawFormulaCodeSupported (M : RawPAModel)
    (supportCode supportStep code : M) : Prop :=
  RawCodedAssignmentLookup M supportCode supportStep code
    (rawNumeralValue M 1).

Arguments rawFormulaCodeSupported M supportCode supportStep code
  : clear implicits.

Definition formulaCodeSupportedTermAt
    (supportCode supportStep code : term) : formula :=
  codedAssignmentLookupTermAt supportCode supportStep code
    (Term.numeral 1).

Lemma raw_sat_formulaCodeSupportedTermAt_iff : forall (M : RawPAModel)
    e supportCode supportStep code,
  raw_formula_sat M e
    (formulaCodeSupportedTermAt supportCode supportStep code) <->
  rawFormulaCodeSupported M
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e code).
Proof.
  intros. unfold formulaCodeSupportedTermAt, rawFormulaCodeSupported.
  rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  rewrite raw_term_eval_numeral. reflexivity.
Qed.

(** Atomic equality uses two complete term-evaluation certificates. *)
Definition rankZeroEqCertifiedRowTermAt
    (code output assignmentCode assignmentStep
      left leftValue right rightValue : term) : formula :=
  pAnd4
    (formulaEqCodeTermAt code left right)
    (termEvaluationCertificateTermAt
      left leftValue assignmentCode assignmentStep)
    (termEvaluationCertificateTermAt
      right rightValue assignmentCode assignmentStep)
    (equalityTruthTermAt output leftValue rightValue).

Definition RawRankZeroEqCertifiedRow (M : RawPAModel)
    (code output assignmentCode assignmentStep
      left leftValue right rightValue : M) : Prop :=
  code = rawFormulaEqCode M left right /\
  RawTermEvaluationCertificate M
    left leftValue assignmentCode assignmentStep /\
  RawTermEvaluationCertificate M
    right rightValue assignmentCode assignmentStep /\
  RawEqualityTruth M output leftValue rightValue.

Arguments RawRankZeroEqCertifiedRow
  M code output assignmentCode assignmentStep
    left leftValue right rightValue : clear implicits.

Lemma raw_sat_rankZeroEqCertifiedRowTermAt_iff : forall
    (M : RawPAModel) e code output assignmentCode assignmentStep
      left leftValue right rightValue,
  raw_formula_sat M e
    (rankZeroEqCertifiedRowTermAt code output assignmentCode assignmentStep
      left leftValue right rightValue) <->
  RawRankZeroEqCertifiedRow M
    (raw_term_eval M e code) (raw_term_eval M e output)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)
    (raw_term_eval M e left) (raw_term_eval M e leftValue)
    (raw_term_eval M e right) (raw_term_eval M e rightValue).
Proof.
  intros. unfold rankZeroEqCertifiedRowTermAt,
    RawRankZeroEqCertifiedRow, pAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaEqCodeTermAt_iff,
    !raw_sat_termEvaluationCertificateTermAt_iff,
    raw_sat_equalityTruthTermAt_iff.
  reflexivity.
Qed.

Definition rankZeroImpClosedRowTermAt
    (code output truthCode truthStep supportCode supportStep
      left leftTruth right rightTruth : term) : formula :=
  pAnd
    (formulaImpTruthRowTermAt code output truthCode truthStep
      left leftTruth right rightTruth)
    (pAnd4
      (formulaCodeSupportedTermAt supportCode supportStep left)
      (formulaCodeSupportedTermAt supportCode supportStep right)
      (Formula.ltTermAt left code)
      (Formula.ltTermAt right code)).

Definition rankZeroAndClosedRowTermAt
    (code output truthCode truthStep supportCode supportStep
      left leftTruth right rightTruth : term) : formula :=
  pAnd
    (formulaAndTruthRowTermAt code output truthCode truthStep
      left leftTruth right rightTruth)
    (pAnd4
      (formulaCodeSupportedTermAt supportCode supportStep left)
      (formulaCodeSupportedTermAt supportCode supportStep right)
      (Formula.ltTermAt left code)
      (Formula.ltTermAt right code)).

Definition rankZeroOrClosedRowTermAt
    (code output truthCode truthStep supportCode supportStep
      left leftTruth right rightTruth : term) : formula :=
  pAnd
    (formulaOrTruthRowTermAt code output truthCode truthStep
      left leftTruth right rightTruth)
    (pAnd4
      (formulaCodeSupportedTermAt supportCode supportStep left)
      (formulaCodeSupportedTermAt supportCode supportStep right)
      (Formula.ltTermAt left code)
      (Formula.ltTermAt right code)).

Definition rankZeroTruthClosedWitnessRowTermAt
    (code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep left leftValue right rightValue : term)
    : formula :=
  pOr
    (rankZeroEqCertifiedRowTermAt
      code output assignmentCode assignmentStep
      left leftValue right rightValue)
    (pOr
      (formulaBotTruthRowTermAt code output)
      (pOr
        (rankZeroImpClosedRowTermAt
          code output truthCode truthStep supportCode supportStep
          left leftValue right rightValue)
        (pOr
          (rankZeroAndClosedRowTermAt
            code output truthCode truthStep supportCode supportStep
            left leftValue right rightValue)
          (rankZeroOrClosedRowTermAt
            code output truthCode truthStep supportCode supportStep
            left leftValue right rightValue)))).

Definition RawRankZeroTruthClosedWitnessRow (M : RawPAModel)
    (code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep left leftValue right rightValue : M) : Prop :=
  RawRankZeroEqCertifiedRow M
      code output assignmentCode assignmentStep
      left leftValue right rightValue \/
  RawFormulaBotTruthRow M code output \/
  (RawFormulaImpTruthRow M code output truthCode truthStep
      left leftValue right rightValue /\
    rawFormulaCodeSupported M supportCode supportStep left /\
    rawFormulaCodeSupported M supportCode supportStep right /\
    rawLt M left code /\ rawLt M right code) \/
  (RawFormulaAndTruthRow M code output truthCode truthStep
      left leftValue right rightValue /\
    rawFormulaCodeSupported M supportCode supportStep left /\
    rawFormulaCodeSupported M supportCode supportStep right /\
    rawLt M left code /\ rawLt M right code) \/
  (RawFormulaOrTruthRow M code output truthCode truthStep
      left leftValue right rightValue /\
    rawFormulaCodeSupported M supportCode supportStep left /\
    rawFormulaCodeSupported M supportCode supportStep right /\
    rawLt M left code /\ rawLt M right code).

Arguments RawRankZeroTruthClosedWitnessRow
  M code output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep left leftValue right rightValue : clear implicits.

Lemma raw_sat_rankZeroTruthClosedWitnessRowTermAt_iff : forall
    (M : RawPAModel) e code output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep
      left leftValue right rightValue,
  raw_formula_sat M e
    (rankZeroTruthClosedWitnessRowTermAt
      code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep left leftValue right rightValue) <->
  RawRankZeroTruthClosedWitnessRow M
    (raw_term_eval M e code) (raw_term_eval M e output)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)
    (raw_term_eval M e truthCode) (raw_term_eval M e truthStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e left) (raw_term_eval M e leftValue)
    (raw_term_eval M e right) (raw_term_eval M e rightValue).
Proof.
  intros. unfold rankZeroTruthClosedWitnessRowTermAt,
    rankZeroImpClosedRowTermAt,
    rankZeroAndClosedRowTermAt,
    rankZeroOrClosedRowTermAt,
    RawRankZeroTruthClosedWitnessRow, pAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_rankZeroEqCertifiedRowTermAt_iff,
    raw_sat_formulaBotTruthRowTermAt_iff,
    raw_sat_formulaImpTruthRowTermAt_iff,
    raw_sat_formulaAndTruthRowTermAt_iff,
    raw_sat_formulaOrTruthRowTermAt_iff,
    !raw_sat_formulaCodeSupportedTermAt_iff,
    !raw_sat_ltTermAt_iff.
  tauto.
Qed.

Definition rankZeroTruthClosedStepTermAt
    (code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep : term) : formula :=
  pEx4
    (rankZeroTruthClosedWitnessRowTermAt
      (liftTerm 4 code) (liftTerm 4 output)
      (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
      (liftTerm 4 truthCode) (liftTerm 4 truthStep)
      (liftTerm 4 supportCode) (liftTerm 4 supportStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)).

Definition RawRankZeroTruthClosedStep (M : RawPAModel)
    (code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep : M) : Prop :=
  exists left leftValue right rightValue : M,
    RawRankZeroTruthClosedWitnessRow M
      code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep left leftValue right rightValue.

Arguments RawRankZeroTruthClosedStep
  M code output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep : clear implicits.

Lemma raw_sat_rankZeroTruthClosedStepTermAt_iff : forall
    (M : RawPAModel) e code output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep,
  raw_formula_sat M e
    (rankZeroTruthClosedStepTermAt
      code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep) <->
  RawRankZeroTruthClosedStep M
    (raw_term_eval M e code) (raw_term_eval M e output)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)
    (raw_term_eval M e truthCode) (raw_term_eval M e truthStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e code output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep.
  unfold rankZeroTruthClosedStepTermAt,
    RawRankZeroTruthClosedStep, pEx4.
  cbn [raw_formula_sat]. split.
  - intros [left [leftValue [right [rightValue hrow]]]].
    exists left, leftValue, right, rightValue.
    apply (proj1 (raw_sat_rankZeroTruthClosedWitnessRowTermAt_iff M
      (scons M rightValue
        (scons M right (scons M leftValue (scons M left e))))
      (liftTerm 4 code) (liftTerm 4 output)
      (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
      (liftTerm 4 truthCode) (liftTerm 4 truthStep)
      (liftTerm 4 supportCode) (liftTerm 4 supportStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))) in hrow.
    rewrite !raw_term_eval_liftTerm_four_truth in hrow.
    cbn [raw_term_eval scons] in hrow. exact hrow.
  - intros [left [leftValue [right [rightValue hrow]]]].
    exists left, leftValue, right, rightValue.
    apply (proj2 (raw_sat_rankZeroTruthClosedWitnessRowTermAt_iff M
      (scons M rightValue
        (scons M right (scons M leftValue (scons M left e))))
      (liftTerm 4 code) (liftTerm 4 output)
      (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
      (liftTerm 4 truthCode) (liftTerm 4 truthStep)
      (liftTerm 4 supportCode) (liftTerm 4 supportStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))).
    rewrite !raw_term_eval_liftTerm_four_truth.
    cbn [raw_term_eval scons]. exact hrow.
Qed.

(** ------------------------------------------------------------------
    Global support/truth tables and their root certificate. *)

Definition RawRankZeroTruthTraversal (M : RawPAModel)
    (bound assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M supportCode supportStep bound /\
  RawCodedAssignmentDefinedThrough M truthCode truthStep bound /\
  forall code,
    rawLt M code bound ->
    rawFormulaCodeSupported M supportCode supportStep code ->
    exists output,
      RawCodedAssignmentLookup M truthCode truthStep code output /\
      RawRankZeroTruthClosedStep M
        code output assignmentCode assignmentStep truthCode truthStep
        supportCode supportStep.

Arguments RawRankZeroTruthTraversal
  M bound assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep : clear implicits.

Definition rankZeroTruthTraversalTermAt
    (bound assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep : term) : formula :=
  pAnd3
    (codedAssignmentDefinedThroughTermAt supportCode supportStep bound)
    (codedAssignmentDefinedThroughTermAt truthCode truthStep bound)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
        (pImp
          (formulaCodeSupportedTermAt
            (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
          (pEx
            (pAnd
              (codedAssignmentLookupTermAt
                (liftTerm 2 truthCode) (liftTerm 2 truthStep)
                (tVar 1) (tVar 0))
              (rankZeroTruthClosedStepTermAt
                (tVar 1) (tVar 0)
                (liftTerm 2 assignmentCode) (liftTerm 2 assignmentStep)
                (liftTerm 2 truthCode) (liftTerm 2 truthStep)
                (liftTerm 2 supportCode) (liftTerm 2 supportStep))))))).

Lemma raw_sat_rankZeroTruthTraversalTermAt_iff : forall
    (M : RawPAModel) e bound assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep,
  raw_formula_sat M e
    (rankZeroTruthTraversalTermAt
      bound assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep) <->
  RawRankZeroTruthTraversal M
    (raw_term_eval M e bound)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)
    (raw_term_eval M e truthCode) (raw_term_eval M e truthStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e bound assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep.
  unfold rankZeroTruthTraversalTermAt,
    RawRankZeroTruthTraversal, pAnd3.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  split.
  - intros [hsupport [htruth hall]].
    split; [exact hsupport |]. split; [exact htruth |].
    intros code hcode hsupported.
    assert (hltSat : raw_formula_sat M (scons M code e)
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hcode.
    }
    assert (hsupportedSat : raw_formula_sat M (scons M code e)
        (formulaCodeSupportedTermAt
          (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))).
    {
      apply (proj2 (raw_sat_formulaCodeSupportedTermAt_iff M _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hsupported.
    }
    destruct (hall code hltSat hsupportedSat) as
      [output [hlookup hstep]].
    exists output. split.
    + apply (proj1 (raw_sat_codedAssignmentLookupTermAt_iff
        M _ _ _ _ _)) in hlookup.
      rewrite !raw_term_eval_liftTerm_two_traversal in hlookup.
      cbn [raw_term_eval scons] in hlookup. exact hlookup.
    + apply (proj1 (raw_sat_rankZeroTruthClosedStepTermAt_iff
        M _ _ _ _ _ _ _ _ _)) in hstep.
      rewrite !raw_term_eval_liftTerm_two_traversal in hstep.
      cbn [raw_term_eval scons] in hstep. exact hstep.
  - intros [hsupport [htruth hall]].
    split; [exact hsupport |]. split; [exact htruth |].
    intros code hltSat hsupportedSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat) as hcode.
    rewrite raw_term_eval_liftTerm_one_traversal in hcode.
    cbn [raw_term_eval scons] in hcode.
    pose proof (proj1 (raw_sat_formulaCodeSupportedTermAt_iff M _ _ _ _)
      hsupportedSat) as hsupported.
    rewrite !raw_term_eval_liftTerm_one_traversal in hsupported.
    cbn [raw_term_eval scons] in hsupported.
    destruct (hall code hcode hsupported) as [output [hlookup hstep]].
    exists output. split.
    + apply (proj2 (raw_sat_codedAssignmentLookupTermAt_iff
        M _ _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_two_traversal.
      cbn [raw_term_eval scons]. exact hlookup.
    + apply (proj2 (raw_sat_rankZeroTruthClosedStepTermAt_iff
        M _ _ _ _ _ _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_two_traversal.
      cbn [raw_term_eval scons]. exact hstep.
Qed.

Definition RawRankZeroTruthCertificateWithTables (M : RawPAModel)
    (root output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep : M) : Prop :=
  RawRankZeroTruthTraversal M (raw_succ M root)
    assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep /\
  rawFormulaCodeSupported M supportCode supportStep root /\
  RawCodedAssignmentLookup M truthCode truthStep root output /\
  RawTruthBit M output.

Definition rankZeroTruthCertificateWithTablesTermAt
    (root output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep : term) : formula :=
  pAnd4
    (rankZeroTruthTraversalTermAt (tSucc root)
      assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep)
    (formulaCodeSupportedTermAt supportCode supportStep root)
    (codedAssignmentLookupTermAt truthCode truthStep root output)
    (truthBitTermAt output).

Lemma raw_sat_rankZeroTruthCertificateWithTablesTermAt_iff : forall
    (M : RawPAModel) e root output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep,
  raw_formula_sat M e
    (rankZeroTruthCertificateWithTablesTermAt
      root output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep) <->
  RawRankZeroTruthCertificateWithTables M
    (raw_term_eval M e root) (raw_term_eval M e output)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)
    (raw_term_eval M e truthCode) (raw_term_eval M e truthStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros. unfold rankZeroTruthCertificateWithTablesTermAt,
    RawRankZeroTruthCertificateWithTables, pAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_rankZeroTruthTraversalTermAt_iff,
    raw_sat_formulaCodeSupportedTermAt_iff,
    raw_sat_codedAssignmentLookupTermAt_iff,
    raw_sat_truthBitTermAt_iff.
  reflexivity.
Qed.

Definition rankZeroTruthCertificateTermAt
    (root output assignmentCode assignmentStep : term) : formula :=
  pEx4
    (rankZeroTruthCertificateWithTablesTermAt
      (liftTerm 4 root) (liftTerm 4 output)
      (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
      (tVar 1) (tVar 0) (tVar 3) (tVar 2)).

Definition RawRankZeroTruthCertificate (M : RawPAModel)
    (root output assignmentCode assignmentStep : M) : Prop :=
  exists supportCode supportStep truthCode truthStep : M,
    RawRankZeroTruthCertificateWithTables M
      root output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep.

Arguments RawRankZeroTruthCertificate
  M root output assignmentCode assignmentStep : clear implicits.

Lemma raw_sat_rankZeroTruthCertificateTermAt_iff : forall
    (M : RawPAModel) e root output assignmentCode assignmentStep,
  raw_formula_sat M e
    (rankZeroTruthCertificateTermAt
      root output assignmentCode assignmentStep) <->
  RawRankZeroTruthCertificate M
    (raw_term_eval M e root) (raw_term_eval M e output)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intros M e root output assignmentCode assignmentStep.
  unfold rankZeroTruthCertificateTermAt,
    RawRankZeroTruthCertificate, pEx4.
  cbn [raw_formula_sat]. split.
  - intros [supportCode [supportStep [truthCode [truthStep hcert]]]].
    exists supportCode, supportStep, truthCode, truthStep.
    apply (proj1
      (raw_sat_rankZeroTruthCertificateWithTablesTermAt_iff M
        (scons M truthStep
          (scons M truthCode
            (scons M supportStep (scons M supportCode e))))
        (liftTerm 4 root) (liftTerm 4 output)
        (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
        (tVar 1) (tVar 0) (tVar 3) (tVar 2))) in hcert.
    rewrite !raw_term_eval_liftTerm_four_truth in hcert.
    cbn [raw_term_eval scons] in hcert. exact hcert.
  - intros [supportCode [supportStep [truthCode [truthStep hcert]]]].
    exists supportCode, supportStep, truthCode, truthStep.
    apply (proj2
      (raw_sat_rankZeroTruthCertificateWithTablesTermAt_iff M
        (scons M truthStep
          (scons M truthCode
            (scons M supportStep (scons M supportCode e))))
        (liftTerm 4 root) (liftTerm 4 output)
        (liftTerm 4 assignmentCode) (liftTerm 4 assignmentStep)
        (tVar 1) (tVar 0) (tVar 3) (tVar 2))).
    rewrite !raw_term_eval_liftTerm_four_truth.
    cbn [raw_term_eval scons]. exact hcert.
Qed.

(** ------------------------------------------------------------------
    PA-definable prefix agreement of two truth traversals. *)

Definition RawRankZeroTruthTablesAgreeBelow (M : RawPAModel)
    (bound leftTruthCode leftTruthStep leftSupportCode leftSupportStep
      rightTruthCode rightTruthStep rightSupportCode rightSupportStep : M)
    : Prop :=
  forall code,
    rawLt M code bound ->
    rawFormulaCodeSupported M leftSupportCode leftSupportStep code ->
    rawFormulaCodeSupported M rightSupportCode rightSupportStep code ->
    forall leftOutput rightOutput,
      RawCodedAssignmentLookup M
        leftTruthCode leftTruthStep code leftOutput ->
      RawCodedAssignmentLookup M
        rightTruthCode rightTruthStep code rightOutput ->
      leftOutput = rightOutput.

Arguments RawRankZeroTruthTablesAgreeBelow
  M bound leftTruthCode leftTruthStep leftSupportCode leftSupportStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep
  : clear implicits.

Definition rankZeroTruthTablesAgreeBelowTermAt
    (bound leftTruthCode leftTruthStep leftSupportCode leftSupportStep
      rightTruthCode rightTruthStep rightSupportCode rightSupportStep : term)
    : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (pImp
        (formulaCodeSupportedTermAt
          (liftTerm 1 leftSupportCode) (liftTerm 1 leftSupportStep) (tVar 0))
        (pImp
          (formulaCodeSupportedTermAt
            (liftTerm 1 rightSupportCode) (liftTerm 1 rightSupportStep)
            (tVar 0))
          (pAll
            (pImp
              (codedAssignmentLookupTermAt
                (liftTerm 2 leftTruthCode) (liftTerm 2 leftTruthStep)
                (tVar 1) (tVar 0))
              (pAll
                (pImp
                  (codedAssignmentLookupTermAt
                    (liftTerm 3 rightTruthCode)
                    (liftTerm 3 rightTruthStep) (tVar 2) (tVar 0))
                  (pEq (tVar 1) (tVar 0))))))))).

Lemma raw_sat_rankZeroTruthTablesAgreeBelowTermAt_iff : forall
    (M : RawPAModel) e bound
      leftTruthCode leftTruthStep leftSupportCode leftSupportStep
      rightTruthCode rightTruthStep rightSupportCode rightSupportStep,
  raw_formula_sat M e
    (rankZeroTruthTablesAgreeBelowTermAt bound
      leftTruthCode leftTruthStep leftSupportCode leftSupportStep
      rightTruthCode rightTruthStep rightSupportCode rightSupportStep) <->
  RawRankZeroTruthTablesAgreeBelow M (raw_term_eval M e bound)
    (raw_term_eval M e leftTruthCode)
    (raw_term_eval M e leftTruthStep)
    (raw_term_eval M e leftSupportCode)
    (raw_term_eval M e leftSupportStep)
    (raw_term_eval M e rightTruthCode)
    (raw_term_eval M e rightTruthStep)
    (raw_term_eval M e rightSupportCode)
    (raw_term_eval M e rightSupportStep).
Proof.
  intros M e bound leftTruthCode leftTruthStep
    leftSupportCode leftSupportStep rightTruthCode rightTruthStep
    rightSupportCode rightSupportStep.
  unfold rankZeroTruthTablesAgreeBelowTermAt,
    RawRankZeroTruthTablesAgreeBelow.
  cbn [raw_formula_sat]. split.
  - intros hall code hcode hleftSupport hrightSupport
      leftOutput rightOutput hleft hright.
    assert (hltSat : raw_formula_sat M (scons M code e)
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hcode.
    }
    assert (hleftSupportSat : raw_formula_sat M (scons M code e)
        (formulaCodeSupportedTermAt
          (liftTerm 1 leftSupportCode) (liftTerm 1 leftSupportStep)
          (tVar 0))).
    {
      apply (proj2 (raw_sat_formulaCodeSupportedTermAt_iff M _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hleftSupport.
    }
    assert (hrightSupportSat : raw_formula_sat M (scons M code e)
        (formulaCodeSupportedTermAt
          (liftTerm 1 rightSupportCode) (liftTerm 1 rightSupportStep)
          (tVar 0))).
    {
      apply (proj2 (raw_sat_formulaCodeSupportedTermAt_iff M _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hrightSupport.
    }
    pose proof (hall code hltSat hleftSupportSat hrightSupportSat
      leftOutput) as hleftImp.
    assert (hleftSat : raw_formula_sat M
        (scons M leftOutput (scons M code e))
        (codedAssignmentLookupTermAt
          (liftTerm 2 leftTruthCode) (liftTerm 2 leftTruthStep)
          (tVar 1) (tVar 0))).
    {
      apply (proj2 (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_two_traversal.
      cbn [raw_term_eval scons]. exact hleft.
    }
    pose proof (hleftImp hleftSat rightOutput) as hrightImp.
    assert (hrightSat : raw_formula_sat M
        (scons M rightOutput (scons M leftOutput (scons M code e)))
        (codedAssignmentLookupTermAt
          (liftTerm 3 rightTruthCode) (liftTerm 3 rightTruthStep)
          (tVar 2) (tVar 0))).
    {
      apply (proj2 (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_three_traversal.
      cbn [raw_term_eval scons]. exact hright.
    }
    exact (hrightImp hrightSat).
  - intros hagree code hltSat hleftSupportSat hrightSupportSat
      leftOutput hleftSat rightOutput hrightSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat) as hcode.
    rewrite raw_term_eval_liftTerm_one_traversal in hcode.
    cbn [raw_term_eval scons] in hcode.
    pose proof (proj1 (raw_sat_formulaCodeSupportedTermAt_iff M _ _ _ _)
      hleftSupportSat) as hleftSupport.
    rewrite !raw_term_eval_liftTerm_one_traversal in hleftSupport.
    cbn [raw_term_eval scons] in hleftSupport.
    pose proof (proj1 (raw_sat_formulaCodeSupportedTermAt_iff M _ _ _ _)
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
      leftOutput rightOutput hleft hright).
Qed.

(** ------------------------------------------------------------------
    Cross-table local extensionality. *)

Definition RawRankZeroTruthClosedStepExtensionality
    (M : RawPAModel) : Prop :=
  forall assignmentCode assignmentStep
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep
    code leftOutput rightOutput,
  (forall child,
    rawLt M child code ->
    rawFormulaCodeSupported M leftSupportCode leftSupportStep child ->
    rawFormulaCodeSupported M rightSupportCode rightSupportStep child ->
    forall leftChildOutput rightChildOutput,
      RawCodedAssignmentLookup M
        leftTruthCode leftTruthStep child leftChildOutput ->
      RawCodedAssignmentLookup M
        rightTruthCode rightTruthStep child rightChildOutput ->
      leftChildOutput = rightChildOutput) ->
  RawRankZeroTruthClosedStep M
    code leftOutput assignmentCode assignmentStep
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep ->
  RawRankZeroTruthClosedStep M
    code rightOutput assignmentCode assignmentStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep ->
  leftOutput = rightOutput.

Theorem raw_rankZeroTruthClosedStep_extensional : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawRankZeroTruthClosedStepExtensionality M.
Proof.
  intros M hPA assignmentCode assignmentStep
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep
    code leftOutput rightOutput hchildren
    [l1 [lv1 [r1 [rv1 hleft]]]]
    [l2 [lv2 [r2 [rv2 hright]]]].
  destruct hleft as [heq1 | [hbot1 | [himp1 | [hand1 | hor1]]]];
  destruct hright as [heq2 | [hbot2 | [himp2 | [hand2 | hor2]]]].
  - destruct heq1 as [hc1 [htermL1 [htermR1 htruth1]]].
    destruct heq2 as [hc2 [htermL2 [htermR2 htruth2]]].
    assert (hcodes : rawFormulaEqCode M l1 r1 =
        rawFormulaEqCode M l2 r2).
    { exact (eq_trans (eq_sym hc1) hc2). }
    unfold rawFormulaEqCode in hcodes.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcodes) as [_ [hl hr]].
    subst l2. subst r2.
    assert (hlv : lv1 = lv2).
    {
      exact (raw_termEvaluationCertificate_value_functional M hPA
        l1 assignmentCode assignmentStep lv1 lv2 htermL1 htermL2).
    }
    assert (hrv : rv1 = rv2).
    {
      exact (raw_termEvaluationCertificate_value_functional M hPA
        r1 assignmentCode assignmentStep rv1 rv2 htermR1 htermR2).
    }
    subst lv2. subst rv2.
    exact (raw_equalityTruth_functional M lv1 rv1
      leftOutput rightOutput htruth1 htruth2).
  - destruct heq1 as [hc1 _]. destruct hbot2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 0) l1 r1).
    exact (eq_trans (eq_sym hc2) hc1).
  - destruct heq1 as [hc1 _]. destruct himp2 as [himp2 _].
    destruct himp2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      0 2 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct heq1 as [hc1 _]. destruct hand2 as [hand2 _].
    destruct hand2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      0 3 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct heq1 as [hc1 _]. destruct hor2 as [hor2 _].
    destruct hor2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      0 4 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hbot1 as [hc1 _]. destruct heq2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 0) l2 r2).
    exact (eq_trans (eq_sym hc1) hc2).
  - destruct hbot1 as [_ hv1]. destruct hbot2 as [_ hv2].
    now rewrite hv1, hv2.
  - destruct hbot1 as [hc1 _]. destruct himp2 as [himp2 _].
    destruct himp2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 2) l2 r2).
    exact (eq_trans (eq_sym hc1) hc2).
  - destruct hbot1 as [hc1 _]. destruct hand2 as [hand2 _].
    destruct hand2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 3) l2 r2).
    exact (eq_trans (eq_sym hc1) hc2).
  - destruct hbot1 as [hc1 _]. destruct hor2 as [hor2 _].
    destruct hor2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 4) l2 r2).
    exact (eq_trans (eq_sym hc1) hc2).
  - destruct himp1 as [himp1 _]. destruct himp1 as [hc1 _].
    destruct heq2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      2 0 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct himp1 as [himp1 _]. destruct himp1 as [hc1 _].
    destruct hbot2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 2) l1 r1).
    exact (eq_trans (eq_sym hc2) hc1).
  - destruct himp1 as
      [himp1 [hleftSupport1 [hrightSupport1 [hleftLt1 hrightLt1]]]].
    destruct himp2 as
      [himp2 [hleftSupport2 [hrightSupport2 [hleftLt2 hrightLt2]]]].
    destruct himp1 as
      [hc1 [hleftLookup1 [hrightLookup1 htruth1]]].
    destruct himp2 as
      [hc2 [hleftLookup2 [hrightLookup2 htruth2]]].
    assert (hcodes : rawFormulaImpCode M l1 r1 =
        rawFormulaImpCode M l2 r2).
    { exact (eq_trans (eq_sym hc1) hc2). }
    unfold rawFormulaImpCode in hcodes.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcodes) as [_ [hl hr]].
    subst l2. subst r2.
    assert (hlv : lv1 = lv2).
    {
      exact (hchildren l1 hleftLt1 hleftSupport1 hleftSupport2
        lv1 lv2 hleftLookup1 hleftLookup2).
    }
    assert (hrv : rv1 = rv2).
    {
      exact (hchildren r1 hrightLt1 hrightSupport1 hrightSupport2
        rv1 rv2 hrightLookup1 hrightLookup2).
    }
    subst lv2. subst rv2.
    exact (raw_impTruth_functional M hPA lv1 rv1
      leftOutput rightOutput htruth1 htruth2).
  - destruct himp1 as [himp1 _]. destruct himp1 as [hc1 _].
    destruct hand2 as [hand2 _]. destruct hand2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      2 3 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct himp1 as [himp1 _]. destruct himp1 as [hc1 _].
    destruct hor2 as [hor2 _]. destruct hor2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      2 4 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hand1 as [hand1 _]. destruct hand1 as [hc1 _].
    destruct heq2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      3 0 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hand1 as [hand1 _]. destruct hand1 as [hc1 _].
    destruct hbot2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 3) l1 r1).
    exact (eq_trans (eq_sym hc2) hc1).
  - destruct hand1 as [hand1 _]. destruct hand1 as [hc1 _].
    destruct himp2 as [himp2 _]. destruct himp2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      3 2 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hand1 as
      [hand1 [hleftSupport1 [hrightSupport1 [hleftLt1 hrightLt1]]]].
    destruct hand2 as
      [hand2 [hleftSupport2 [hrightSupport2 [hleftLt2 hrightLt2]]]].
    destruct hand1 as
      [hc1 [hleftLookup1 [hrightLookup1 htruth1]]].
    destruct hand2 as
      [hc2 [hleftLookup2 [hrightLookup2 htruth2]]].
    assert (hcodes : rawFormulaAndCode M l1 r1 =
        rawFormulaAndCode M l2 r2).
    { exact (eq_trans (eq_sym hc1) hc2). }
    unfold rawFormulaAndCode in hcodes.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcodes) as [_ [hl hr]].
    subst l2. subst r2.
    assert (hlv : lv1 = lv2).
    {
      exact (hchildren l1 hleftLt1 hleftSupport1 hleftSupport2
        lv1 lv2 hleftLookup1 hleftLookup2).
    }
    assert (hrv : rv1 = rv2).
    {
      exact (hchildren r1 hrightLt1 hrightSupport1 hrightSupport2
        rv1 rv2 hrightLookup1 hrightLookup2).
    }
    subst lv2. subst rv2.
    exact (raw_andTruth_functional M hPA lv1 rv1
      leftOutput rightOutput htruth1 htruth2).
  - destruct hand1 as [hand1 _]. destruct hand1 as [hc1 _].
    destruct hor2 as [hor2 _]. destruct hor2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      3 4 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hor1 as [hor1 _]. destruct hor1 as [hc1 _].
    destruct heq2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      4 0 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hor1 as [hor1 _]. destruct hor1 as [hc1 _].
    destruct hbot2 as [hc2 _].
    exfalso. apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 4) l1 r1).
    exact (eq_trans (eq_sym hc2) hc1).
  - destruct hor1 as [hor1 _]. destruct hor1 as [hc1 _].
    destruct himp2 as [himp2 _]. destruct himp2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      4 2 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hor1 as [hor1 _]. destruct hor1 as [hc1 _].
    destruct hand2 as [hand2 _]. destruct hand2 as [hc2 _].
    exfalso. pose proof (raw_codeList3_numeral_tags_eq M hPA
      4 3 l1 r1 l2 r2 (eq_trans (eq_sym hc1) hc2)). discriminate.
  - destruct hor1 as
      [hor1 [hleftSupport1 [hrightSupport1 [hleftLt1 hrightLt1]]]].
    destruct hor2 as
      [hor2 [hleftSupport2 [hrightSupport2 [hleftLt2 hrightLt2]]]].
    destruct hor1 as
      [hc1 [hleftLookup1 [hrightLookup1 htruth1]]].
    destruct hor2 as
      [hc2 [hleftLookup2 [hrightLookup2 htruth2]]].
    assert (hcodes : rawFormulaOrCode M l1 r1 =
        rawFormulaOrCode M l2 r2).
    { exact (eq_trans (eq_sym hc1) hc2). }
    unfold rawFormulaOrCode in hcodes.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcodes) as [_ [hl hr]].
    subst l2. subst r2.
    assert (hlv : lv1 = lv2).
    {
      exact (hchildren l1 hleftLt1 hleftSupport1 hleftSupport2
        lv1 lv2 hleftLookup1 hleftLookup2).
    }
    assert (hrv : rv1 = rv2).
    {
      exact (hchildren r1 hrightLt1 hrightSupport1 hrightSupport2
        rv1 rv2 hrightLookup1 hrightLookup2).
    }
    subst lv2. subst rv2.
    exact (raw_orTruth_functional M hPA lv1 rv1
      leftOutput rightOutput htruth1 htruth2).
Qed.

(** ------------------------------------------------------------------
    Genuine PA induction over an arbitrary carrier bound. *)

Definition rankZeroTruthTablesAgreeThroughTermAt
    (current limit
      leftTruthCode leftTruthStep leftSupportCode leftSupportStep
      rightTruthCode rightTruthStep rightSupportCode rightSupportStep : term)
    : formula :=
  pImp (Formula.leTermAt current limit)
    (rankZeroTruthTablesAgreeBelowTermAt current
      leftTruthCode leftTruthStep leftSupportCode leftSupportStep
      rightTruthCode rightTruthStep rightSupportCode rightSupportStep).

Definition RawRankZeroTruthTablesAgreeThrough (M : RawPAModel)
    (current limit
      leftTruthCode leftTruthStep leftSupportCode leftSupportStep
      rightTruthCode rightTruthStep rightSupportCode rightSupportStep : M)
    : Prop :=
  rawLe M current limit ->
  RawRankZeroTruthTablesAgreeBelow M current
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep.

Lemma raw_sat_rankZeroTruthTablesAgreeThroughTermAt_iff : forall
    (M : RawPAModel) e current limit
      leftTruthCode leftTruthStep leftSupportCode leftSupportStep
      rightTruthCode rightTruthStep rightSupportCode rightSupportStep,
  raw_formula_sat M e
    (rankZeroTruthTablesAgreeThroughTermAt current limit
      leftTruthCode leftTruthStep leftSupportCode leftSupportStep
      rightTruthCode rightTruthStep rightSupportCode rightSupportStep) <->
  RawRankZeroTruthTablesAgreeThrough M
    (raw_term_eval M e current) (raw_term_eval M e limit)
    (raw_term_eval M e leftTruthCode)
    (raw_term_eval M e leftTruthStep)
    (raw_term_eval M e leftSupportCode)
    (raw_term_eval M e leftSupportStep)
    (raw_term_eval M e rightTruthCode)
    (raw_term_eval M e rightTruthStep)
    (raw_term_eval M e rightSupportCode)
    (raw_term_eval M e rightSupportStep).
Proof.
  intros. unfold rankZeroTruthTablesAgreeThroughTermAt,
    RawRankZeroTruthTablesAgreeThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_traversal,
    raw_sat_rankZeroTruthTablesAgreeBelowTermAt_iff.
  tauto.
Qed.

Lemma raw_rankZeroTruthTablesAgreeBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep current,
  RawRankZeroTruthTraversal M limit assignmentCode assignmentStep
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep ->
  RawRankZeroTruthTraversal M limit assignmentCode assignmentStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep ->
  rawLt M current limit ->
  RawRankZeroTruthTablesAgreeBelow M current
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep ->
  RawRankZeroTruthTablesAgreeBelow M (raw_succ M current)
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep current
    hleftTraversal hrightTraversal hcurrentLimit hagree
    code hcodeSucc hleftSupport hrightSupport leftOutput rightOutput
    hleftLookup hrightLookup.
  destruct (raw_lt_succ_cases M hPA code current hcodeSucc)
    as [hcodeCurrent | hcodeEq].
  - exact (hagree code hcodeCurrent hleftSupport hrightSupport
      leftOutput rightOutput hleftLookup hrightLookup).
  - subst code.
    destruct hleftTraversal as [_ [_ hleftRows]].
    destruct hrightTraversal as [_ [_ hrightRows]].
    destruct (hleftRows current hcurrentLimit hleftSupport) as
      [leftCanonical [hleftCanonicalLookup hleftStep]].
    destruct (hrightRows current hcurrentLimit hrightSupport) as
      [rightCanonical [hrightCanonicalLookup hrightStep]].
    assert (hleftEq : leftOutput = leftCanonical).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        leftTruthCode leftTruthStep current leftOutput leftCanonical
        hleftLookup hleftCanonicalLookup).
    }
    assert (hrightEq : rightOutput = rightCanonical).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        rightTruthCode rightTruthStep current rightOutput rightCanonical
        hrightLookup hrightCanonicalLookup).
    }
    rewrite hleftEq, hrightEq.
    exact (raw_rankZeroTruthClosedStep_extensional M hPA
      assignmentCode assignmentStep
      leftTruthCode leftTruthStep leftSupportCode leftSupportStep
      rightTruthCode rightTruthStep rightSupportCode rightSupportStep
      current leftCanonical rightCanonical hagree hleftStep hrightStep).
Qed.

Theorem raw_rankZeroTruthTraversals_agree_below : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep,
  RawRankZeroTruthTraversal M limit assignmentCode assignmentStep
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep ->
  RawRankZeroTruthTraversal M limit assignmentCode assignmentStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep ->
  RawRankZeroTruthTablesAgreeBelow M limit
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep
    hleftTraversal hrightTraversal.
  set (parameterEnv := scons M limit
    (scons M leftTruthCode (scons M leftTruthStep
      (scons M leftSupportCode (scons M leftSupportStep
        (scons M rightTruthCode (scons M rightTruthStep
          (scons M rightSupportCode (scons M rightSupportStep
            (fun _ : nat => raw_zero M)))))))))).
  set (phi := rankZeroTruthTablesAgreeThroughTermAt
    (tVar 0) (tVar 1)
    (tVar 2) (tVar 3) (tVar 4) (tVar 5)
    (tVar 6) (tVar 7) (tVar 8) (tVar 9)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_rankZeroTruthTablesAgreeThroughTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 0) (tVar 1)
          (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _. intros code hcode.
      exfalso. exact (raw_not_lt_zero M hPA code hcode).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_rankZeroTruthTablesAgreeThroughTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1)
          (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9)) hcurrent)
        as hcurrentRaw.
      apply (proj2
        (raw_sat_rankZeroTruthTablesAgreeThroughTermAt_iff M
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
      exact (raw_rankZeroTruthTablesAgreeBelow_succ M hPA
        limit assignmentCode assignmentStep
        leftTruthCode leftTruthStep leftSupportCode leftSupportStep
        rightTruthCode rightTruthStep rightSupportCode rightSupportStep
        current hleftTraversal hrightTraversal hcurrentLimit
        (hcurrentRaw hcurrentLe)).
  }
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_rankZeroTruthTablesAgreeThroughTermAt_iff M
      (scons M limit parameterEnv)
      (tVar 0) (tVar 1)
      (tVar 2) (tVar 3) (tVar 4) (tVar 5)
      (tVar 6) (tVar 7) (tVar 8) (tVar 9))
    (hall limit)) as hlimit.
  unfold parameterEnv in hlimit.
  cbn [raw_term_eval scons] in hlimit.
  exact (hlimit (raw_le_refl_traversal M hPA limit)).
Qed.

Theorem raw_rankZeroTruthCertificate_output_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep leftOutput rightOutput,
  RawRankZeroTruthCertificate M
    root leftOutput assignmentCode assignmentStep ->
  RawRankZeroTruthCertificate M
    root rightOutput assignmentCode assignmentStep ->
  leftOutput = rightOutput.
Proof.
  intros M hPA root assignmentCode assignmentStep leftOutput rightOutput
    hleft hright.
  destruct hleft as [leftSupportCode hleft].
  destruct hleft as [leftSupportStep hleft].
  destruct hleft as [leftTruthCode hleft].
  destruct hleft as [leftTruthStep hleft].
  destruct hleft as
    [hleftTraversal [hleftSupport [hleftLookup hleftBit]]].
  destruct hright as [rightSupportCode hright].
  destruct hright as [rightSupportStep hright].
  destruct hright as [rightTruthCode hright].
  destruct hright as [rightTruthStep hright].
  destruct hright as
    [hrightTraversal [hrightSupport [hrightLookup hrightBit]]].
  pose proof (raw_rankZeroTruthTraversals_agree_below M hPA
    (raw_succ M root) assignmentCode assignmentStep
    leftTruthCode leftTruthStep leftSupportCode leftSupportStep
    rightTruthCode rightTruthStep rightSupportCode rightSupportStep
    hleftTraversal hrightTraversal) as hagree.
  assert (hrootLt : rawLt M root (raw_succ M root)).
  { exact (raw_assignment_lt_self_succ M hPA root). }
  exact (hagree root hrootLt hleftSupport hrightSupport
    leftOutput rightOutput hleftLookup hrightLookup).
Qed.

Corollary raw_sat_rankZeroTruthCertificateTermAt_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep leftOutput rightOutput e,
  raw_formula_sat M e
    (rankZeroTruthCertificateTermAt
      root leftOutput assignmentCode assignmentStep) ->
  raw_formula_sat M e
    (rankZeroTruthCertificateTermAt
      root rightOutput assignmentCode assignmentStep) ->
  raw_term_eval M e leftOutput = raw_term_eval M e rightOutput.
Proof.
  intros M hPA root assignmentCode assignmentStep
    leftOutput rightOutput e hleft hright.
  apply (raw_rankZeroTruthCertificate_output_functional M hPA
    (raw_term_eval M e root)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep)).
  - apply (proj1 (raw_sat_rankZeroTruthCertificateTermAt_iff
      M e root leftOutput assignmentCode assignmentStep)). exact hleft.
  - apply (proj1 (raw_sat_rankZeroTruthCertificateTermAt_iff
      M e root rightOutput assignmentCode assignmentStep)). exact hright.
Qed.

(** A certificate's public root lookup is backed by the closed local row at
    that root, rather than merely being an arbitrary beta-table entry. *)
Theorem raw_rankZeroTruthCertificate_root_closed_step : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root output assignmentCode assignmentStep,
  RawRankZeroTruthCertificate M
    root output assignmentCode assignmentStep ->
  exists supportCode supportStep truthCode truthStep,
    RawRankZeroTruthClosedStep M
      root output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep.
Proof.
  intros M hPA root output assignmentCode assignmentStep hcert.
  destruct hcert as [supportCode hcert].
  destruct hcert as [supportStep hcert].
  destruct hcert as [truthCode hcert].
  destruct hcert as [truthStep hcert].
  destruct hcert as [htraversal [hsupport [hlookup hbit]]].
  destruct htraversal as [hsupportDefined [htruthDefined hrows]].
  destruct (hrows root (raw_assignment_lt_self_succ M hPA root) hsupport)
    as [canonical [hcanonicalLookup hstep]].
  assert (houtput : output = canonical).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      truthCode truthStep root output canonical
      hlookup hcanonicalLookup).
  }
  rewrite <- houtput in hstep.
  exists supportCode, supportStep, truthCode, truthStep.
  exact hstep.
Qed.

(** Close global functionality back into an explicit theorem of PA.  The
    binders are root, assignment code, assignment step, left output, and
    right output. *)
Definition rankZeroTruthCertificateFunctionalFormula : formula :=
  pAll (pAll (pAll (pAll (pAll
    (pImp
      (pAnd
        (rankZeroTruthCertificateTermAt
          (tVar 4) (tVar 1) (tVar 3) (tVar 2))
        (rankZeroTruthCertificateTermAt
          (tVar 4) (tVar 0) (tVar 3) (tVar 2)))
      (pEq (tVar 1) (tVar 0))))))).

Lemma raw_sat_rankZeroTruthCertificateFunctionalFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e rankZeroTruthCertificateFunctionalFormula <->
  forall root assignmentCode assignmentStep leftOutput rightOutput : M,
    (RawRankZeroTruthCertificate M
      root leftOutput assignmentCode assignmentStep /\
    RawRankZeroTruthCertificate M
      root rightOutput assignmentCode assignmentStep) ->
    leftOutput = rightOutput.
Proof.
  intros M e.
  unfold rankZeroTruthCertificateFunctionalFormula.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_rankZeroTruthCertificateTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem rankZeroTruthCertificateFunctionalFormula_sentence :
  Formula.Sentence rankZeroTruthCertificateFunctionalFormula.
Proof.
  intros k hfree.
  unfold rankZeroTruthCertificateFunctionalFormula in hfree.
  cbn in hfree. lia.
Qed.

Theorem rankZeroTruthCertificateFunctionalFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e rankZeroTruthCertificateFunctionalFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_rankZeroTruthCertificateFunctionalFormula_iff M e)).
  intros root assignmentCode assignmentStep leftOutput rightOutput
    [hleft hright].
  exact (raw_rankZeroTruthCertificate_output_functional M hPA
    root assignmentCode assignmentStep leftOutput rightOutput
    hleft hright).
Qed.

Theorem PA_proves_rankZeroTruthCertificateFunctionalFormula :
  Formula.BProv Formula.Ax_s []
    rankZeroTruthCertificateFunctionalFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact rankZeroTruthCertificateFunctionalFormula_sentence.
  - exact rankZeroTruthCertificateFunctionalFormula_raw_valid.
Qed.

(** ------------------------------------------------------------------
    CRT extension capacity and the remaining nonstandard-totality seam. *)

Definition RawRankZeroTruthTableAppendCapacity (M : RawPAModel)
    (target output supportStep truthStep : M) : Prop :=
  RawCommonMultipleThrough M target supportStep /\
  rawLt M (rawNumeralValue M 1)
    (rawBetaModulus M supportStep target) /\
  RawCommonMultipleThrough M target truthStep /\
  rawLt M output (rawBetaModulus M truthStep target).

Theorem raw_rankZeroTruthTables_append_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall target output supportCode supportStep truthCode truthStep,
  RawRankZeroTruthTableAppendCapacity M
    target output supportStep truthStep ->
  exists newSupportCode newTruthCode,
    RawBetaCodeExtension M supportCode supportStep target
      (rawNumeralValue M 1) newSupportCode /\
    RawBetaCodeExtension M truthCode truthStep target
      output newTruthCode.
Proof.
  intros M hPA target output supportCode supportStep truthCode truthStep
    [hsupportCommon [hsupportBound [htruthCommon houtputBound]]].
  destruct (raw_betaCodeExtension_exists M hPA supportCode supportStep
    target (rawNumeralValue M 1) hsupportCommon hsupportBound)
    as [newSupportCode hsupport].
  destruct (raw_betaCodeExtension_exists M hPA truthCode truthStep
    target output htruthCommon houtputBound) as [newTruthCode htruth].
  exists newSupportCode, newTruthCode. split; assumption.
Qed.

(** [admissible root assignmentCode assignmentStep] is intended to combine
    a future nonstandard rank-zero well-formedness trace with sufficient
    assignment definedness for every variable in the root.  Proving this
    realization obligation requires that missing syntax traversal; it is a
    named proposition here, not an axiom or an assumed theorem. *)
Definition RawRankZeroTruthCertificateTotalityFor (M : RawPAModel)
    (admissible : M -> M -> M -> Prop) : Prop :=
  forall root assignmentCode assignmentStep,
    admissible root assignmentCode assignmentStep ->
    exists output,
      RawRankZeroTruthCertificate M
        root output assignmentCode assignmentStep.

End PABoundedRawCodedRankZeroTruthTraversal.
