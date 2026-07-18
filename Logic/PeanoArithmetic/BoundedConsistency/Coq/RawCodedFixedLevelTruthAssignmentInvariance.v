(**
  Locality of represented truth with respect to beta-coded assignments.

  A coded formula can inspect only assignment indices below its own code:
  every variable index is a strict member of a term code, and every term
  code is a strict member of its enclosing equality/formula code.  This file
  makes the corresponding assignment-agreement relation explicit and begins
  the certificate-level locality proof needed by the eigenvariable rules.

  The first layer is independent of fixed-level truth.  It proves that two
  represented prepends with the same head and source agree on their common
  advertised prefix, and that a term-evaluation certificate can be reused
  unchanged under any assignment agreeing through the root term code.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedProofDescent
  RawCodedTermEvaluationStep RawCodedTermEvaluationTraversal
  RawCodedRankZeroTruthStep RawCodedRankZeroTruthTraversal
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelTruthLaws.

Import ListNotations.

Module PABoundedRawCodedFixedLevelTruthAssignmentInvariance.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedTermEvaluationStep.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedRankZeroTruthStep.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelTruthLaws.

Definition assignmentInvariantIff (left right : formula) : formula :=
  pAnd (pImp left right) (pImp right left).

Definition codedAssignmentsAgreeThroughTermAt
    (leftCode leftStep rightCode rightStep bound : term) : formula :=
  pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 1) (liftTerm 2 bound))
      (assignmentInvariantIff
        (codedAssignmentLookupTermAt
          (liftTerm 2 leftCode) (liftTerm 2 leftStep)
          (tVar 1) (tVar 0))
        (codedAssignmentLookupTermAt
          (liftTerm 2 rightCode) (liftTerm 2 rightStep)
          (tVar 1) (tVar 0))))).

Definition RawCodedAssignmentsAgreeThrough (M : RawPAModel)
    (leftCode leftStep rightCode rightStep bound : M) : Prop :=
  forall index value : M,
    rawLt M index bound ->
    (RawCodedAssignmentLookup M leftCode leftStep index value <->
     RawCodedAssignmentLookup M rightCode rightStep index value).

Arguments RawCodedAssignmentsAgreeThrough
  M leftCode leftStep rightCode rightStep bound : clear implicits.

Lemma raw_assignmentInvariant_eval_liftTerm_two : forall
    (M : RawPAModel) first second (e : nat -> M) t,
  raw_term_eval M (scons M first (scons M second e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M first second e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 2) with (S (S index)) by lia. reflexivity.
Qed.

Lemma raw_sat_codedAssignmentsAgreeThroughTermAt_iff : forall
    (M : RawPAModel) e leftCode leftStep rightCode rightStep bound,
  raw_formula_sat M e
    (codedAssignmentsAgreeThroughTermAt
      leftCode leftStep rightCode rightStep bound) <->
  RawCodedAssignmentsAgreeThrough M
    (raw_term_eval M e leftCode) (raw_term_eval M e leftStep)
    (raw_term_eval M e rightCode) (raw_term_eval M e rightStep)
    (raw_term_eval M e bound).
Proof.
  intros. unfold codedAssignmentsAgreeThroughTermAt,
    assignmentInvariantIff, RawCodedAssignmentsAgreeThrough.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  repeat setoid_rewrite raw_assignmentInvariant_eval_liftTerm_two.
  cbn [raw_term_eval scons]. tauto.
Qed.

Lemma raw_codedAssignmentsAgreeThrough_refl : forall
    (M : RawPAModel) code step bound,
  RawCodedAssignmentsAgreeThrough M code step code step bound.
Proof. intros M code step bound index value _. reflexivity. Qed.

Lemma raw_codedAssignmentsAgreeThrough_sym : forall
    (M : RawPAModel) leftCode leftStep rightCode rightStep bound,
  RawCodedAssignmentsAgreeThrough M
    leftCode leftStep rightCode rightStep bound ->
  RawCodedAssignmentsAgreeThrough M
    rightCode rightStep leftCode leftStep bound.
Proof.
  intros M leftCode leftStep rightCode rightStep bound hagree
    index value hindex. symmetry. exact (hagree index value hindex).
Qed.

Lemma raw_codedAssignmentsAgreeThrough_restrict : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftCode leftStep rightCode rightStep smallBound largeBound,
  rawLt M smallBound largeBound ->
  RawCodedAssignmentsAgreeThrough M
    leftCode leftStep rightCode rightStep largeBound ->
  RawCodedAssignmentsAgreeThrough M
    leftCode leftStep rightCode rightStep smallBound.
Proof.
  intros M hPA leftCode leftStep rightCode rightStep
    smallBound largeBound hsmall hagree index value hindex.
  exact (hagree index value
    (raw_assignment_lt_trans M hPA index smallBound largeBound
      hindex hsmall)).
Qed.

(** Two prepend witnesses with the same source, head, and bound may use
    different beta codes and steps, but all of their advertised rows agree.
    The extra successor covers the new head slot. *)
Lemma raw_codedAssignmentPrepends_agree : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sourceCode sourceStep head bound
      leftCode leftStep rightCode rightStep,
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound ->
  RawCodedAssignmentPrepend M
    sourceCode sourceStep head bound leftCode leftStep ->
  RawCodedAssignmentPrepend M
    sourceCode sourceStep head bound rightCode rightStep ->
  RawCodedAssignmentsAgreeThrough M
    leftCode leftStep rightCode rightStep (raw_succ M bound).
Proof.
  intros M hPA sourceCode sourceStep head bound
    leftCode leftStep rightCode rightStep hdefined hleft hright
    index value hindex.
  destruct (raw_assignment_zero_or_successor M hPA index)
    as [-> | [predecessor ->]].
  - rewrite (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
      sourceCode sourceStep head bound leftCode leftStep value hleft).
    rewrite (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
      sourceCode sourceStep head bound rightCode rightStep value hright).
    reflexivity.
  - assert (hpredecessor : rawLt M predecessor bound).
    {
      destruct (raw_lt_succ_cases M hPA
        (raw_succ M predecessor) bound hindex) as [hlt | heq].
      - exact (raw_assignment_lt_trans M hPA predecessor
          (raw_succ M predecessor) bound
          (raw_assignment_lt_self_succ M hPA predecessor) hlt).
      - rewrite <- heq.
        exact (raw_assignment_lt_self_succ M hPA predecessor).
    }
    rewrite (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
      sourceCode sourceStep head bound leftCode leftStep
      hdefined hleft predecessor hpredecessor value).
    rewrite (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
      sourceCode sourceStep head bound rightCode rightStep
      hdefined hright predecessor hpredecessor value).
    reflexivity.
Qed.

(** The common-prefix form used by eigenvariable normalization. *)
Lemma raw_codedAssignmentPrepends_agree_common_prefix : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sourceCode sourceStep head commonBound leftBound rightBound
      leftCode leftStep rightCode rightStep,
  rawLt M commonBound leftBound ->
  rawLt M commonBound rightBound ->
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep leftBound ->
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep rightBound ->
  RawCodedAssignmentPrepend M
    sourceCode sourceStep head leftBound leftCode leftStep ->
  RawCodedAssignmentPrepend M
    sourceCode sourceStep head rightBound rightCode rightStep ->
  RawCodedAssignmentsAgreeThrough M
    leftCode leftStep rightCode rightStep commonBound.
Proof.
  intros M hPA sourceCode sourceStep head commonBound
    leftBound rightBound leftCode leftStep rightCode rightStep
    hcommonLeft hcommonRight hdefinedLeft hdefinedRight hleft hright.
  pose proof (raw_codedAssignmentPrepend_restrict M hPA
    sourceCode sourceStep head commonBound leftBound leftCode leftStep
    hcommonLeft hleft) as hleftCommon.
  pose proof (raw_codedAssignmentPrepend_restrict M hPA
    sourceCode sourceStep head commonBound rightBound rightCode rightStep
    hcommonRight hright) as hrightCommon.
  pose proof (raw_codedAssignmentPrepends_agree M hPA
    sourceCode sourceStep head commonBound leftCode leftStep
    rightCode rightStep
    (raw_codedAssignmentDefinedThrough_of_lt M hPA
      sourceCode sourceStep commonBound leftBound
      hcommonLeft hdefinedLeft)
    hleftCommon hrightCommon) as hagreeSucc.
  exact (raw_codedAssignmentsAgreeThrough_restrict M hPA
    leftCode leftStep rightCode rightStep commonBound
    (raw_succ M commonBound)
    (raw_assignment_lt_self_succ M hPA commonBound) hagreeSucc).
Qed.

(** Only variable rows mention the external assignment.  Agreement through
    the root term code therefore lets us reuse every support/value table and
    every non-variable local row verbatim. *)
Lemma raw_termEvaluationClosedStep_assignment_transport : forall
    (M : RawPAModel), RawPASatisfies M -> forall root
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      tableCode tableStep supportCode supportStep code value,
  RawCodedAssignmentsAgreeThrough M
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep root ->
  rawLt M code (raw_succ M root) ->
  RawTermEvaluationClosedStep M code value
    sourceAssignmentCode sourceAssignmentStep
    tableCode tableStep supportCode supportStep ->
  RawTermEvaluationClosedStep M code value
    targetAssignmentCode targetAssignmentStep
    tableCode tableStep supportCode supportStep.
Proof.
  intros M hPA root sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    tableCode tableStep supportCode supportStep code value
    hagree hcode
    (left & leftValue & right & rightValue & hrow).
  exists left, leftValue, right, rightValue.
  destruct hrow as
    [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - left. destruct hvar as [hshape hlookup]. split; [exact hshape |].
    assert (hleftCode : rawLt M left code).
    { rewrite hshape. apply rawProofListCode_member_lt;
        [exact hPA | simpl; tauto]. }
    assert (hleftRoot : rawLt M left root).
    {
      destruct (raw_lt_succ_cases M hPA code root hcode) as [hlt | ->].
      - exact (raw_assignment_lt_trans M hPA left code root
          hleftCode hlt).
      - exact hleftCode.
    }
    exact (proj1 (hagree left value hleftRoot) hlookup).
  - right. left. exact hzero.
  - right. right. left. exact hsucc.
  - right. right. right. left. exact hadd.
  - right. right. right. right. exact hmul.
Qed.

Theorem raw_termEvaluationCertificate_assignment_transport : forall
    (M : RawPAModel), RawPASatisfies M -> forall root value
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  RawCodedAssignmentsAgreeThrough M
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep root ->
  RawTermEvaluationCertificate M root value
    sourceAssignmentCode sourceAssignmentStep ->
  RawTermEvaluationCertificate M root value
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA root value
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hagree
    (supportCode & supportStep & tableCode & tableStep &
      htraversal & hrootSupported & hrootValue).
  exists supportCode, supportStep, tableCode, tableStep.
  split; [| split; assumption].
  destruct htraversal as [hsupport [htable hrows]].
  split; [exact hsupport |]. split; [exact htable |].
  intros code hcode hsupported.
  destruct (hrows code hcode hsupported) as [codeValue [hlookup hstep]].
  exists codeValue. split; [exact hlookup |].
  exact (raw_termEvaluationClosedStep_assignment_transport M hPA root
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    tableCode tableStep supportCode supportStep code codeValue
    hagree hcode hstep).
Qed.

Corollary raw_termEvaluationCertificate_assignment_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall root value
      leftAssignmentCode leftAssignmentStep
      rightAssignmentCode rightAssignmentStep,
  RawCodedAssignmentsAgreeThrough M
    leftAssignmentCode leftAssignmentStep
    rightAssignmentCode rightAssignmentStep root ->
  (RawTermEvaluationCertificate M root value
      leftAssignmentCode leftAssignmentStep <->
   RawTermEvaluationCertificate M root value
      rightAssignmentCode rightAssignmentStep).
Proof.
  intros M hPA root value
    leftAssignmentCode leftAssignmentStep
    rightAssignmentCode rightAssignmentStep hagree. split.
  - exact (raw_termEvaluationCertificate_assignment_transport M hPA
      root value leftAssignmentCode leftAssignmentStep
      rightAssignmentCode rightAssignmentStep hagree).
  - exact (raw_termEvaluationCertificate_assignment_transport M hPA
      root value rightAssignmentCode rightAssignmentStep
      leftAssignmentCode leftAssignmentStep
      (raw_codedAssignmentsAgreeThrough_sym M
        leftAssignmentCode leftAssignmentStep
        rightAssignmentCode rightAssignmentStep root hagree)).
Qed.

(** Rank-zero truth tables can likewise be reused: only equality rows refer
    to the external assignment, and their two evaluator certificates are
    transported by the preceding theorem. *)
Lemma raw_rankZeroTruthClosedStep_assignment_transport : forall
    (M : RawPAModel), RawPASatisfies M -> forall root
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      truthCode truthStep supportCode supportStep code output,
  RawCodedAssignmentsAgreeThrough M
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep root ->
  rawLt M code (raw_succ M root) ->
  RawRankZeroTruthClosedStep M code output
    sourceAssignmentCode sourceAssignmentStep
    truthCode truthStep supportCode supportStep ->
  RawRankZeroTruthClosedStep M code output
    targetAssignmentCode targetAssignmentStep
    truthCode truthStep supportCode supportStep.
Proof.
  intros M hPA root sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    truthCode truthStep supportCode supportStep code output
    hagree hcode
    (left & leftValue & right & rightValue & hrow).
  exists left, leftValue, right, rightValue.
  destruct hrow as
    [heq | [hbot | [himp | [hand | hor]]]].
  - left. destruct heq as [hshape [hleft [hright htruth]]].
    assert (hleftCode : rawLt M left code).
    { rewrite hshape. unfold rawFormulaEqCode.
      apply rawProofListCode_member_lt; [exact hPA | simpl; tauto]. }
    assert (hrightCode : rawLt M right code).
    { rewrite hshape. unfold rawFormulaEqCode.
      apply rawProofListCode_member_lt; [exact hPA | simpl; tauto]. }
    assert (hleftRoot : rawLt M left root).
    {
      destruct (raw_lt_succ_cases M hPA code root hcode) as [hlt | ->].
      - exact (raw_assignment_lt_trans M hPA left code root
          hleftCode hlt).
      - exact hleftCode.
    }
    assert (hrightRoot : rawLt M right root).
    {
      destruct (raw_lt_succ_cases M hPA code root hcode) as [hlt | ->].
      - exact (raw_assignment_lt_trans M hPA right code root
          hrightCode hlt).
      - exact hrightCode.
    }
    repeat split.
    + exact hshape.
    + apply (raw_termEvaluationCertificate_assignment_transport M hPA
        left leftValue sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep).
      * exact (raw_codedAssignmentsAgreeThrough_restrict M hPA
          sourceAssignmentCode sourceAssignmentStep
          targetAssignmentCode targetAssignmentStep left root
          hleftRoot hagree).
      * exact hleft.
    + apply (raw_termEvaluationCertificate_assignment_transport M hPA
        right rightValue sourceAssignmentCode sourceAssignmentStep
        targetAssignmentCode targetAssignmentStep).
      * exact (raw_codedAssignmentsAgreeThrough_restrict M hPA
          sourceAssignmentCode sourceAssignmentStep
          targetAssignmentCode targetAssignmentStep right root
          hrightRoot hagree).
      * exact hright.
    + exact htruth.
  - right. left. exact hbot.
  - right. right. left. exact himp.
  - right. right. right. left. exact hand.
  - right. right. right. right. exact hor.
Qed.

Theorem raw_rankZeroTruthCertificate_assignment_transport : forall
    (M : RawPAModel), RawPASatisfies M -> forall root output
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  RawCodedAssignmentsAgreeThrough M
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep root ->
  RawRankZeroTruthCertificate M root output
    sourceAssignmentCode sourceAssignmentStep ->
  RawRankZeroTruthCertificate M root output
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA root output
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hagree
    (supportCode & supportStep & truthCode & truthStep &
      htraversal & hrootSupported & hrootOutput & htruthBit).
  exists supportCode, supportStep, truthCode, truthStep.
  split.
  - destruct htraversal as [hsupport [htruth hrows]].
    split; [exact hsupport |]. split; [exact htruth |].
    intros code hcode hsupported.
    destruct (hrows code hcode hsupported) as
      [codeOutput [hlookup hstep]].
    exists codeOutput. split; [exact hlookup |].
    exact (raw_rankZeroTruthClosedStep_assignment_transport M hPA root
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep
      truthCode truthStep supportCode supportStep code codeOutput
      hagree hcode hstep).
  - repeat split; assumption.
Qed.

Corollary raw_rankZeroTruthCertificate_assignment_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall root output
      leftAssignmentCode leftAssignmentStep
      rightAssignmentCode rightAssignmentStep,
  RawCodedAssignmentsAgreeThrough M
    leftAssignmentCode leftAssignmentStep
    rightAssignmentCode rightAssignmentStep root ->
  (RawRankZeroTruthCertificate M root output
      leftAssignmentCode leftAssignmentStep <->
   RawRankZeroTruthCertificate M root output
      rightAssignmentCode rightAssignmentStep).
Proof.
  intros M hPA root output
    leftAssignmentCode leftAssignmentStep
    rightAssignmentCode rightAssignmentStep hagree. split.
  - exact (raw_rankZeroTruthCertificate_assignment_transport M hPA
      root output leftAssignmentCode leftAssignmentStep
      rightAssignmentCode rightAssignmentStep hagree).
  - exact (raw_rankZeroTruthCertificate_assignment_transport M hPA
      root output rightAssignmentCode rightAssignmentStep
      leftAssignmentCode leftAssignmentStep
      (raw_codedAssignmentsAgreeThrough_sym M
        leftAssignmentCode leftAssignmentStep
        rightAssignmentCode rightAssignmentStep root hagree)).
Qed.

End PABoundedRawCodedFixedLevelTruthAssignmentInvariance.
