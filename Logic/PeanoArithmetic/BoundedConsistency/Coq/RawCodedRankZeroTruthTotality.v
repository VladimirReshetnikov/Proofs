(**
  Unconditional rank-zero truth totality on the honest coded-syntax domain.

  [RawCodedRankZeroTruthRealization] isolated one remaining condition:
  equality payload terms had to satisfy the fixed-step evaluation capacity
  predicate.  The step-parametric construction in
  [RawCodedTermEvaluationCapacity] now proves that predicate from each term's
  model-internal syntax certificate.  Consequently every arithmetized
  quantifier-free syntax certificate has a unique truth certificate, even
  when all codes and traversal bounds are nonstandard model elements.

  The final section closes this semantic theorem back into an actual closed
  theorem of PA.  It says uniformly that any root/assignment satisfying the
  genuine formula [rankZeroSyntaxRealizableTermAt] has some output satisfying
  [rankZeroTruthCertificateTermAt].
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  PolynomialPairInjectivity RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedTermEvaluationTraversal RawCodedTermEvaluationRealization
  RawCodedTermEvaluationCapacity
  RawCodedRankZeroTruthStep RawCodedRankZeroTruthTraversal
  RawCodedRankZeroTruthRealization.

Import ListNotations.

Module PABoundedRawCodedRankZeroTruthTotality.

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
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedTermEvaluationCapacity.
Import PABoundedRawCodedRankZeroTruthStep.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedRankZeroTruthRealization.

(** ------------------------------------------------------------------
    Discharge the inherited atomic-term condition. *)

(** The formula-level term adequacy hypothesis is included in the public
    interface because it supplies the term-syntax witnesses used by equality
    rows.  Once one such witness is unpacked, capacity follows solely from
    that witness; no additional property of the enclosing formula is used. *)
Theorem raw_rankZeroAtomicTermCapacity_of_adequate : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall bound assignmentCode assignmentStep supportCode supportStep,
  RawRankZeroSyntaxTermAdequate M bound
    assignmentCode assignmentStep supportCode supportStep ->
  RawRankZeroAtomicTermCapacity M bound
    assignmentCode assignmentStep supportCode supportStep.
Proof.
  intros M hPA bound assignmentCode assignmentStep supportCode supportStep
    _ code left right _ _ _ termCode termSupportCode termSupportStep
    _ htermSyntax.
  exact (raw_termEvaluationRealizationCapacity_of_certificate M hPA
    termCode assignmentCode assignmentStep
    termSupportCode termSupportStep htermSyntax).
Qed.

(** In fact the capacity transformer is uniform once a term certificate is
    handed to it.  This stronger alias is useful when callers already carry
    the equality payload witnesses separately. *)
Corollary raw_rankZeroAtomicTermCapacity_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall bound assignmentCode assignmentStep supportCode supportStep,
  RawRankZeroAtomicTermCapacity M bound
    assignmentCode assignmentStep supportCode supportStep.
Proof.
  intros M hPA bound assignmentCode assignmentStep supportCode supportStep
    code left right _ _ _ termCode termSupportCode termSupportStep
    _ htermSyntax.
  exact (raw_termEvaluationRealizationCapacity_of_certificate M hPA
    termCode assignmentCode assignmentStep
    termSupportCode termSupportStep htermSyntax).
Qed.

(** ------------------------------------------------------------------
    Unconditional semantic totality and uniqueness. *)

Theorem raw_rankZeroTruthCertificateWithTables_exists_of_syntax : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep supportCode supportStep,
  RawRankZeroSyntaxCertificateWithSupport M
    root assignmentCode assignmentStep supportCode supportStep ->
  exists output truthCode truthStep : M,
    RawRankZeroTruthCertificateWithTables M
      root output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep.
Proof.
  intros M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax.
  apply (raw_rankZeroTruthCertificateWithTables_exists_of_syntax_capacity
    M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax).
  exact (raw_rankZeroAtomicTermCapacity_all M hPA
    (raw_succ M root) assignmentCode assignmentStep
    supportCode supportStep).
Qed.

Corollary raw_rankZeroTruthCertificate_exists_of_syntax : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep supportCode supportStep,
  RawRankZeroSyntaxCertificateWithSupport M
    root assignmentCode assignmentStep supportCode supportStep ->
  exists output : M,
    RawRankZeroTruthCertificate M
      root output assignmentCode assignmentStep.
Proof.
  intros M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax.
  destruct (raw_rankZeroTruthCertificateWithTables_exists_of_syntax
    M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax) as [output [truthCode [truthStep hcertificate]]].
  exists output, supportCode, supportStep, truthCode, truthStep.
  exact hcertificate.
Qed.

Corollary raw_rankZeroTruthCertificate_exists_unique_of_syntax : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep supportCode supportStep,
  RawRankZeroSyntaxCertificateWithSupport M
    root assignmentCode assignmentStep supportCode supportStep ->
  exists output : M,
    RawRankZeroTruthCertificate M
      root output assignmentCode assignmentStep /\
    forall otherOutput,
      RawRankZeroTruthCertificate M
        root otherOutput assignmentCode assignmentStep ->
      output = otherOutput.
Proof.
  intros M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax.
  destruct (raw_rankZeroTruthCertificate_exists_of_syntax M hPA
    root assignmentCode assignmentStep supportCode supportStep hsyntax)
    as [output houtput].
  exists output. split; [exact houtput |].
  intros otherOutput hother.
  exact (raw_rankZeroTruthCertificate_output_functional M hPA
    root assignmentCode assignmentStep output otherOutput houtput hother).
Qed.

Corollary raw_rankZeroTruthCertificate_exists_of_realizable_syntax :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep,
  RawRankZeroSyntaxRealizable M root assignmentCode assignmentStep ->
  exists output : M,
    RawRankZeroTruthCertificate M
      root output assignmentCode assignmentStep.
Proof.
  intros M hPA root assignmentCode assignmentStep
    [supportCode [supportStep hsyntax]].
  exact (raw_rankZeroTruthCertificate_exists_of_syntax M hPA
    root assignmentCode assignmentStep supportCode supportStep hsyntax).
Qed.

Corollary raw_rankZeroTruthCertificate_exists_unique_of_realizable_syntax :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep,
  RawRankZeroSyntaxRealizable M root assignmentCode assignmentStep ->
  exists output : M,
    RawRankZeroTruthCertificate M
      root output assignmentCode assignmentStep /\
    forall otherOutput,
      RawRankZeroTruthCertificate M
        root otherOutput assignmentCode assignmentStep ->
      output = otherOutput.
Proof.
  intros M hPA root assignmentCode assignmentStep hsyntax.
  destruct (raw_rankZeroTruthCertificate_exists_of_realizable_syntax
    M hPA root assignmentCode assignmentStep hsyntax)
    as [output houtput].
  exists output. split; [exact houtput |].
  intros otherOutput hother.
  exact (raw_rankZeroTruthCertificate_output_functional M hPA
    root assignmentCode assignmentStep output otherOutput houtput hother).
Qed.

Theorem raw_rankZeroTruthCertificate_totality_for_syntax : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawRankZeroTruthCertificateTotalityFor M
    (RawRankZeroSyntaxRealizable M).
Proof.
  intros M hPA root assignmentCode assignmentStep hsyntax.
  exact (raw_rankZeroTruthCertificate_exists_of_realizable_syntax
    M hPA root assignmentCode assignmentStep hsyntax).
Qed.

(** ------------------------------------------------------------------
    Close totality into an explicit theorem of PA. *)

(** Outside binders are [root, assignmentCode, assignmentStep].  Under the
    output existential they become variables three, two, and one, while the
    proposed truth output is variable zero. *)
Definition rankZeroTruthTotalityOnSyntaxFormula : formula :=
  pAll (pAll (pAll
    (pImp
      (rankZeroSyntaxRealizableTermAt
        (tVar 2) (tVar 1) (tVar 0))
      (pEx
        (rankZeroTruthCertificateTermAt
          (tVar 3) (tVar 0) (tVar 2) (tVar 1)))))).

Lemma raw_sat_rankZeroTruthTotalityOnSyntaxFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e rankZeroTruthTotalityOnSyntaxFormula <->
  forall root assignmentCode assignmentStep : M,
    RawRankZeroSyntaxRealizable M
      root assignmentCode assignmentStep ->
    exists output : M,
      RawRankZeroTruthCertificate M
        root output assignmentCode assignmentStep.
Proof.
  intros M e.
  unfold rankZeroTruthTotalityOnSyntaxFormula.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_rankZeroSyntaxRealizableTermAt_iff.
  repeat setoid_rewrite raw_sat_rankZeroTruthCertificateTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem rankZeroTruthTotalityOnSyntaxFormula_sentence :
  Formula.Sentence rankZeroTruthTotalityOnSyntaxFormula.
Proof.
  intros k hfree.
  unfold rankZeroTruthTotalityOnSyntaxFormula,
    rankZeroSyntaxRealizableTermAt,
    rankZeroSyntaxCertificateWithSupportTermAt,
    rankZeroSyntaxTraversalTermAt,
    rankZeroSyntaxStepTermAt,
    rankZeroSyntaxWitnessRowTermAt,
    rankZeroSyntaxTermAdequateTermAt,
    termSyntaxRealizableTermAt,
    termSyntaxCertificateWithSupportTermAt,
    termSyntaxTraversalTermAt,
    termSyntaxStepTermAt,
    termSyntaxWitnessRowTermAt,
    termSyntaxAssignmentAdequateTermAt,
    rankZeroTruthCertificateTermAt,
    rankZeroTruthCertificateWithTablesTermAt,
    rankZeroTruthTraversalTermAt,
    rankZeroTruthClosedStepTermAt,
    rankZeroTruthClosedWitnessRowTermAt,
    rankZeroEqCertifiedRowTermAt,
    rankZeroImpClosedRowTermAt,
    rankZeroAndClosedRowTermAt,
    rankZeroOrClosedRowTermAt,
    formulaCodeSupportedTermAt,
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

Theorem rankZeroTruthTotalityOnSyntaxFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e rankZeroTruthTotalityOnSyntaxFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_rankZeroTruthTotalityOnSyntaxFormula_iff M e)).
  exact (raw_rankZeroTruthCertificate_totality_for_syntax M hPA).
Qed.

Theorem PA_proves_rankZeroTruthTotalityOnSyntaxFormula :
  Formula.BProv Formula.Ax_s []
    rankZeroTruthTotalityOnSyntaxFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact rankZeroTruthTotalityOnSyntaxFormula_sentence.
  - exact rankZeroTruthTotalityOnSyntaxFormula_raw_valid.
Qed.

End PABoundedRawCodedRankZeroTruthTotality.
