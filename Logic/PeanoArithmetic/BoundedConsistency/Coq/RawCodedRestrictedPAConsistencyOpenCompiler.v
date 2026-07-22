(**
  Reduce the nonstandard successor certificate to one exact open proof.

  The compact uniform-provability theorem used to expose an arbitrary
  successor target code.  The transparent target graph is substantially
  sharper: after its numeral-code witness is opened, the target is exactly

      forall certificate, RestrictedPAProof(level, certificate) -> bottom.

  This file proves that raw-code view without decoding a nonstandard formula.
  It then connects the concrete implication-introduction/universal-
  introduction constructors to the compact successor interface.  What
  remains is stated as [RawRestrictedPAConsistencyOpenContradictionCompiler]:
  from the incoming proof of the lower consistency target, build a covered
  proof of bottom under the single, exact successor restricted-proof
  assumption.  No target-code generation or final proof packaging remains
  in that premise.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedNumeralTermCode
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedPAProvability RawCodedPAOpenProofComposition
  RawCodedPAProofAllICertificates RawCodedPAProofAllNCertificates
  CompactPAUniformProvability.

Module PABoundedRawCodedRestrictedPAConsistencyOpenCompiler.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAOpenProofComposition.
Import PABoundedRawCodedPAProofAllICertificates.
Import PABoundedRawCodedPAProofAllNCertificates.
Import PABoundedCompactPAUniformProvability.

(** The formula assumed while refuting one candidate certificate.  Keeping
    this as a named raw-code operation prevents the open compiler interface
    from expanding the large represented restricted-proof predicate. *)
Definition rawRestrictedPAProofAssumptionCode (M : RawPAModel)
    (numeralCode : M) : M :=
  rawRestrictedTargetFormulaContextCode M numeralCode
    (restrictedTargetCodedRestrictedPAProofContext (tVar 0)).

Arguments rawRestrictedPAProofAssumptionCode M numeralCode
  : clear implicits.

(** Exact constructor view of the target selected from a numeral-term code.
    This holds equally for nonstandard [numeralCode] values: it is a statement
    about the transparent raw syntax constructor, not quotation adequacy. *)
Theorem raw_restrictedPAConsistencyTargetCode_view : forall
    (M : RawPAModel) numeralCode,
  rawRestrictedTargetFormulaContextCode M numeralCode
    restrictedPAConsistencyFormulaContext =
  rawRestrictedTargetCloseNFormulaCode M
    (restrictedTargetFormulaContextBound
      restrictedPAConsistencyBodyFormulaContext)
    (rawFormulaAllCode M
      (rawFormulaImpCode M
        (rawRestrictedPAProofAssumptionCode M numeralCode)
        (rawFormulaBotCode M))).
Proof.
  intros M numeralCode.
  unfold restrictedPAConsistencyFormulaContext,
    restrictedPAConsistencyBodyFormulaContext,
    rawRestrictedPAProofAssumptionCode.
  cbn [rawRestrictedTargetFormulaContextCode].
  reflexivity.
Qed.

(** Every target-graph witness therefore exposes the exact assumption which
    an open soundness proof must refute.  The numeral-code witness is retained
    because it is also the parameter used by that proof compiler. *)
Theorem raw_restrictedPAConsistencyFormulaCodeAt_open_view : forall
    (M : RawPAModel) level target,
  RawRestrictedPAConsistencyFormulaCodeAt M level target ->
  exists numeralCode,
    RawNumeralTermCodeAt M level numeralCode /\
    target =
      rawRestrictedTargetCloseNFormulaCode M
        (restrictedTargetFormulaContextBound
          restrictedPAConsistencyBodyFormulaContext)
        (rawFormulaAllCode M
          (rawFormulaImpCode M
            (rawRestrictedPAProofAssumptionCode M numeralCode)
            (rawFormulaBotCode M))).
Proof.
  intros M level target
    [numeralCode [hnumeral ->]].
  exists numeralCode. split.
  - exact hnumeral.
  - apply raw_restrictedPAConsistencyTargetCode_view.
Qed.

(** The genuine local proof-producing seam.

    Unlike [RawRestrictedPAConsistencyCertificateSuccessor], this predicate
    does not quantify over an opaque successor target and does not ask the
    caller to package implication introduction or universal introduction.
    Its output is only a covered derivation of falsity in the context

      RestrictedPAProof(succ(level), certificate) :: nil.

    The incoming lower target and its PA certificate remain available because
    the eventual truth/soundness construction must use them.  Any remaining
    truth reflection assumptions should be added behind this interface, not
    by weakening its conclusion back to the old successor statement. *)
Definition RawRestrictedPAConsistencyOpenContradictionCompiler
    (M : RawPAModel) : Prop :=
  forall level target certificate successorNumeralCode,
    RawRestrictedPAConsistencyFormulaCodeAt M level target ->
    RawCodedPAProofOf M target certificate ->
    RawNumeralTermCodeAt M (raw_succ M level) successorNumeralCode ->
    RawCodedPAOpenProvability M
      (raw_zero M) (raw_zero M)
      (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
      (rawFormulaBotCode M).

Arguments RawRestrictedPAConsistencyOpenContradictionCompiler M
  : clear implicits.

Definition RawRestrictedPAConsistencyOpenContradictionCompilerInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawRestrictedPAConsistencyOpenContradictionCompiler M.

(** Once the local open contradiction exists, the constructors already proved
    in [RawCodedPAProofAllICertificates] build the exact successor target.
    Target functionality is not needed: the target's own graph witness gives
    the numeral code and the constructor view above rewrites it directly. *)
Theorem raw_restrictedPAConsistencyCertificateSuccessor_of_openCompiler :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawRestrictedPAConsistencyOpenContradictionCompiler M ->
  RawRestrictedPAConsistencyCertificateSuccessor M.
Proof.
  intros M hPA hcompiler level target certificate nextTarget
    htarget hcertificate hnextTarget.
  destruct (raw_restrictedPAConsistencyFormulaCodeAt_open_view
    M (raw_succ M level) nextTarget hnextTarget)
    as [successorNumeralCode [hnumeral hnextTargetView]].
  destruct (hcompiler level target certificate successorNumeralCode
    htarget hcertificate hnumeral) as [child hopen].
  exists (rawProofSealedUniversalOpenNegationCertificate M
    (restrictedTargetFormulaContextBound
      restrictedPAConsistencyBodyFormulaContext)
    (rawRestrictedPAProofAssumptionCode M successorNumeralCode) child).
  rewrite hnextTargetView.
  exact (raw_codedPAProofOf_sealed_universal_negation_of_open_bottom M hPA
    (restrictedTargetFormulaContextBound
      restrictedPAConsistencyBodyFormulaContext)
    (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
    child hopen).
Qed.

Corollary
    raw_restrictedPAConsistencyCertificateSuccessorInAllModels_of_openCompiler
    : RawRestrictedPAConsistencyOpenContradictionCompilerInAllModels ->
  RawRestrictedPAConsistencyCertificateSuccessorInAllModels.
Proof.
  intros hcompiler M hPA.
  exact (raw_restrictedPAConsistencyCertificateSuccessor_of_openCompiler
    M hPA (hcompiler M hPA)).
Qed.

(** Fully connected conditional endpoint.  The remaining premise is the
    narrowly typed open contradiction compiler above; the formerly open
    arbitrary-target successor has been discharged. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_openCompiler
    : RawRestrictedPAConsistencyOpenContradictionCompilerInAllModels ->
  Formula.BProv Formula.Ax_s nil
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hcompiler.
  apply
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_certificate_successor.
  exact
    (raw_restrictedPAConsistencyCertificateSuccessorInAllModels_of_openCompiler
      hcompiler).
Qed.

End PABoundedRawCodedRestrictedPAConsistencyOpenCompiler.
