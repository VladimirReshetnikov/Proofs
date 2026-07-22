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
  RawCodedContextShift RawCodedRestrictedPAProof
  RawCodedProofEndpoints RawCodedProofRuleCoverage
  RawCodedPAProvability RawCodedPAOpenProofComposition
  RawCodedPAProofAllNCarriedCertificates
  CompactPAUniformProvability.

Module PABoundedRawCodedRestrictedPAConsistencyOpenCompiler.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAOpenProofComposition.
Import PABoundedRawCodedPAProofAllNCarriedCertificates.
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

(** Concrete elimination of the existential fields hidden by an ordinary
    proof certificate.  This small theorem is intentionally public: later
    compiler stages must retain these exact fields instead of silently
    replacing the generally nonempty witnessed PA context by [nil]. *)
Theorem raw_codedPAProofOf_unpack_components : forall
    (M : RawPAModel) target certificate,
  RawCodedPAProofOf M target certificate ->
  exists witnessList proof baseContext : M,
    certificate = rawCodeList3 M
      (rawNumeralValue M 0) witnessList proof /\
    RawCodedPAAxiomWitnessContext M witnessList baseContext /\
    RawProofRuleCoverage M proof /\
    RawProofEndpoint M proof baseContext target.
Proof.
  intros M target certificate hcertificate.
  exact hcertificate.
Qed.

(** Carried output of the local contradiction compiler.  The first four
    fields are exactly the unpacked incoming certificate; the open proof
    keeps its witnessed list and base context.  [RawContextShift base base]
    is the honest side condition needed to quantify and seal the resulting
    implication without erasing that context. *)
Definition RawCodedPACarriedOpenContradictionFrom
    (M : RawPAModel) (target certificate assumption : M) : Prop :=
  exists witnessList proof baseContext child : M,
    certificate = rawCodeList3 M
      (rawNumeralValue M 0) witnessList proof /\
    RawCodedPAAxiomWitnessContext M witnessList baseContext /\
    RawProofRuleCoverage M proof /\
    RawProofEndpoint M proof baseContext target /\
    RawContextShift M baseContext baseContext /\
    RawCodedPAOpenProofOf M witnessList baseContext assumption
      (rawFormulaBotCode M) child.

Arguments RawCodedPACarriedOpenContradictionFrom
  M target certificate assumption : clear implicits.

(** The genuine local proof-producing seam.

    Unlike [RawRestrictedPAConsistencyCertificateSuccessor], this predicate
    does not quantify over an opaque successor target and does not ask the
    caller to package implication introduction or universal introduction.
    Its output is only a covered derivation of falsity in the context

      RestrictedPAProof(succ(level), certificate) :: baseContext,

    where [baseContext] and its witness list are the exact fields hidden in
    the incoming lower certificate.  This avoids a nonexistent generic
    weakening operation on proof trees whose every node stores its context.
    Any remaining truth-reflection work belongs behind this interface. *)
Definition RawRestrictedPAConsistencyOpenContradictionCompiler
    (M : RawPAModel) : Prop :=
  forall level target certificate successorNumeralCode,
    RawRestrictedPAConsistencyFormulaCodeAt M level target ->
    RawCodedPAProofOf M target certificate ->
    RawNumeralTermCodeAt M (raw_succ M level) successorNumeralCode ->
    RawCodedPACarriedOpenContradictionFrom M target certificate
      (rawRestrictedPAProofAssumptionCode M successorNumeralCode).

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
    htarget hcertificate hnumeral) as
    (witnessList & lowerProof & baseContext & child &
      hcertificateView & hwitness & hlowerCoverage & hlowerEndpoint &
      hbaseShift & hopen).
  exists (rawProofSealedUniversalOpenNegationCarriedCertificate M
    witnessList baseContext
    (restrictedTargetFormulaContextBound
      restrictedPAConsistencyBodyFormulaContext)
    (rawRestrictedPAProofAssumptionCode M successorNumeralCode) child).
  rewrite hnextTargetView.
  exact
    (raw_codedPAProofOf_sealed_universal_negation_of_carried_open_bottom
    M hPA witnessList baseContext
    (restrictedTargetFormulaContextBound
      restrictedPAConsistencyBodyFormulaContext)
    (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
    child hbaseShift hopen).
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
