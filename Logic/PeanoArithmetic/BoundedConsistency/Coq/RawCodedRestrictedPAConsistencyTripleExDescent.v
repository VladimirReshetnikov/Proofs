(**
  Triple existential descent for the restricted-proof assumption.

  The named assumption has shape

      exists witnessList, exists proof, exists context, fields7.

  Three applications of the exact [RP_exE] constructor reduce an open proof
  of falsity to a local falsity proof in the context whose head is [fields7].
  Each intermediate context is the pointwise shift required by natural
  deduction.  These shifts are retained as explicit certificate data: this
  module performs no illicit syntactic decoding of a nonstandard formula.

  The witnessed PA-axiom base of the incoming lower certificate is retained
  as the tail of every context.  The remaining field-level seam must expose
  those exact certificate fields, certify that the base is stable under
  binder shift, and provide a covered proof of falsity from the seven-field
  conjunction.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedNumeralTermCode
  RawCodedContextLists RawCodedContextShift
  RawCodedRestrictedPAProof RawCodedProofEndpoints
  RawCodedProofRuleCoverage
  RawCodedProofAssumptionLeaf RawCodedProofExEConstructor
  RawCodedPAProvability
  RawCodedPAOpenProofComposition RawCodedPALocalProofExistential
  RawCodedRestrictedPAConsistencyFormulaCode
  CompactPAUniformProvability
  RawCodedRestrictedPAConsistencyOpenCompiler
  RawCodedRestrictedPAConsistencyOpenDescent.

Module PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofExEConstructor.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAOpenProofComposition.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedRestrictedPAConsistencyOpenCompiler.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.

Definition rawRestrictedPAOpenRootContextCode (M : RawPAModel)
    (numeralCode baseContext : M) : M :=
  rawListNode M
    (rawRestrictedPAProofAssumptionCode M numeralCode) baseContext.

Definition rawRestrictedPAAfterWitnessContextCode (M : RawPAModel)
    (numeralCode shiftedRootContext : M) : M :=
  rawListNode M
    (rawRestrictedPAProofAfterWitnessCode M numeralCode)
    shiftedRootContext.

Definition rawRestrictedPAAfterProofContextCode (M : RawPAModel)
    (numeralCode shiftedWitnessContext : M) : M :=
  rawListNode M
    (rawRestrictedPAProofAfterProofCode M numeralCode)
    shiftedWitnessContext.

Definition rawRestrictedPAFieldsContextCode (M : RawPAModel)
    (numeralCode shiftedProofContext : M) : M :=
  rawListNode M
    (rawRestrictedPAProofFieldsCode M numeralCode)
    shiftedProofContext.

Arguments rawRestrictedPAOpenRootContextCode M numeralCode baseContext
  : clear implicits.
Arguments rawRestrictedPAAfterWitnessContextCode
  M numeralCode shiftedRootContext : clear implicits.
Arguments rawRestrictedPAAfterProofContextCode
  M numeralCode shiftedWitnessContext : clear implicits.
Arguments rawRestrictedPAFieldsContextCode
  M numeralCode shiftedProofContext : clear implicits.

(** The three binder shifts, stated against the exact contexts to which each
    successive [RP_exE] is applied. *)
Definition RawRestrictedPAExistentialDescentContexts (M : RawPAModel)
    (numeralCode baseContext shiftedRootContext shiftedWitnessContext
      shiftedProofContext : M) : Prop :=
  RawContextShift M
    (rawRestrictedPAOpenRootContextCode M numeralCode baseContext)
    shiftedRootContext /\
  RawContextShift M
    (rawRestrictedPAAfterWitnessContextCode M
      numeralCode shiftedRootContext)
    shiftedWitnessContext /\
  RawContextShift M
    (rawRestrictedPAAfterProofContextCode M
      numeralCode shiftedWitnessContext)
    shiftedProofContext.

Arguments RawRestrictedPAExistentialDescentContexts
  M numeralCode baseContext shiftedRootContext shiftedWitnessContext
    shiftedProofContext : clear implicits.

(** Explicit proof roots, from the innermost elimination outward. *)
Definition rawRestrictedPAThirdExERoot (M : RawPAModel)
    (numeralCode shiftedWitnessContext shiftedProofContext fieldChild : M)
    : M :=
  rawProofExERoot M
    (rawRestrictedPAAfterProofContextCode M
      numeralCode shiftedWitnessContext)
    (rawRestrictedPAProofFieldsCode M numeralCode)
    (rawFormulaBotCode M)
    (rawProofAssumptionRoot M
      (rawRestrictedPAAfterProofContextCode M
        numeralCode shiftedWitnessContext)
      (rawRestrictedPAProofAfterProofCode M numeralCode))
    fieldChild.

Definition rawRestrictedPASecondExERoot (M : RawPAModel)
    (numeralCode shiftedRootContext shiftedWitnessContext
      shiftedProofContext fieldChild : M) : M :=
  rawProofExERoot M
    (rawRestrictedPAAfterWitnessContextCode M
      numeralCode shiftedRootContext)
    (rawRestrictedPAProofAfterProofCode M numeralCode)
    (rawFormulaBotCode M)
    (rawProofAssumptionRoot M
      (rawRestrictedPAAfterWitnessContextCode M
        numeralCode shiftedRootContext)
      (rawRestrictedPAProofAfterWitnessCode M numeralCode))
    (rawRestrictedPAThirdExERoot M
      numeralCode shiftedWitnessContext shiftedProofContext fieldChild).

Definition rawRestrictedPATripleExERoot (M : RawPAModel)
    (numeralCode baseContext shiftedRootContext shiftedWitnessContext
      shiftedProofContext fieldChild : M) : M :=
  rawProofExERoot M
    (rawRestrictedPAOpenRootContextCode M numeralCode baseContext)
    (rawRestrictedPAProofAfterWitnessCode M numeralCode)
    (rawFormulaBotCode M)
    (rawProofAssumptionRoot M
      (rawRestrictedPAOpenRootContextCode M numeralCode baseContext)
      (rawRestrictedPAProofAssumptionCode M numeralCode))
    (rawRestrictedPASecondExERoot M
      numeralCode shiftedRootContext shiftedWitnessContext
      shiftedProofContext fieldChild).

Arguments rawRestrictedPAThirdExERoot
  M numeralCode shiftedWitnessContext shiftedProofContext fieldChild
  : clear implicits.
Arguments rawRestrictedPASecondExERoot
  M numeralCode shiftedRootContext shiftedWitnessContext
    shiftedProofContext fieldChild : clear implicits.
Arguments rawRestrictedPATripleExERoot
  M numeralCode baseContext shiftedRootContext shiftedWitnessContext
    shiftedProofContext fieldChild : clear implicits.

Theorem raw_codedPAOpenProofOf_bottom_of_restrictedPA_fields : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext numeralCode
      shiftedRootContext shiftedWitnessContext
      shiftedProofContext fieldChild,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawRestrictedPAExistentialDescentContexts M numeralCode baseContext
    shiftedRootContext shiftedWitnessContext shiftedProofContext ->
  RawCodedPALocalProofOf M
    (rawRestrictedPAFieldsContextCode M
      numeralCode shiftedProofContext)
    (rawFormulaBotCode M) fieldChild ->
  RawCodedPAOpenProofOf M witnessList baseContext
    (rawRestrictedPAProofAssumptionCode M numeralCode)
    (rawFormulaBotCode M)
    (rawRestrictedPATripleExERoot M numeralCode baseContext
      shiftedRootContext shiftedWitnessContext
      shiftedProofContext fieldChild).
Proof.
  intros M hPA witnessList baseContext numeralCode
    shiftedRootContext shiftedWitnessContext shiftedProofContext fieldChild
    hwitness [hrootShift [hwitnessShift hproofShift]] hfield.
  assert (hproofTailRealizable :
      RawContextListRealizable M shiftedWitnessContext).
  {
    exact (raw_contextShift_target_realizable M
      (rawRestrictedPAAfterWitnessContextCode M
        numeralCode shiftedRootContext)
      shiftedWitnessContext hwitnessShift).
  }
  assert (hproofAssumption :
      RawCodedPALocalProofOf M
        (rawRestrictedPAAfterProofContextCode M
          numeralCode shiftedWitnessContext)
        (rawRestrictedPAProofAfterProofCode M numeralCode)
        (rawProofAssumptionRoot M
          (rawRestrictedPAAfterProofContextCode M
            numeralCode shiftedWitnessContext)
          (rawRestrictedPAProofAfterProofCode M numeralCode))).
  {
    exact (raw_codedPALocalProofOf_assumption M hPA
      shiftedWitnessContext
      (rawRestrictedPAProofAfterProofCode M numeralCode)
      hproofTailRealizable).
  }
  assert (hthird :
      RawCodedPALocalProofOf M
        (rawRestrictedPAAfterProofContextCode M
          numeralCode shiftedWitnessContext)
        (rawFormulaBotCode M)
        (rawRestrictedPAThirdExERoot M numeralCode
          shiftedWitnessContext shiftedProofContext fieldChild)).
  {
    unfold rawRestrictedPAThirdExERoot.
    apply (raw_codedPALocalProofOf_exE_bottom M hPA
      (rawRestrictedPAAfterProofContextCode M
        numeralCode shiftedWitnessContext)
      shiftedProofContext
      (rawRestrictedPAProofFieldsCode M numeralCode)).
    - exact hproofAssumption.
    - exact hproofShift.
    - exact hfield.
  }
  assert (hwitnessTailRealizable :
      RawContextListRealizable M shiftedRootContext).
  {
    exact (raw_contextShift_target_realizable M
      (rawRestrictedPAOpenRootContextCode M numeralCode baseContext)
      shiftedRootContext hrootShift).
  }
  assert (hwitnessAssumption :
      RawCodedPALocalProofOf M
        (rawRestrictedPAAfterWitnessContextCode M
          numeralCode shiftedRootContext)
        (rawRestrictedPAProofAfterWitnessCode M numeralCode)
        (rawProofAssumptionRoot M
          (rawRestrictedPAAfterWitnessContextCode M
            numeralCode shiftedRootContext)
          (rawRestrictedPAProofAfterWitnessCode M numeralCode))).
  {
    exact (raw_codedPALocalProofOf_assumption M hPA
      shiftedRootContext
      (rawRestrictedPAProofAfterWitnessCode M numeralCode)
      hwitnessTailRealizable).
  }
  assert (hsecond :
      RawCodedPALocalProofOf M
        (rawRestrictedPAAfterWitnessContextCode M
          numeralCode shiftedRootContext)
        (rawFormulaBotCode M)
        (rawRestrictedPASecondExERoot M numeralCode
          shiftedRootContext shiftedWitnessContext
          shiftedProofContext fieldChild)).
  {
    unfold rawRestrictedPASecondExERoot.
    apply (raw_codedPALocalProofOf_exE_bottom M hPA
      (rawRestrictedPAAfterWitnessContextCode M
        numeralCode shiftedRootContext)
      shiftedWitnessContext
      (rawRestrictedPAProofAfterProofCode M numeralCode)).
    - exact hwitnessAssumption.
    - exact hwitnessShift.
    - exact hthird.
  }
  assert (houterAssumption :
      RawCodedPAOpenProofOf M
        witnessList baseContext
        (rawRestrictedPAProofAssumptionCode M numeralCode)
        (rawFormulaExCode M
          (rawRestrictedPAProofAfterWitnessCode M numeralCode))
        (rawProofAssumptionRoot M
          (rawRestrictedPAOpenRootContextCode M numeralCode baseContext)
          (rawRestrictedPAProofAssumptionCode M numeralCode))).
  {
    rewrite <- raw_restrictedPAProofAssumptionCode_view.
    exact (raw_codedPAOpenProofOf_restrictedPAProof_assumption
      M hPA numeralCode witnessList baseContext hwitness).
  }
  unfold rawRestrictedPATripleExERoot.
  exact (raw_codedPAOpenProofOf_exE_bottom M hPA
    witnessList baseContext
    (rawRestrictedPAProofAssumptionCode M numeralCode)
    shiftedRootContext
    (rawRestrictedPAProofAfterWitnessCode M numeralCode)
    (rawProofAssumptionRoot M
      (rawRestrictedPAOpenRootContextCode M numeralCode baseContext)
      (rawRestrictedPAProofAssumptionCode M numeralCode))
    (rawRestrictedPASecondExERoot M numeralCode
      shiftedRootContext shiftedWitnessContext
      shiftedProofContext fieldChild)
    houterAssumption hrootShift hsecond).
Qed.

(** Exact remaining field-level compiler.  Compared with the previous open
    contradiction seam, its proof output starts after all three existential
    witnesses have been exposed, in the explicitly named field context. *)
Definition RawRestrictedPAConsistencyFieldRefutationCompiler
    (M : RawPAModel) : Prop :=
  forall level target certificate successorNumeralCode,
    RawRestrictedPAConsistencyFormulaCodeAt M level target ->
    RawCodedPAProofOf M target certificate ->
    RawNumeralTermCodeAt M (raw_succ M level) successorNumeralCode ->
    exists witnessList lowerProof baseContext
      shiftedRootContext shiftedWitnessContext shiftedProofContext
      fieldChild : M,
      certificate = rawCodeList3 M
        (rawNumeralValue M 0) witnessList lowerProof /\
      RawCodedPAAxiomWitnessContext M witnessList baseContext /\
      RawProofRuleCoverage M lowerProof /\
      RawProofEndpoint M lowerProof baseContext target /\
      RawContextShift M baseContext baseContext /\
      RawRestrictedPAExistentialDescentContexts M successorNumeralCode
        baseContext shiftedRootContext shiftedWitnessContext
        shiftedProofContext /\
      RawCodedPALocalProofOf M
        (rawRestrictedPAFieldsContextCode M
          successorNumeralCode shiftedProofContext)
        (rawFormulaBotCode M) fieldChild.

Arguments RawRestrictedPAConsistencyFieldRefutationCompiler M
  : clear implicits.

Definition RawRestrictedPAConsistencyFieldRefutationCompilerInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawRestrictedPAConsistencyFieldRefutationCompiler M.

Theorem raw_restrictedPAConsistencyOpenCompiler_of_fieldRefutation : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawRestrictedPAConsistencyFieldRefutationCompiler M ->
  RawRestrictedPAConsistencyOpenContradictionCompiler M.
Proof.
  intros M hPA hfield level target certificate successorNumeralCode
    htarget hcertificate hnumeral.
  destruct (hfield level target certificate successorNumeralCode
    htarget hcertificate hnumeral) as
    (witnessList & lowerProof & baseContext & shiftedRootContext &
      shiftedWitnessContext & shiftedProofContext & fieldChild &
      hcertificateView & hwitness & hlowerCoverage & hlowerEndpoint &
      hbaseShift & hcontexts & hfieldChild).
  exists witnessList, lowerProof, baseContext,
    (rawRestrictedPATripleExERoot M successorNumeralCode baseContext
      shiftedRootContext shiftedWitnessContext shiftedProofContext
      fieldChild).
  split; [exact hcertificateView |].
  split; [exact hwitness |].
  split; [exact hlowerCoverage |].
  split; [exact hlowerEndpoint |].
  split; [exact hbaseShift |].
  exact (raw_codedPAOpenProofOf_bottom_of_restrictedPA_fields M hPA
    witnessList baseContext successorNumeralCode
    shiftedRootContext shiftedWitnessContext shiftedProofContext
    fieldChild hwitness hcontexts hfieldChild).
Qed.

Corollary
    raw_restrictedPAConsistencyOpenCompilerInAllModels_of_fieldRefutation
    : RawRestrictedPAConsistencyFieldRefutationCompilerInAllModels ->
  RawRestrictedPAConsistencyOpenContradictionCompilerInAllModels.
Proof.
  intros hfield M hPA.
  exact (raw_restrictedPAConsistencyOpenCompiler_of_fieldRefutation
    M hPA (hfield M hPA)).
Qed.

Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_fieldRefutation
    : RawRestrictedPAConsistencyFieldRefutationCompilerInAllModels ->
  Formula.BProv Formula.Ax_s nil
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hfield.
  apply
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_openCompiler.
  exact
    (raw_restrictedPAConsistencyOpenCompilerInAllModels_of_fieldRefutation
      hfield).
Qed.

End PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
