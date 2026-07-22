(**
  Honest local projections of all seven restricted-proof checker fields.

  After the three existential witnesses are opened, the head assumption is
  a right-associated conjunction of seven fields.  The roots below are the
  exact [RP_andE1]/[RP_andE2] chains selecting each field.  The construction
  retains one common arbitrary context and certifies coverage and endpoints
  for every projection; no semantic meaning of a field is assumed here.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedContextLists
  RawCodedProofAssumptionLeaf RawCodedProofAndEConstructors
  RawCodedPALocalProofExistential RawCodedPALocalProofConjunction
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPAConsistencyTripleExDescent.

Module PABoundedRawCodedRestrictedPAFieldProjections.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.

(** The unnamed conjunction tails, from five fields down to the final pair. *)
Definition rawRestrictedPAProofFieldsSuffix5Code (M : RawPAModel)
    (numeralCode : M) : M :=
  rawFormulaAndCode M
    (rawRestrictedPAOccurrenceBoundFieldCode M numeralCode)
    (rawFormulaAndCode M
      (rawRestrictedPAAtomicAdequacyFieldCode M)
      (rawFormulaAndCode M
        (rawRestrictedPAFormulaCoverageFieldCode M)
        (rawFormulaAndCode M
          (rawRestrictedPARuleCoverageFieldCode M)
          (rawRestrictedPABottomEndpointFieldCode M)))).

Definition rawRestrictedPAProofFieldsSuffix4Code (M : RawPAModel) : M :=
  rawFormulaAndCode M
    (rawRestrictedPAAtomicAdequacyFieldCode M)
    (rawFormulaAndCode M
      (rawRestrictedPAFormulaCoverageFieldCode M)
      (rawFormulaAndCode M
        (rawRestrictedPARuleCoverageFieldCode M)
        (rawRestrictedPABottomEndpointFieldCode M))).

Definition rawRestrictedPAProofFieldsSuffix3Code (M : RawPAModel) : M :=
  rawFormulaAndCode M
    (rawRestrictedPAFormulaCoverageFieldCode M)
    (rawFormulaAndCode M
      (rawRestrictedPARuleCoverageFieldCode M)
      (rawRestrictedPABottomEndpointFieldCode M)).

Definition rawRestrictedPAProofFieldsSuffix2Code (M : RawPAModel) : M :=
  rawFormulaAndCode M
    (rawRestrictedPARuleCoverageFieldCode M)
    (rawRestrictedPABottomEndpointFieldCode M).

Arguments rawRestrictedPAProofFieldsSuffix5Code M numeralCode
  : clear implicits.

Lemma raw_restrictedPAProofFieldsSuffix6Code_view : forall
    (M : RawPAModel) numeralCode,
  rawRestrictedPAProofFieldsSuffix6Code M numeralCode =
  rawFormulaAndCode M
    (rawRestrictedPAAxiomContextFieldCode M)
    (rawRestrictedPAProofFieldsSuffix5Code M numeralCode).
Proof. reflexivity. Qed.

Lemma raw_restrictedPAProofFieldsSuffix5Code_view : forall
    (M : RawPAModel) numeralCode,
  rawRestrictedPAProofFieldsSuffix5Code M numeralCode =
  rawFormulaAndCode M
    (rawRestrictedPAOccurrenceBoundFieldCode M numeralCode)
    (rawRestrictedPAProofFieldsSuffix4Code M).
Proof. reflexivity. Qed.

Lemma raw_restrictedPAProofFieldsSuffix4Code_view : forall
    (M : RawPAModel),
  rawRestrictedPAProofFieldsSuffix4Code M =
  rawFormulaAndCode M
    (rawRestrictedPAAtomicAdequacyFieldCode M)
    (rawRestrictedPAProofFieldsSuffix3Code M).
Proof. reflexivity. Qed.

Lemma raw_restrictedPAProofFieldsSuffix3Code_view : forall
    (M : RawPAModel),
  rawRestrictedPAProofFieldsSuffix3Code M =
  rawFormulaAndCode M
    (rawRestrictedPAFormulaCoverageFieldCode M)
    (rawRestrictedPAProofFieldsSuffix2Code M).
Proof. reflexivity. Qed.

(** Exact roots for the assumption and its six successive right tails. *)
Definition rawRestrictedPAFieldsAssumptionRoot (M : RawPAModel)
    (numeralCode tailContext : M) : M :=
  rawProofAssumptionRoot M
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawRestrictedPAProofFieldsCode M numeralCode).

Definition rawRestrictedPACertificateTupleProjectionRoot (M : RawPAModel)
    (numeralCode tailContext : M) : M :=
  rawProofAndERoot M RawAndLeft
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawRestrictedPACertificateTupleFieldCode M)
    (rawRestrictedPAProofFieldsSuffix6Code M numeralCode)
    (rawRestrictedPAFieldsAssumptionRoot M numeralCode tailContext).

Definition rawRestrictedPASuffix6ProjectionRoot (M : RawPAModel)
    (numeralCode tailContext : M) : M :=
  rawProofAndERoot M RawAndRight
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawRestrictedPACertificateTupleFieldCode M)
    (rawRestrictedPAProofFieldsSuffix6Code M numeralCode)
    (rawRestrictedPAFieldsAssumptionRoot M numeralCode tailContext).

Definition rawRestrictedPAAxiomContextProjectionRoot (M : RawPAModel)
    (numeralCode tailContext : M) : M :=
  rawProofAndERoot M RawAndLeft
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawRestrictedPAAxiomContextFieldCode M)
    (rawRestrictedPAProofFieldsSuffix5Code M numeralCode)
    (rawRestrictedPASuffix6ProjectionRoot M numeralCode tailContext).

Definition rawRestrictedPASuffix5ProjectionRoot (M : RawPAModel)
    (numeralCode tailContext : M) : M :=
  rawProofAndERoot M RawAndRight
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawRestrictedPAAxiomContextFieldCode M)
    (rawRestrictedPAProofFieldsSuffix5Code M numeralCode)
    (rawRestrictedPASuffix6ProjectionRoot M numeralCode tailContext).

Definition rawRestrictedPAOccurrenceBoundProjectionRoot (M : RawPAModel)
    (numeralCode tailContext : M) : M :=
  rawProofAndERoot M RawAndLeft
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawRestrictedPAOccurrenceBoundFieldCode M numeralCode)
    (rawRestrictedPAProofFieldsSuffix4Code M)
    (rawRestrictedPASuffix5ProjectionRoot M numeralCode tailContext).

Definition rawRestrictedPASuffix4ProjectionRoot (M : RawPAModel)
    (numeralCode tailContext : M) : M :=
  rawProofAndERoot M RawAndRight
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawRestrictedPAOccurrenceBoundFieldCode M numeralCode)
    (rawRestrictedPAProofFieldsSuffix4Code M)
    (rawRestrictedPASuffix5ProjectionRoot M numeralCode tailContext).

Definition rawRestrictedPAAtomicAdequacyProjectionRoot (M : RawPAModel)
    (numeralCode tailContext : M) : M :=
  rawProofAndERoot M RawAndLeft
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawRestrictedPAAtomicAdequacyFieldCode M)
    (rawRestrictedPAProofFieldsSuffix3Code M)
    (rawRestrictedPASuffix4ProjectionRoot M numeralCode tailContext).

Definition rawRestrictedPASuffix3ProjectionRoot (M : RawPAModel)
    (numeralCode tailContext : M) : M :=
  rawProofAndERoot M RawAndRight
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawRestrictedPAAtomicAdequacyFieldCode M)
    (rawRestrictedPAProofFieldsSuffix3Code M)
    (rawRestrictedPASuffix4ProjectionRoot M numeralCode tailContext).

Definition rawRestrictedPAFormulaCoverageProjectionRoot (M : RawPAModel)
    (numeralCode tailContext : M) : M :=
  rawProofAndERoot M RawAndLeft
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawRestrictedPAFormulaCoverageFieldCode M)
    (rawRestrictedPAProofFieldsSuffix2Code M)
    (rawRestrictedPASuffix3ProjectionRoot M numeralCode tailContext).

Definition rawRestrictedPASuffix2ProjectionRoot (M : RawPAModel)
    (numeralCode tailContext : M) : M :=
  rawProofAndERoot M RawAndRight
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawRestrictedPAFormulaCoverageFieldCode M)
    (rawRestrictedPAProofFieldsSuffix2Code M)
    (rawRestrictedPASuffix3ProjectionRoot M numeralCode tailContext).

Definition rawRestrictedPARuleCoverageProjectionRoot (M : RawPAModel)
    (numeralCode tailContext : M) : M :=
  rawProofAndERoot M RawAndLeft
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawRestrictedPARuleCoverageFieldCode M)
    (rawRestrictedPABottomEndpointFieldCode M)
    (rawRestrictedPASuffix2ProjectionRoot M numeralCode tailContext).

Definition rawRestrictedPABottomEndpointProjectionRoot (M : RawPAModel)
    (numeralCode tailContext : M) : M :=
  rawProofAndERoot M RawAndRight
    (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
    (rawRestrictedPARuleCoverageFieldCode M)
    (rawRestrictedPABottomEndpointFieldCode M)
    (rawRestrictedPASuffix2ProjectionRoot M numeralCode tailContext).

(** The seven proofs are bundled so the semantic compiler can consume them
    without repeating or trusting a conjunction decomposition. *)
Record RawRestrictedPAFieldProjectionPackage (M : RawPAModel)
    (numeralCode tailContext : M) : Prop := {
  rawRestrictedPACertificateTupleProjection :
    RawCodedPALocalProofOf M
      (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
      (rawRestrictedPACertificateTupleFieldCode M)
      (rawRestrictedPACertificateTupleProjectionRoot
        M numeralCode tailContext);
  rawRestrictedPAAxiomContextProjection :
    RawCodedPALocalProofOf M
      (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
      (rawRestrictedPAAxiomContextFieldCode M)
      (rawRestrictedPAAxiomContextProjectionRoot M numeralCode tailContext);
  rawRestrictedPAOccurrenceBoundProjection :
    RawCodedPALocalProofOf M
      (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
      (rawRestrictedPAOccurrenceBoundFieldCode M numeralCode)
      (rawRestrictedPAOccurrenceBoundProjectionRoot
        M numeralCode tailContext);
  rawRestrictedPAAtomicAdequacyProjection :
    RawCodedPALocalProofOf M
      (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
      (rawRestrictedPAAtomicAdequacyFieldCode M)
      (rawRestrictedPAAtomicAdequacyProjectionRoot M numeralCode tailContext);
  rawRestrictedPAFormulaCoverageProjection :
    RawCodedPALocalProofOf M
      (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
      (rawRestrictedPAFormulaCoverageFieldCode M)
      (rawRestrictedPAFormulaCoverageProjectionRoot M numeralCode tailContext);
  rawRestrictedPARuleCoverageProjection :
    RawCodedPALocalProofOf M
      (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
      (rawRestrictedPARuleCoverageFieldCode M)
      (rawRestrictedPARuleCoverageProjectionRoot M numeralCode tailContext);
  rawRestrictedPABottomEndpointProjection :
    RawCodedPALocalProofOf M
      (rawRestrictedPAFieldsContextCode M numeralCode tailContext)
      (rawRestrictedPABottomEndpointFieldCode M)
      (rawRestrictedPABottomEndpointProjectionRoot M numeralCode tailContext)
}.

Arguments RawRestrictedPAFieldProjectionPackage
  M numeralCode tailContext : clear implicits.

Theorem raw_restrictedPAFieldProjectionPackage : forall
    (M : RawPAModel), RawPASatisfies M -> forall numeralCode tailContext,
  RawContextListRealizable M tailContext ->
  RawRestrictedPAFieldProjectionPackage M numeralCode tailContext.
Proof.
  intros M hPA numeralCode tailContext htail.
  set (context := rawRestrictedPAFieldsContextCode
    M numeralCode tailContext).
  assert (hfields : RawCodedPALocalProofOf M context
      (rawRestrictedPAProofFieldsCode M numeralCode)
      (rawRestrictedPAFieldsAssumptionRoot M numeralCode tailContext)).
  {
    unfold context, rawRestrictedPAFieldsAssumptionRoot,
      rawRestrictedPAFieldsContextCode.
    apply (raw_codedPALocalProofOf_assumption M hPA). exact htail.
  }
  assert (hcertificate : RawCodedPALocalProofOf M context
      (rawRestrictedPACertificateTupleFieldCode M)
      (rawRestrictedPACertificateTupleProjectionRoot
        M numeralCode tailContext)).
  {
    unfold rawRestrictedPAProofFieldsCode,
      rawRestrictedPACertificateTupleProjectionRoot.
    exact (raw_codedPALocalProofOf_andE1 M hPA context
      (rawRestrictedPACertificateTupleFieldCode M)
      (rawRestrictedPAProofFieldsSuffix6Code M numeralCode)
      (rawRestrictedPAFieldsAssumptionRoot M numeralCode tailContext)
      hfields).
  }
  assert (hsuffix6 : RawCodedPALocalProofOf M context
      (rawRestrictedPAProofFieldsSuffix6Code M numeralCode)
      (rawRestrictedPASuffix6ProjectionRoot M numeralCode tailContext)).
  {
    unfold rawRestrictedPAProofFieldsCode,
      rawRestrictedPASuffix6ProjectionRoot.
    exact (raw_codedPALocalProofOf_andE2 M hPA context
      (rawRestrictedPACertificateTupleFieldCode M)
      (rawRestrictedPAProofFieldsSuffix6Code M numeralCode)
      (rawRestrictedPAFieldsAssumptionRoot M numeralCode tailContext)
      hfields).
  }
  rewrite raw_restrictedPAProofFieldsSuffix6Code_view in hsuffix6.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context
    (rawRestrictedPAAxiomContextFieldCode M)
    (rawRestrictedPAProofFieldsSuffix5Code M numeralCode)
    (rawRestrictedPASuffix6ProjectionRoot M numeralCode tailContext)
    hsuffix6) as haxiom.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    (rawRestrictedPAAxiomContextFieldCode M)
    (rawRestrictedPAProofFieldsSuffix5Code M numeralCode)
    (rawRestrictedPASuffix6ProjectionRoot M numeralCode tailContext)
    hsuffix6) as hsuffix5.
  rewrite raw_restrictedPAProofFieldsSuffix5Code_view in hsuffix5.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context
    (rawRestrictedPAOccurrenceBoundFieldCode M numeralCode)
    (rawRestrictedPAProofFieldsSuffix4Code M)
    (rawRestrictedPASuffix5ProjectionRoot M numeralCode tailContext)
    hsuffix5) as hoccurrence.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    (rawRestrictedPAOccurrenceBoundFieldCode M numeralCode)
    (rawRestrictedPAProofFieldsSuffix4Code M)
    (rawRestrictedPASuffix5ProjectionRoot M numeralCode tailContext)
    hsuffix5) as hsuffix4.
  rewrite raw_restrictedPAProofFieldsSuffix4Code_view in hsuffix4.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context
    (rawRestrictedPAAtomicAdequacyFieldCode M)
    (rawRestrictedPAProofFieldsSuffix3Code M)
    (rawRestrictedPASuffix4ProjectionRoot M numeralCode tailContext)
    hsuffix4) as hatomic.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    (rawRestrictedPAAtomicAdequacyFieldCode M)
    (rawRestrictedPAProofFieldsSuffix3Code M)
    (rawRestrictedPASuffix4ProjectionRoot M numeralCode tailContext)
    hsuffix4) as hsuffix3.
  rewrite raw_restrictedPAProofFieldsSuffix3Code_view in hsuffix3.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context
    (rawRestrictedPAFormulaCoverageFieldCode M)
    (rawRestrictedPAProofFieldsSuffix2Code M)
    (rawRestrictedPASuffix3ProjectionRoot M numeralCode tailContext)
    hsuffix3) as hformula.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    (rawRestrictedPAFormulaCoverageFieldCode M)
    (rawRestrictedPAProofFieldsSuffix2Code M)
    (rawRestrictedPASuffix3ProjectionRoot M numeralCode tailContext)
    hsuffix3) as hsuffix2.
  unfold rawRestrictedPAProofFieldsSuffix2Code in hsuffix2.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context
    (rawRestrictedPARuleCoverageFieldCode M)
    (rawRestrictedPABottomEndpointFieldCode M)
    (rawRestrictedPASuffix2ProjectionRoot M numeralCode tailContext)
    hsuffix2) as hrule.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    (rawRestrictedPARuleCoverageFieldCode M)
    (rawRestrictedPABottomEndpointFieldCode M)
    (rawRestrictedPASuffix2ProjectionRoot M numeralCode tailContext)
    hsuffix2) as hbottom.
  unfold context in *.
  constructor; assumption.
Qed.

End PABoundedRawCodedRestrictedPAFieldProjections.
