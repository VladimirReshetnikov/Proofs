(**
  Concrete syntax at the entrance to the open restricted-proof refutation.

  The successor target assumes one formula whose raw code was named in
  [RawCodedRestrictedPAConsistencyOpenCompiler].  This file exposes that code
  as three existential binders followed by the seven exact checker fields.
  It also constructs the genuine assumption leaf at the start of the local
  derivation.  Thus the next compiler can concentrate on existential descent
  and field-level soundness rather than treating the large assumption as an
  opaque formula code.
*)

From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedRestrictedPAProof
  RawCodedFormulaOperations
  RawCodedProofAtomicAdequacy RawCodedProofRuleCoverage RawCodedProofRules
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedProofAssumptionLeaf RawCodedPAProofLeafCertificates
  RawCodedPAOpenProofComposition
  RawCodedRestrictedPAConsistencyOpenCompiler.

Module PABoundedRawCodedRestrictedPAConsistencyOpenDescent.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedPAProofLeafCertificates.
Import PABoundedRawCodedPAOpenProofComposition.
Import PABoundedRawCodedRestrictedPAConsistencyOpenCompiler.

(** Raw codes of the seven right-associated conjunction fields in
    [codedRestrictedPAProofTermAt].  The three existential binders have
    already been entered, so witness list, proof root, and proof context are
    respectively variables 2, 1, and 0. *)
Definition rawRestrictedPACertificateTupleFieldCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    (codeList3TermAt (liftTerm 3 (tVar 0))
      (Term.numeral 0) (tVar 2) (tVar 1)).

Definition rawRestrictedPAAxiomContextFieldCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    (codedPAAxiomWitnessContextTermAt (tVar 2) (tVar 0)).

Definition rawRestrictedPAOccurrenceBoundFieldCode (M : RawPAModel)
    (numeralCode : M) : M :=
  rawRestrictedTargetFormulaContextCode M numeralCode
    (restrictedTargetProofContext (tVar 1)).

Definition rawRestrictedPAAtomicAdequacyFieldCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    (proofAtomicallyAdequateTermAt (tVar 1)).

Definition rawRestrictedPAFormulaCoverageFieldCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    (proofHasFormulaCoverageTermAt (tVar 1)).

Definition rawRestrictedPARuleCoverageFieldCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    (proofRuleCoverageTermAt (tVar 1)).

Definition rawRestrictedPABottomEndpointFieldCode (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    (proofRuleValidTermAt
      (tVar 1) (tVar 0) rawFormulaBotCodeTerm).

(** The checker uses [restrictedPAAnd7], hence this exact right-associated
    shape.  Naming each suffix is useful when successive [RP_andE2] nodes
    peel the record from left to right. *)
Definition rawRestrictedPAProofFieldsSuffix6Code (M : RawPAModel)
    (numeralCode : M) : M :=
  rawFormulaAndCode M
    (rawRestrictedPAAxiomContextFieldCode M)
    (rawFormulaAndCode M
      (rawRestrictedPAOccurrenceBoundFieldCode M numeralCode)
      (rawFormulaAndCode M
        (rawRestrictedPAAtomicAdequacyFieldCode M)
        (rawFormulaAndCode M
          (rawRestrictedPAFormulaCoverageFieldCode M)
          (rawFormulaAndCode M
            (rawRestrictedPARuleCoverageFieldCode M)
            (rawRestrictedPABottomEndpointFieldCode M))))).

Definition rawRestrictedPAProofFieldsCode (M : RawPAModel)
    (numeralCode : M) : M :=
  rawFormulaAndCode M
    (rawRestrictedPACertificateTupleFieldCode M)
    (rawRestrictedPAProofFieldsSuffix6Code M numeralCode).

(** Bodies seen after opening, respectively, the witness-list, proof-root,
    and proof-context existential quantifiers. *)
Definition rawRestrictedPAProofAfterWitnessCode (M : RawPAModel)
    (numeralCode : M) : M :=
  rawFormulaExCode M
    (rawFormulaExCode M
      (rawRestrictedPAProofFieldsCode M numeralCode)).

Definition rawRestrictedPAProofAfterProofCode (M : RawPAModel)
    (numeralCode : M) : M :=
  rawFormulaExCode M
    (rawRestrictedPAProofFieldsCode M numeralCode).

Arguments rawRestrictedPAOccurrenceBoundFieldCode M numeralCode
  : clear implicits.
Arguments rawRestrictedPAProofFieldsSuffix6Code M numeralCode
  : clear implicits.
Arguments rawRestrictedPAProofFieldsCode M numeralCode : clear implicits.
Arguments rawRestrictedPAProofAfterWitnessCode M numeralCode
  : clear implicits.
Arguments rawRestrictedPAProofAfterProofCode M numeralCode
  : clear implicits.

(** Definitional exposure of the three binders and the seven fields.  No
    formula decoder or standardness of [numeralCode] is used. *)
Theorem raw_restrictedPAProofAssumptionCode_view : forall
    (M : RawPAModel) numeralCode,
  rawRestrictedPAProofAssumptionCode M numeralCode =
  rawFormulaExCode M
    (rawRestrictedPAProofAfterWitnessCode M numeralCode).
Proof.
  intros M numeralCode.
  unfold rawRestrictedPAProofAssumptionCode,
    restrictedTargetCodedRestrictedPAProofContext,
    rawRestrictedPAProofAfterWitnessCode,
    rawRestrictedPAProofAfterProofCode,
    rawRestrictedPAProofFieldsCode,
    rawRestrictedPAProofFieldsSuffix6Code,
    rawRestrictedPACertificateTupleFieldCode,
    rawRestrictedPAAxiomContextFieldCode,
    rawRestrictedPAOccurrenceBoundFieldCode,
    rawRestrictedPAAtomicAdequacyFieldCode,
    rawRestrictedPAFormulaCoverageFieldCode,
    rawRestrictedPARuleCoverageFieldCode,
    rawRestrictedPABottomEndpointFieldCode.
  cbn [restrictedTargetExN rawRestrictedTargetFormulaContextCode].
  reflexivity.
Qed.

(** The local proof really begins with the checker formula as an assumption,
    over the exact witnessed-axiom context carried by the incoming lower
    certificate.  The previous empty-context specialization discarded data
    needed by any compiler which actually reuses that certificate. *)
Theorem raw_codedPAOpenProofOf_restrictedPAProof_assumption : forall
    (M : RawPAModel), RawPASatisfies M -> forall numeralCode,
  forall witnessList baseContext,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPAOpenProofOf M
    witnessList baseContext
    (rawRestrictedPAProofAssumptionCode M numeralCode)
    (rawRestrictedPAProofAssumptionCode M numeralCode)
    (rawProofAssumptionRoot M
      (rawListNode M
        (rawRestrictedPAProofAssumptionCode M numeralCode)
        baseContext)
      (rawRestrictedPAProofAssumptionCode M numeralCode)).
Proof.
  intros M hPA numeralCode witnessList baseContext hwitness.
  apply (raw_codedPAOpenProofOf_assumption M hPA
    witnessList baseContext
    (rawRestrictedPAProofAssumptionCode M numeralCode)).
  exact hwitness.
Qed.

End PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
