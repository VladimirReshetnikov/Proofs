(**
  Unconditional realization of the six formula shifts used by restricted
  PA consistency.

  The three contexts below are exactly the formula bodies visible before,
  after one, and after two existential eliminations.  The iterated restricted
  target shift theorem supplies respectively three, two, and one successor
  renaming edges.  Feeding those six edges to
  [RawRestrictedPAFormulaShiftOrbit] constructs all three pointwise context
  shifts with no residual syntax-operation premise.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedNumeralTermCode
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAConsistencyOpenCompiler
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedTargetFormulaShift
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedPAConsistencyShiftOrbit.

Module PABoundedRawCodedRestrictedPAConsistencyShiftRealization.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAConsistencyOpenCompiler.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedTargetFormulaShift.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedPAConsistencyShiftOrbit.

Definition restrictedPAProofAssumptionFormulaContext
    : RestrictedTargetFormulaContext :=
  restrictedTargetCodedRestrictedPAProofContext (tVar 0).

Definition restrictedFormulaContextExBody
    (context : RestrictedTargetFormulaContext)
    : RestrictedTargetFormulaContext :=
  match context with
  | RTFCEx body => body
  | _ => RTFCBot
  end.

Definition restrictedPAProofAfterWitnessFormulaContext
    : RestrictedTargetFormulaContext :=
  restrictedFormulaContextExBody restrictedPAProofAssumptionFormulaContext.

Definition restrictedPAProofAfterProofFormulaContext
    : RestrictedTargetFormulaContext :=
  restrictedFormulaContextExBody restrictedPAProofAfterWitnessFormulaContext.

(** Constructor-code views linking the reusable context representation to
    the names consumed by existential descent. *)
Lemma raw_restrictedPAProofAssumptionFormulaContext_view : forall
    (M : RawPAModel) numeralCode,
  rawRestrictedTargetFormulaContextCode M numeralCode
    restrictedPAProofAssumptionFormulaContext =
  rawRestrictedPAProofAssumptionCode M numeralCode.
Proof. reflexivity. Qed.

Lemma raw_restrictedPAProofAfterWitnessFormulaContext_view : forall
    (M : RawPAModel) numeralCode,
  rawRestrictedTargetFormulaContextCode M numeralCode
    restrictedPAProofAfterWitnessFormulaContext =
  rawRestrictedPAProofAfterWitnessCode M numeralCode.
Proof.
  intros M numeralCode.
  unfold restrictedPAProofAfterWitnessFormulaContext,
    restrictedFormulaContextExBody,
    restrictedPAProofAssumptionFormulaContext,
    restrictedTargetCodedRestrictedPAProofContext,
    rawRestrictedPAProofAfterWitnessCode,
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

Lemma raw_restrictedPAProofAfterProofFormulaContext_view : forall
    (M : RawPAModel) numeralCode,
  rawRestrictedTargetFormulaContextCode M numeralCode
    restrictedPAProofAfterProofFormulaContext =
  rawRestrictedPAProofAfterProofCode M numeralCode.
Proof.
  intros M numeralCode.
  unfold restrictedPAProofAfterProofFormulaContext,
    restrictedPAProofAfterWitnessFormulaContext,
    restrictedFormulaContextExBody,
    restrictedPAProofAssumptionFormulaContext,
    restrictedTargetCodedRestrictedPAProofContext,
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

(** The proof checker context uses neither compound term contexts nor a seal.
    Fixed formula leaves remain opaque to this computation. *)
Lemma restrictedPAProofAssumptionFormulaContext_shift_supported :
  RestrictedTargetFormulaContextShiftSupported
    restrictedPAProofAssumptionFormulaContext.
Proof.
  unfold restrictedPAProofAssumptionFormulaContext,
    restrictedTargetCodedRestrictedPAProofContext,
    restrictedTargetProofContext,
    restrictedTargetProofCertificateWithSupportContext,
    restrictedTargetProofTraversalContext,
    restrictedTargetProofConstructorOccurrencesBoundedContext,
    restrictedTargetProofOccurrenceCasesBoundedContext,
    restrictedTargetProofFormulaFieldsBoundedContext,
    restrictedTargetContextAllBoundedContext,
    restrictedTargetContextAllBoundedWithTablesContext,
    restrictedTargetFormulaQuantifierBoundedContext,
    restrictedTargetSigmaDomainContext,
    restrictedTargetPiDomainContext,
    restrictedTargetLeContext.
  cbn [restrictedTargetExN restrictedTargetAllN
    RestrictedTargetFormulaContextShiftSupported
    RestrictedTargetTermContextShiftSupported].
  repeat split; exact I.
Qed.

Lemma restrictedPAProofAfterWitnessFormulaContext_shift_supported :
  RestrictedTargetFormulaContextShiftSupported
    restrictedPAProofAfterWitnessFormulaContext.
Proof.
  exact restrictedPAProofAssumptionFormulaContext_shift_supported.
Qed.

Lemma restrictedPAProofAfterProofFormulaContext_shift_supported :
  RestrictedTargetFormulaContextShiftSupported
    restrictedPAProofAfterProofFormulaContext.
Proof.
  exact restrictedPAProofAssumptionFormulaContext_shift_supported.
Qed.

Definition rawRestrictedPAProofAssumptionIteratedShiftCode
    (M : RawPAModel) (numeralCode : M) (prior : nat) : M :=
  rawRestrictedTargetFormulaContextIteratedShiftCode
    M numeralCode 0 prior restrictedPAProofAssumptionFormulaContext.

Definition rawRestrictedPAProofAfterWitnessIteratedShiftCode
    (M : RawPAModel) (numeralCode : M) (prior : nat) : M :=
  rawRestrictedTargetFormulaContextIteratedShiftCode
    M numeralCode 0 prior restrictedPAProofAfterWitnessFormulaContext.

Definition rawRestrictedPAProofAfterProofIteratedShiftCode
    (M : RawPAModel) (numeralCode : M) (prior : nat) : M :=
  rawRestrictedTargetFormulaContextIteratedShiftCode
    M numeralCode 0 prior restrictedPAProofAfterProofFormulaContext.

Arguments rawRestrictedPAProofAssumptionIteratedShiftCode
  M numeralCode prior : clear implicits.
Arguments rawRestrictedPAProofAfterWitnessIteratedShiftCode
  M numeralCode prior : clear implicits.
Arguments rawRestrictedPAProofAfterProofIteratedShiftCode
  M numeralCode prior : clear implicits.

(** All six exact edges, packaged in the order expected by the context-orbit
    bridge. *)
Theorem raw_restrictedPAFormulaShiftOrbit_realized : forall
    (M : RawPAModel), RawPASatisfies M -> forall level numeralCode,
  RawNumeralTermCodeAt M level numeralCode ->
  RawRestrictedPAFormulaShiftOrbit M numeralCode
    (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 1)
    (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 2)
    (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 3)
    (rawRestrictedPAProofAfterWitnessIteratedShiftCode M numeralCode 1)
    (rawRestrictedPAProofAfterWitnessIteratedShiftCode M numeralCode 2)
    (rawRestrictedPAProofAfterProofIteratedShiftCode M numeralCode 1).
Proof.
  intros M hPA level numeralCode hnumeral.
  assert (hAssumption0 :
      rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 0 =
      rawRestrictedPAProofAssumptionCode M numeralCode).
  {
    unfold rawRestrictedPAProofAssumptionIteratedShiftCode.
    rewrite rawRestrictedTargetFormulaContextIteratedShiftCode_zero
      by exact restrictedPAProofAssumptionFormulaContext_shift_supported.
    apply raw_restrictedPAProofAssumptionFormulaContext_view.
  }
  assert (hAfterWitness0 :
      rawRestrictedPAProofAfterWitnessIteratedShiftCode M numeralCode 0 =
      rawRestrictedPAProofAfterWitnessCode M numeralCode).
  {
    unfold rawRestrictedPAProofAfterWitnessIteratedShiftCode.
    rewrite rawRestrictedTargetFormulaContextIteratedShiftCode_zero
      by exact restrictedPAProofAfterWitnessFormulaContext_shift_supported.
    apply raw_restrictedPAProofAfterWitnessFormulaContext_view.
  }
  assert (hAfterProof0 :
      rawRestrictedPAProofAfterProofIteratedShiftCode M numeralCode 0 =
      rawRestrictedPAProofAfterProofCode M numeralCode).
  {
    unfold rawRestrictedPAProofAfterProofIteratedShiftCode.
    rewrite rawRestrictedTargetFormulaContextIteratedShiftCode_zero
      by exact restrictedPAProofAfterProofFormulaContext_shift_supported.
    apply raw_restrictedPAProofAfterProofFormulaContext_view.
  }
  unfold RawRestrictedPAFormulaShiftOrbit.
  repeat split.
  - rewrite <- hAssumption0.
    exact (raw_codedFormulaShift_restrictedTargetContext_iterated
      M hPA level numeralCode 0 0
      restrictedPAProofAssumptionFormulaContext hnumeral
      restrictedPAProofAssumptionFormulaContext_shift_supported).
  - exact (raw_codedFormulaShift_restrictedTargetContext_iterated
      M hPA level numeralCode 0 1
      restrictedPAProofAssumptionFormulaContext hnumeral
      restrictedPAProofAssumptionFormulaContext_shift_supported).
  - exact (raw_codedFormulaShift_restrictedTargetContext_iterated
      M hPA level numeralCode 0 2
      restrictedPAProofAssumptionFormulaContext hnumeral
      restrictedPAProofAssumptionFormulaContext_shift_supported).
  - rewrite <- hAfterWitness0.
    exact (raw_codedFormulaShift_restrictedTargetContext_iterated
      M hPA level numeralCode 0 0
      restrictedPAProofAfterWitnessFormulaContext hnumeral
      restrictedPAProofAfterWitnessFormulaContext_shift_supported).
  - exact (raw_codedFormulaShift_restrictedTargetContext_iterated
      M hPA level numeralCode 0 1
      restrictedPAProofAfterWitnessFormulaContext hnumeral
      restrictedPAProofAfterWitnessFormulaContext_shift_supported).
  - rewrite <- hAfterProof0.
    exact (raw_codedFormulaShift_restrictedTargetContext_iterated
      M hPA level numeralCode 0 0
      restrictedPAProofAfterProofFormulaContext hnumeral
      restrictedPAProofAfterProofFormulaContext_shift_supported).
Qed.

(** The three concrete context-shift witnesses now exist unconditionally
    from the numeral-code certificate. *)
Corollary raw_restrictedPAExistentialDescentContexts_realized : forall
    (M : RawPAModel), RawPASatisfies M -> forall level numeralCode,
  RawNumeralTermCodeAt M level numeralCode ->
  RawRestrictedPAExistentialDescentContexts M numeralCode
    (rawRestrictedPAShiftedRootContextCode M
      (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 1))
    (rawRestrictedPAShiftedWitnessContextCode M
      (rawRestrictedPAProofAfterWitnessIteratedShiftCode M numeralCode 1)
      (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 2))
    (rawRestrictedPAShiftedProofContextCode M
      (rawRestrictedPAProofAfterProofIteratedShiftCode M numeralCode 1)
      (rawRestrictedPAProofAfterWitnessIteratedShiftCode M numeralCode 2)
      (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 3)).
Proof.
  intros M hPA level numeralCode hnumeral.
  apply raw_restrictedPAExistentialDescentContexts_of_formulaShiftOrbit.
  - exact hPA.
  - exact (raw_restrictedPAFormulaShiftOrbit_realized
      M hPA level numeralCode hnumeral).
Qed.

End PABoundedRawCodedRestrictedPAConsistencyShiftRealization.
