(**
  Reduce the exact restricted-PA field refutation compiler to one local
  proof-producing reflection step.

  The three contexts below are the canonical witnesses supplied by the
  realized six-edge formula-shift orbit.  In the innermost context, the
  seven checker fields are available through honest [RP_andE1]/[RP_andE2]
  derivations.  Consequently a remaining compiler need not manufacture
  shifts or trust a meta-level decomposition of the checker conjunction: it
  receives the complete local projection package and only has to compose
  those proofs with the lower consistency certificate into falsity.

  This module deliberately does not call semantic validity a proof code.
  [RawRestrictedPAProjectedFieldRefutationCompiler] is the exact remaining
  proof-producing reflection obligation.  The theorem below proves that it
  implies the previously exposed field-refutation compiler, discharging all
  surrounding syntax bookkeeping unconditionally in every PA model.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedNumeralTermCode
  RawCodedContextLists RawCodedContextShift RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedRestrictedPAConsistencyFormulaCode
  CompactPAUniformProvability
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedPAConsistencyShiftOrbit
  RawCodedRestrictedPAConsistencyShiftRealization
  RawCodedRestrictedPAFieldProjections.

Module PABoundedRawCodedRestrictedPAProjectedFieldRefutation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedPAConsistencyShiftOrbit.
Import PABoundedRawCodedRestrictedPAConsistencyShiftRealization.
Import PABoundedRawCodedRestrictedPAFieldProjections.

(** Canonical contexts after respectively one, two, and three existential
    eliminations.  Naming them keeps the remaining reflection interface
    readable and makes its context equality definitional. *)
Definition rawRestrictedPACanonicalShiftedRootContextCode
    (M : RawPAModel) (numeralCode : M) : M :=
  rawRestrictedPAShiftedRootContextCode M
    (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 1).

Definition rawRestrictedPACanonicalShiftedWitnessContextCode
    (M : RawPAModel) (numeralCode : M) : M :=
  rawRestrictedPAShiftedWitnessContextCode M
    (rawRestrictedPAProofAfterWitnessIteratedShiftCode M numeralCode 1)
    (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 2).

Definition rawRestrictedPACanonicalShiftedProofContextCode
    (M : RawPAModel) (numeralCode : M) : M :=
  rawRestrictedPAShiftedProofContextCode M
    (rawRestrictedPAProofAfterProofIteratedShiftCode M numeralCode 1)
    (rawRestrictedPAProofAfterWitnessIteratedShiftCode M numeralCode 2)
    (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 3).

Arguments rawRestrictedPACanonicalShiftedRootContextCode
  M numeralCode : clear implicits.
Arguments rawRestrictedPACanonicalShiftedWitnessContextCode
  M numeralCode : clear implicits.
Arguments rawRestrictedPACanonicalShiftedProofContextCode
  M numeralCode : clear implicits.

(** The sole remaining local compiler.

    Its [projections] argument contains seven genuine local PA proof trees,
    all in the exact field context used by the third existential elimination.
    The lower target/certificate and the successor numeral-code witness are
    retained because the missing dynamic partial-truth construction must use
    them.  The output is only the final covered local proof of [bottom]. *)
Definition RawRestrictedPAProjectedFieldRefutationCompiler
    (M : RawPAModel) : Prop :=
  forall level target certificate successorNumeralCode,
    RawRestrictedPAConsistencyFormulaCodeAt M level target ->
    RawCodedPAProofOf M target certificate ->
    RawNumeralTermCodeAt M (raw_succ M level) successorNumeralCode ->
    RawRestrictedPAFieldProjectionPackage M successorNumeralCode
      (rawRestrictedPACanonicalShiftedProofContextCode
        M successorNumeralCode) ->
    exists fieldChild : M,
      RawCodedPALocalProofOf M
        (rawRestrictedPAFieldsContextCode M successorNumeralCode
          (rawRestrictedPACanonicalShiftedProofContextCode
            M successorNumeralCode))
        (rawFormulaBotCode M) fieldChild.

Arguments RawRestrictedPAProjectedFieldRefutationCompiler M
  : clear implicits.

Definition RawRestrictedPAProjectedFieldRefutationCompilerInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawRestrictedPAProjectedFieldRefutationCompiler M.

(** All three existential shifts and every conjunction projection are now
    theorem outputs, not premises of the old compiler. *)
Theorem raw_restrictedPAConsistencyFieldRefutation_of_projectedFields :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawRestrictedPAProjectedFieldRefutationCompiler M ->
  RawRestrictedPAConsistencyFieldRefutationCompiler M.
Proof.
  intros M hPA hprojected level target certificate successorNumeralCode
    htarget hcertificate hnumeral.
  set (shiftedRootContext :=
    rawRestrictedPACanonicalShiftedRootContextCode
      M successorNumeralCode).
  set (shiftedWitnessContext :=
    rawRestrictedPACanonicalShiftedWitnessContextCode
      M successorNumeralCode).
  set (shiftedProofContext :=
    rawRestrictedPACanonicalShiftedProofContextCode
      M successorNumeralCode).
  assert (hcontexts : RawRestrictedPAExistentialDescentContexts M
      successorNumeralCode shiftedRootContext shiftedWitnessContext
      shiftedProofContext).
  {
    unfold shiftedRootContext, shiftedWitnessContext, shiftedProofContext.
    exact (raw_restrictedPAExistentialDescentContexts_realized
      M hPA (raw_succ M level) successorNumeralCode hnumeral).
  }
  destruct hcontexts as [hrootShift [hwitnessShift hproofShift]].
  assert (hproofContextRealizable :
      RawContextListRealizable M shiftedProofContext).
  {
    exact (raw_contextShift_target_realizable M
      (rawRestrictedPAAfterProofContextCode M successorNumeralCode
        shiftedWitnessContext)
      shiftedProofContext hproofShift).
  }
  assert (hprojections : RawRestrictedPAFieldProjectionPackage M
      successorNumeralCode shiftedProofContext).
  {
    exact (raw_restrictedPAFieldProjectionPackage M hPA
      successorNumeralCode shiftedProofContext hproofContextRealizable).
  }
  destruct (hprojected level target certificate successorNumeralCode
      htarget hcertificate hnumeral hprojections)
    as [fieldChild hfieldChild].
  exists shiftedRootContext, shiftedWitnessContext, shiftedProofContext,
    fieldChild.
  split.
  - exact (conj hrootShift (conj hwitnessShift hproofShift)).
  - exact hfieldChild.
Qed.

Corollary
    raw_restrictedPAConsistencyFieldRefutationInAllModels_of_projectedFields
    : RawRestrictedPAProjectedFieldRefutationCompilerInAllModels ->
  RawRestrictedPAConsistencyFieldRefutationCompilerInAllModels.
Proof.
  intros hprojected M hPA.
  exact (raw_restrictedPAConsistencyFieldRefutation_of_projectedFields
    M hPA (hprojected M hPA)).
Qed.

(** Fully connected conditional endpoint for the exact requested PA theorem.
    Only the local proof-producing reflection compiler above remains. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_projectedFields
    : RawRestrictedPAProjectedFieldRefutationCompilerInAllModels ->
  Formula.BProv Formula.Ax_s nil
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hprojected.
  apply
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_fieldRefutation.
  exact
    (raw_restrictedPAConsistencyFieldRefutationInAllModels_of_projectedFields
      hprojected).
Qed.

End PABoundedRawCodedRestrictedPAProjectedFieldRefutation.
