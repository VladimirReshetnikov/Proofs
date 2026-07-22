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
  proof-producing obligation.  It contains both the self-shift certificate
  for the retained witnessed-axiom base and the dynamic-reflection step.  The
  theorem below discharges every subsequent context and projection step.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedNumeralTermCode
  RawCodedContextLists RawCodedContextShift RawCodedRestrictedPAProof
  RawCodedProofEndpoints RawCodedProofRuleCoverage RawCodedPAProvability
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
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
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
    (M : RawPAModel) (baseContext numeralCode : M) : M :=
  rawRestrictedPAShiftedRootContextCode M baseContext
    (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 1).

Definition rawRestrictedPACanonicalShiftedWitnessContextCode
    (M : RawPAModel) (baseContext numeralCode : M) : M :=
  rawRestrictedPAShiftedWitnessContextCode M baseContext
    (rawRestrictedPAProofAfterWitnessIteratedShiftCode M numeralCode 1)
    (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 2).

Definition rawRestrictedPACanonicalShiftedProofContextCode
    (M : RawPAModel) (baseContext numeralCode : M) : M :=
  rawRestrictedPAShiftedProofContextCode M baseContext
    (rawRestrictedPAProofAfterProofIteratedShiftCode M numeralCode 1)
    (rawRestrictedPAProofAfterWitnessIteratedShiftCode M numeralCode 2)
    (rawRestrictedPAProofAssumptionIteratedShiftCode M numeralCode 3).

Arguments rawRestrictedPACanonicalShiftedRootContextCode
  M baseContext numeralCode : clear implicits.
Arguments rawRestrictedPACanonicalShiftedWitnessContextCode
  M baseContext numeralCode : clear implicits.
Arguments rawRestrictedPACanonicalShiftedProofContextCode
  M baseContext numeralCode : clear implicits.

(** The sole remaining carried compiler.

    Its [projections] argument contains seven genuine local PA proof trees,
    all in the exact field context used by the third existential elimination.
    The lower target/certificate and the successor numeral-code witness are
    retained because the missing dynamic partial-truth construction must use
    them.  Its first output is the exact unpacking of the incoming lower proof;
    after the base self-shift it receives the seven projections and returns
    only the final covered local proof of [bottom]. *)
Definition RawRestrictedPAProjectedFieldRefutationCompiler
    (M : RawPAModel) : Prop :=
  forall level target certificate successorNumeralCode,
    RawRestrictedPAConsistencyFormulaCodeAt M level target ->
    RawCodedPAProofOf M target certificate ->
    RawNumeralTermCodeAt M (raw_succ M level) successorNumeralCode ->
    exists witnessList lowerProof baseContext : M,
      certificate = rawCodeList3 M
        (rawNumeralValue M 0) witnessList lowerProof /\
      RawCodedPAAxiomWitnessContext M witnessList baseContext /\
      RawProofRuleCoverage M lowerProof /\
      RawProofEndpoint M lowerProof baseContext target /\
      RawContextShift M baseContext baseContext /\
      (RawRestrictedPAFieldProjectionPackage M successorNumeralCode
        (rawRestrictedPACanonicalShiftedProofContextCode
          M baseContext successorNumeralCode) ->
       exists fieldChild : M,
         RawCodedPALocalProofOf M
           (rawRestrictedPAFieldsContextCode M successorNumeralCode
             (rawRestrictedPACanonicalShiftedProofContextCode
               M baseContext successorNumeralCode))
           (rawFormulaBotCode M) fieldChild).

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
  destruct (hprojected level target certificate successorNumeralCode
      htarget hcertificate hnumeral) as
    (witnessList & lowerProof & baseContext & hcertificateView &
      hwitness & hlowerCoverage & hlowerEndpoint & hbaseShift & hrefute).
  set (shiftedRootContext :=
    rawRestrictedPACanonicalShiftedRootContextCode
      M baseContext successorNumeralCode).
  set (shiftedWitnessContext :=
    rawRestrictedPACanonicalShiftedWitnessContextCode
      M baseContext successorNumeralCode).
  set (shiftedProofContext :=
    rawRestrictedPACanonicalShiftedProofContextCode
      M baseContext successorNumeralCode).
  assert (hcontexts : RawRestrictedPAExistentialDescentContexts M
      successorNumeralCode baseContext shiftedRootContext
      shiftedWitnessContext shiftedProofContext).
  {
    unfold shiftedRootContext, shiftedWitnessContext, shiftedProofContext.
    exact (raw_restrictedPAExistentialDescentContexts_realized
      M hPA (raw_succ M level) successorNumeralCode baseContext
      hnumeral hbaseShift).
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
  destruct (hrefute hprojections)
    as [fieldChild hfieldChild].
  exists witnessList, lowerProof, baseContext, shiftedRootContext,
    shiftedWitnessContext, shiftedProofContext, fieldChild.
  split; [exact hcertificateView |].
  split; [exact hwitness |].
  split; [exact hlowerCoverage |].
  split; [exact hlowerEndpoint |].
  split; [exact hbaseShift |].
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
