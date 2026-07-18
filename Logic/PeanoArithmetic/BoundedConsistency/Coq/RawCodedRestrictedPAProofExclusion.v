(**
  Assembly of coverage-aware proof soundness into restricted PA consistency.

  The strengthened restricted-proof wrapper already carries every syntactic
  resource needed by the nonstandard proof induction.  Two semantic facts
  remain deliberately explicit here: constructor-local rule soundness and
  truth of the witnessed PA-axiom context under the total zero assignment.
  Once clients discharge those facts, falsity's fixed-level truth law gives
  model-internal proof exclusion and raw completeness returns an actual PA
  derivation of the consistency sentence.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignmentTotality
  RawCodedContextBounds RawCodedFixedLevelContextTruth
  RawCodedFixedLevelBottomLaws
  RawCodedProofRules RawCodedRestrictedProofTraversal
  RawCodedProofAtomicAdequacy
  RawCodedRestrictedProofCoveredSoundness RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistency.

Module PABoundedRawCodedRestrictedPAProofExclusion.

Import ListNotations.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedContextBounds.
Import PABoundedRawCodedFixedLevelContextTruth.
Import PABoundedRawCodedFixedLevelBottomLaws.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedRestrictedProofCoveredSoundness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistency.

Definition RawCodedPAAxiomWitnessContextsSigmaTrue
    (M : RawPAModel) (level : nat) : Prop :=
  forall witnessList context : M,
    RawCodedPAAxiomWitnessContext M witnessList context ->
    RawContextAllBounded M level context ->
    RawContextAllAtomicallyAdequate M context ->
    RawContextAllSigmaTrue M (S level) context
      (raw_zero M) (raw_zero M).

Arguments RawCodedPAAxiomWitnessContextsSigmaTrue M level
  : clear implicits.

Theorem raw_codedRestrictedPAProof_excluded_covered : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredRuleTruthSound M level ->
  RawCodedPAAxiomWitnessContextsSigmaTrue M level ->
  forall certificate : M,
    RawCodedRestrictedPAProof M level certificate -> False.
Proof.
  intros M hPA level hlocal haxioms certificate
    (witnessList & proof & context & _ & hwitnessed & hrestricted &
      hatomic & (coverageBound & hcoverage) & hruleCoverage & hvalid).
  pose proof (raw_proofRuleValid_endpoint M proof context
    (rawFormulaBotCode M) hvalid) as hendpoint.
  pose proof hrestricted as hrestrictedFull.
  destruct hrestricted as
    (supportCode & supportStep & hrestrictedCertificate).
  pose proof (raw_restrictedProofCertificate_root_node M hPA
    level proof supportCode supportStep hrestrictedCertificate) as hrootNode.
  pose proof (raw_restrictedProofNode_endpoint_occurrence M level
    proof supportCode supportStep hrootNode context
    (rawFormulaBotCode M) hendpoint) as [hcontextBounded _].
  pose proof (raw_proofAtomicallyAdequate_root_endpoint M hPA
    proof hatomic context (rawFormulaBotCode M) hendpoint)
    as [hcontextAtomic _].
  apply (raw_restrictedProofCovered_bottom_exclusion M hPA level
    hlocal (raw_fixedLevelSigmaBottomFalse_successor M hPA level)
    proof coverageBound context (raw_zero M) (raw_zero M)
    hrestrictedFull hatomic hcoverage hruleCoverage).
  - exact (raw_codedZeroAssignment_defined_all M hPA coverageBound).
  - exact hvalid.
  - exact (haxioms witnessList context hwitnessed
      hcontextBounded hcontextAtomic).
Qed.

Definition RawRestrictedProofCoveredRuleTruthSoundInAllModels
    (level : nat) : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawRestrictedProofCoveredRuleTruthSound M level.

Definition RawCodedPAAxiomWitnessContextsSigmaTrueInAllModels
    (level : nat) : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawCodedPAAxiomWitnessContextsSigmaTrue M level.

(** This endpoint is already an object-level PA theorem.  Its two premises
    are the exact arbitrary-model facts discharged by the local-rule and
    PA-axiom truth modules, not assumptions added to the object theory. *)
Theorem PA_BProv_restrictedPAConsistencyFormula_of_covered_soundness :
  forall level,
  RawRestrictedProofCoveredRuleTruthSoundInAllModels level ->
  RawCodedPAAxiomWitnessContextsSigmaTrueInAllModels level ->
  Formula.BProv Formula.Ax_s []
    (restrictedPAConsistencyFormula level).
Proof.
  intros level hlocal haxioms.
  apply PA_BProv_restrictedPAConsistencyFormula_of_raw_exclusion.
  intros M hPA certificate hcertificate.
  exact (raw_codedRestrictedPAProof_excluded_covered M hPA level
    (hlocal M hPA) (haxioms M hPA) certificate hcertificate).
Qed.

End PABoundedRawCodedRestrictedPAProofExclusion.
