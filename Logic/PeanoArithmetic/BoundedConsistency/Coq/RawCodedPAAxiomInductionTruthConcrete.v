(** Concrete discharge of PA induction truth from operation theorems. *)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthOperationTarskiPositive
  RawCodedFixedLevelTruthOperationTarskiSubstitutionPositive
  RawCodedFormulaOperationRankPreservation
  RawCodedPAAxiomTruth RawCodedPAAxiomInductionTruth.

Module PABoundedRawCodedPAAxiomInductionTruthConcrete.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthOperationTarskiPositive.
Import PABoundedRawCodedFixedLevelTruthOperationTarskiSubstitutionPositive.
Import PABoundedRawCodedFormulaOperationRankPreservation.
Import PABoundedRawCodedPAAxiomTruth.
Import PABoundedRawCodedPAAxiomInductionTruth.

(** This name isolates the sole formula-operation fact not contained in the
    rank/Tarski modules: shifting a syntactically adequate formula preserves
    the atomic-term adequacy needed by fixed-level truth totality. *)
Definition RawInductionShiftAtomicAdequacy (M : RawPAModel) : Prop :=
  forall cutoff amount input output,
    RawCodedFormulaShift M cutoff amount input output ->
    RawCodedFormulaAtomicallyAdequate M input ->
    RawCodedFormulaAtomicallyAdequate M output.

Arguments RawInductionShiftAtomicAdequacy M : clear implicits.

Theorem raw_fixedLevelInductionProgressTransport_of_shift_atomic : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawInductionShiftAtomicAdequacy M ->
  RawFixedLevelInductionProgressTransportAll M level.
Proof.
  intros M hPA level hatomic.
  apply (raw_fixedLevelInductionProgressTransport_of_operation_facts
    M hPA level).
  - exact (raw_codedFormulaShift_rank_preserving_all M hPA).
  - exact (raw_codedFormulaSingleSubstitution_rank_preserving_all M hPA).
  - exact hatomic.
  - apply raw_fixedLevelFormulaShiftTarskiStep_all. exact hPA.
  - apply raw_fixedLevelFormulaSingleSubstitutionTarskiStep_all. exact hPA.
Qed.

Theorem raw_fixedLevelPAAxiomInductionSigmaSound_of_shift_atomic : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawInductionShiftAtomicAdequacy M ->
  RawFixedLevelPAAxiomInductionSigmaSound M level.
Proof.
  intros M hPA level hatomic.
  apply (raw_codedPAAxiomInduction_sigma_of_progress_transport M hPA level).
  exact (raw_fixedLevelInductionProgressTransport_of_shift_atomic
    M hPA level hatomic).
Qed.

End PABoundedRawCodedPAAxiomInductionTruthConcrete.
