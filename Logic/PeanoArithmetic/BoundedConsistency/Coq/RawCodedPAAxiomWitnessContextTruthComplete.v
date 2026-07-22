(**
  Unconditional fixed-level truth of witnessed PA-axiom contexts.

  Restricted PA proof certificates carry a context whose entries are paired
  with explicit PA-axiom witnesses.  The generic context theorem separates
  induction instances from the finitely many bounded atomic axiom schemes.
  Formula-shift atomic adequacy has now discharged the induction branch, so
  the context interface required by proof exclusion has no remaining
  semantic premise.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedPAAxiomTruth RawCodedRestrictedPAProofExclusion
  RawCodedFormulaShiftAtomicAdequacy.

Module PABoundedRawCodedPAAxiomWitnessContextTruthComplete.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedPAAxiomTruth.
Import PABoundedRawCodedRestrictedPAProofExclusion.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.

(** Every witnessed PA-axiom context satisfying the proof certificate's
    rank and atomic-syntax side conditions is true at the successor level
    under the total zero beta assignment. *)
Theorem raw_codedPAAxiomWitnessContextsSigmaTrue_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawCodedPAAxiomWitnessContextsSigmaTrue M level.
Proof.
  intros M hPA level witnessList context hwitnessed hbounded hatomic.
  apply (raw_codedPAAxiomWitnessContext_sigma_zero_of_bounded_atomic
    M hPA level
    (raw_fixedLevelPAAxiomInductionSigmaSound_all M hPA level)
    witnessList context hwitnessed hbounded hatomic).
Qed.

(** The quantification shape used by the object-theorem assembly module. *)
Theorem raw_codedPAAxiomWitnessContextsSigmaTrueInAllModels_all : forall
    level,
  RawCodedPAAxiomWitnessContextsSigmaTrueInAllModels level.
Proof.
  intros level M hPA.
  exact (raw_codedPAAxiomWitnessContextsSigmaTrue_all M hPA level).
Qed.

End PABoundedRawCodedPAAxiomWitnessContextTruthComplete.
