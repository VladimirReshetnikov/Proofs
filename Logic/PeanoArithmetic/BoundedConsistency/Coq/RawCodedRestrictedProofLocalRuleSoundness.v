(**
  Assembly of constructor-local soundness for covered coded proofs.

  The substantial proofs are split by semantic role: propositional rules,
  four local quantified/equality rules, and the two eigenvariable rules.
  This module records the small public composition step and is the sole
  dependency needed by the final restricted-consistency theorem.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperationRankPreservation
  RawCodedRestrictedProofCoveredSoundness
  RawCodedRestrictedProofPropositionalSoundness
  RawCodedRestrictedProofSpecialSoundness
  RawCodedRestrictedProofEigenRuleSoundness
  RawCodedRestrictedProofExERuleSoundness.

Module PABoundedRawCodedRestrictedProofLocalRuleSoundness.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedFormulaOperationRankPreservation.
Import PABoundedRawCodedRestrictedProofCoveredSoundness.
Import PABoundedRawCodedRestrictedProofPropositionalSoundness.
Import PABoundedRawCodedRestrictedProofSpecialSoundness.
Import PABoundedRawCodedRestrictedProofEigenRuleSoundness.
Import PABoundedRawCodedRestrictedProofExERuleSoundness.

(** Temporary one-seam assembly, useful independently as an exact audit of
    what remains after All-I.  The unconditional corollaries below this lemma
    are added as soon as the separately compiled Ex-E module is imported. *)
Lemma raw_restrictedProofCovered_specialRuleTruthSound_of_exE : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredSelectedSpecialCaseTruthSound M level
    (RawProofExERuleValidCase M) ->
  RawRestrictedProofCoveredSpecialRuleTruthSound M level.
Proof.
  intros M hPA level hexE.
  exact (raw_restrictedProofCovered_specialRuleTruthSound_of_rank_and_eigen
    M hPA level
    (raw_codedFormulaSingleSubstitution_rank_preserving_all M hPA)
    (raw_restrictedProofCovered_allI_sound M hPA level)
    hexE).
Qed.

Lemma raw_restrictedProofCovered_ruleTruthSound_of_exE : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredSelectedSpecialCaseTruthSound M level
    (RawProofExERuleValidCase M) ->
  RawRestrictedProofCoveredRuleTruthSound M level.
Proof.
  intros M hPA level hexE.
  exact (raw_restrictedProofCovered_ruleTruthSound_of_special M hPA level
    (raw_restrictedProofCovered_specialRuleTruthSound_of_exE
      M hPA level hexE)).
Qed.

(** All six non-propositional cases are now concrete. *)
Theorem raw_restrictedProofCovered_specialRuleTruthSound : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredSpecialRuleTruthSound M level.
Proof.
  intros M hPA level.
  exact (raw_restrictedProofCovered_specialRuleTruthSound_of_exE
    M hPA level
    (raw_restrictedProofCovered_exE_sound M hPA level)).
Qed.

(** Public constructor-local endpoint consumed by covered proof-code
    induction.  It covers all seventeen natural-deduction constructors. *)
Theorem raw_restrictedProofCovered_ruleTruthSound : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawRestrictedProofCoveredRuleTruthSound M level.
Proof.
  intros M hPA level.
  exact (raw_restrictedProofCovered_ruleTruthSound_of_special M hPA level
    (raw_restrictedProofCovered_specialRuleTruthSound M hPA level)).
Qed.

End PABoundedRawCodedRestrictedProofLocalRuleSoundness.
