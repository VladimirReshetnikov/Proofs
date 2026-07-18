(**
  The bounded-consistency theorem for PA.

  All semantic interfaces used by the generic restricted-proof exclusion
  theorem have now been discharged in arbitrary models of PA: constructor-
  local proof-rule soundness and truth of every witnessed PA-axiom context.
  This module deliberately exposes only the resulting object-level theorem,
  with no callback or semantic premise in its statement.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAConsistency
  RawCodedRestrictedPAProofExclusion
  RawCodedPAAxiomWitnessContextTruthComplete
  RawCodedRestrictedProofLocalRuleSoundness.

Module PABoundedRawCodedRestrictedPAConsistencyTheorem.

Import ListNotations.
Import PA.

Import PABoundedRawCodedRestrictedPAConsistency.
Import PABoundedRawCodedRestrictedPAProofExclusion.
Import PABoundedRawCodedPAAxiomWitnessContextTruthComplete.
Import PABoundedRawCodedRestrictedProofLocalRuleSoundness.

(** For each metatheoretic quantifier-group bound, PA proves that no coded
    PA derivation restricted to that bound concludes falsity. *)
Theorem PA_BProv_restrictedPAConsistencyFormula :
  forall level,
    Formula.BProv Formula.Ax_s []
      (restrictedPAConsistencyFormula level).
Proof.
  intro level.
  apply (PA_BProv_restrictedPAConsistencyFormula_of_covered_soundness level).
  - intros M hPA.
    exact (raw_restrictedProofCovered_ruleTruthSound M hPA level).
  - exact (raw_codedPAAxiomWitnessContextsSigmaTrueInAllModels_all level).
Qed.

End PABoundedRawCodedRestrictedPAConsistencyTheorem.
