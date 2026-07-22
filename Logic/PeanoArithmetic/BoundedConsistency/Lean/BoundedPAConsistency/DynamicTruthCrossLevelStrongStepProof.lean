import BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStep

/-!
# Compatibility export for the congruence-safe cross-level strong step

An earlier version of this module applied completeness directly to an
arbitrary expansion of PA.  That is not sound for opaque predicates: lifted
PA does not force either placeholder to respect the source equality
relation.  The replacement below deliberately exports the literal-successor
source theorem from `DynamicTruthCrossLevelDerivedStrongStep`, whose
antecedent contains both missing coordinatewise congruence laws and whose
semantic proof works only after equality quotienting.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepProof

open LO FirstOrder
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStep

/-- Compatibility name for the explicit congruence antecedent. -/
noncomputable abbrev sourceCongruenceContext :=
  sourcePlaceholderCongruenceContext

/-- Compatibility name for the sound literal-successor source sentence. -/
noncomputable abbrev sourceStrongStepSentence :=
  sourceCongruentDerivedStrongStepSentence

/-- The compatibility proof is exactly the audited quotient-safe proof; no
bare theorem about arbitrary opaque source relations is reintroduced. -/
noncomputable def sourceStrongStepProof :
    twoPredicateParameterPeano 3 3 3 ⊢! sourceStrongStepSentence :=
  sourceCongruentDerivedStrongStepProof

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepProof
