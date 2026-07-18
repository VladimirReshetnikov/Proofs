import BoundedPAConsistency.FixedLevelSequentDefinability
import BoundedPAConsistency.FixedLevelTruthLaws

/-!
# Fixed-level soundness specialized to Peano arithmetic

The proof-calculus induction and the semantic laws were intentionally proved
independently.  This module joins them at one external hierarchy level while
leaving the theory-specific premise visible: every code accepted by PA's
internal axiom recognizer must be true in the fixed partial-truth predicate.

Keeping this seam explicit is useful for the two recognizer branches.  The
finite `PA⁻` branch reduces to standard quoted axioms, whereas the induction
branch contains genuinely nonstandard formula codes and needs model-internal
induction.  Once those branches supply `hAx` below, no further proof-rule
reasoning remains.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelSoundness

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency
open LeanProofs.BoundedPAConsistency.AbstractSoundness
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.FixedLevelSequentDefinability
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelTruthLaws

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- At a fixed external bound, truth of every internally recognized PA axiom
is the only theory-specific input needed to exclude a nonstandard restricted
derivation of falsity. -/
theorem restrictedConsistent_pa_of_sigmaTrue_axioms (n : ℕ)
    (hAx : ∀ p : V, p ∈ (Peano : Theory ℒₒᵣ).Δ₁Class →
      QuantifierBoundedCode ℒₒᵣ (levelCode n) p →
      ∀ free : V, Arithmetic.Seq free →
        SigmaTrue (n + 1) 0 free p) :
    RestrictedConsistent (V := V) Peano (levelCode n) := by
  apply restrictedConsistent_of_laws Peano
      (sigmaTrue_succ_laws (V := V) n) hAx
  simpa [Nat.add_assoc] using
    (derivationSequentTrue_sigmaTrue_definable (V := V) n)

end LeanProofs.BoundedPAConsistency.FixedLevelSoundness
