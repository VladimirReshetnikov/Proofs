import BoundedPAConsistency.FixedLevelSoundness
import BoundedPAConsistency.FixedLevelPAMinusAxioms
import BoundedPAConsistency.FixedLevelPAInductionAxioms

/-!
# Fixed-level PA axiom soundness and bounded consistency

This is the final theory-specific assembly.  PA's represented axiom
recognizer splits into the finite `PA⁻` recognizer and the universal closure
of an induction instance.  The preceding modules prove fixed-level truth for
those two branches separately, including their nonstandard codes.  Combining
them with abstract derivation soundness gives restricted consistency in every
model of PA.  Arithmetic completeness then turns that model-uniform result
into an actual PA proof for each external hierarchy bound.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelPAAxioms

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.FixedLevelSoundness
open LeanProofs.BoundedPAConsistency.FixedLevelPAMinusAxioms
open LeanProofs.BoundedPAConsistency.FixedLevelPAInductionAxioms
open LeanProofs.BoundedPAConsistency.QuantifierFreePAAxioms

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- Every code accepted by PA's internal axiom recognizer and bounded by the
external quantifier-group level `n` is true in the unified successor partial
truth predicate.  The split is semantic in the ambient PA model, so it also
covers nonstandard recognizer witnesses and nonstandard formula codes. -/
theorem sigmaTrue_succ_of_mem_pa_delta1Class (n : ℕ) {p free : V}
    (hp : p ∈ (Peano : Theory ℒₒᵣ).Δ₁Class)
    (hbounded : QuantifierBoundedCode ℒₒᵣ
      (levelCode (V := V) n) p)
    (hfree : Arithmetic.Seq free) :
    SigmaTrue (n + 1) 0 free p := by
  rcases mem_pa_delta1Class_iff.mp hp with hminus | hind
  · exact sigmaTrue_succ_of_mem_peanoMinus_delta1Class_of_seq
      n hfree hminus hbounded
  · exact sigmaTrue_succ_of_inductionUnivR n hind hbounded hfree

/-- Every model of PA satisfies consistency against internally coded proofs
whose formulas have at most the external number `n` of quantifier groups. -/
theorem restrictedConsistent_pa_fixedLevel (n : ℕ) :
    RestrictedConsistent (V := V) Peano (levelCode n) := by
  apply restrictedConsistent_pa_of_sigmaTrue_axioms n
  intro p hp hbounded free hfree
  exact sigmaTrue_succ_of_mem_pa_delta1Class
    n hp hbounded hfree

/-- For each metatheoretic natural number `n`, PA proves its consistency with
respect to proofs all of whose formulas contain at most `n` quantifier
groups.  This is a family of PA theorems indexed externally by `n`; it does
not assert one internal sentence quantifying over every bound. -/
theorem pa_proves_restrictedConsistency (n : ℕ) :
    Peano ⊢
      (paRestrictedConsistencySentence n : ArithmeticSentence) := by
  apply LO.FirstOrder.Arithmetic.complete.{0} Peano _
  intro M _ _
  simpa [models_iff] using
    (eval_paRestrictedConsistencySentence_iff (V := M) n).mpr
      (restrictedConsistent_pa_fixedLevel (V := M) n)

end LeanProofs.BoundedPAConsistency.FixedLevelPAAxioms
