import BoundedPAConsistency.AbstractSoundness
import BoundedPAConsistency.FixedLevelTruthDefinability

/-!
# Definability of the fixed-level sequent invariant

For an external bound `n`, the eventual uniform satisfaction predicate is
`SigmaTrue (n + 1)`.  It is Sigma at level `n + 2`.  Saying that every coded
free-variable assignment makes some member of a sequent true adds one outer
universal block, so the invariant is Pi at level `n + 3`.

This finite increase is harmless but must be explicit: the internal
derivation may be nonstandard, and its fixed-point induction is performed
inside the ambient model of PA using this represented invariant.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelSequentDefinability

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.AbstractSoundness
open LeanProofs.BoundedPAConsistency.FixedLevelTruth

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

omit [V↓[ℒₒᵣ] ⊧* Peano] in
/-- A Sigma definition can be presented in both polarities one level higher.
This local bridge lets the assignment implication be assembled without
silently asking the definability synthesizer to change polarity. -/
private lemma sigma_definable_delta_succ
    {P : (Fin k → V) → Prop} {m : ℕ}
    (h : Polarity.sigma-[m].Definable P) :
    SigmaPiDelta.delta-[m + 1].Definable P := by
  rcases h with ⟨φ, hφ⟩
  apply HierarchySymbol.Definable.of_sigma_of_pi
      (Γ := SigmaPiDelta.delta)
  · exact ⟨HierarchySymbol.Semiformula.mkSigma φ.val
        (φ.sigma_prop.accum Polarity.sigma), by
      intro v
      simpa using hφ.iff (v := v)⟩
  · exact ⟨HierarchySymbol.Semiformula.mkPi φ.val
        (φ.sigma_prop.accum Polarity.pi), by
      intro v
      simpa using hφ.iff (v := v)⟩

/-- The assignment-uniform sequent invariant for `SigmaTrue (n + 1)` is
represented by a Pi formula at the next hierarchy level. -/
theorem sequentTrue_sigmaTrue_definable (n : ℕ) :
    Polarity.pi-[n + 3]-Predicate
      (fun s : V ↦ SequentTrue (SigmaTrue (V := V) (n + 1)) s) := by
  letI : SigmaPiDelta.delta-[n + 3]-Relation₃
      (SigmaTrue (V := V) (n + 1)) := by
    have h : Polarity.sigma-[n + 2]-Relation₃
        (SigmaTrue (V := V) (n + 1)) :=
      sigmaTrue_definable (n + 1)
    change SigmaPiDelta.delta-[(n + 2) + 1]-Relation₃
      (SigmaTrue (V := V) (n + 1))
    exact sigma_definable_delta_succ h
  have hInner : SigmaPiDelta.delta-[n + 3].Definable
      (fun v : Fin 2 → V ↦
        ∃ p < v 1, p ∈ v 1 ∧ SigmaTrue (n + 1) 0 (v 0) p) := by
    have hConj : SigmaPiDelta.delta-[n + 3].Definable
        (fun w : Fin 3 → V ↦
          w 0 ∈ w 2 ∧ SigmaTrue (n + 1) 0 (w 1) (w 0)) := by
      apply HierarchySymbol.Definable.and
      · definability
      · apply HierarchySymbol.DefinableRel₃.comp
          (show SigmaPiDelta.delta-[n + 3]-Relation₃
              (SigmaTrue (V := V) (n + 1)) from inferInstance)
        · simp
        · simp
        · simp
    apply HierarchySymbol.Definable.bexs_lt
        (f := fun v : Fin 2 → V ↦ v 1)
    · definability
    · exact hConj
  have hBody : Polarity.pi-[n + 3].Definable
      (fun v : Fin 2 → V ↦ Arithmetic.Seq (v 0) →
        ∃ p < v 1, p ∈ v 1 ∧ SigmaTrue (n + 1) 0 (v 0) p) := by
    apply HierarchySymbol.Definable.imp
    · exact HierarchySymbol.Definable.of_deltaOne (by definability)
    · exact HierarchySymbol.Definable.of_delta hInner
  have hBounded : Polarity.pi-[n + 3]-Predicate
      (fun s : V ↦ ∀ free : V, Arithmetic.Seq free →
        ∃ p < s, p ∈ s ∧ SigmaTrue (n + 1) 0 free p) := by
    exact HierarchySymbol.Definable.all hBody
  exact hBounded.of_iff (by
    intro v
    constructor
    · intro h free hfree
      rcases h free hfree with ⟨p, hp, htrue⟩
      exact ⟨p, lt_of_mem hp, hp, htrue⟩
    · intro h free hfree
      rcases h free hfree with ⟨p, _, hp, htrue⟩
      exact ⟨p, hp, htrue⟩)

/-- Composition with the coded derivation's conclusion projection gives the
exact predicate consumed by `AbstractSoundness.restrictedDerivation_sound`. -/
theorem derivationSequentTrue_sigmaTrue_definable (n : ℕ) :
    Polarity.pi-[n + 3]-Predicate
      (fun d : V ↦
        SequentTrue (SigmaTrue (V := V) (n + 1)) (fstIdx d)) := by
  apply HierarchySymbol.DefinablePred.comp
    (sequentTrue_sigmaTrue_definable (V := V) n)
  definability

end LeanProofs.BoundedPAConsistency.FixedLevelSequentDefinability
