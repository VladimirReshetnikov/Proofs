import BoundedPAConsistency.FixedLevelTruthDefinability

/-! Axiom and interface audit for fixed-level partial-truth definability. -/

namespace LeanProofs.BoundedPAConsistency.FixedLevelTruth

open LO FirstOrder
open LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

example (G : HierarchySymbol) :
    G.DefinableFunction₃ (V := V) (truthState : V → V → V → V) :=
  inferInstance

example (G : HierarchySymbol) :
    G.DefinableFunction₄ (V := V)
      (truthRecord : V → V → V → V → V) :=
  inferInstance

example (G : HierarchySymbol) :
    G.DefinableFunction₁ (V := V) (recordBound : V → V) :=
  inferInstance

example (G : HierarchySymbol) :
    G.DefinableFunction₁ (V := V) (recordFree : V → V) :=
  inferInstance

example (G : HierarchySymbol) :
    G.DefinableFunction₁ (V := V) (recordFormula : V → V) :=
  inferInstance

example (G : HierarchySymbol) :
    G.DefinableFunction₁ (V := V) (recordWitness : V → V) :=
  inferInstance

example (G : HierarchySymbol) :
    G.DefinableRel₄ (V := V)
      (HasTruthState : V → V → V → V → Prop) :=
  inferInstance

example {lowerSigma : V → V → V → Prop} {n : ℕ}
    (hLower : (HierarchySymbol.mk SigmaPiDelta.sigma (n + 1)).DefinableRel₃
      (V := V) lowerSigma) :
    (HierarchySymbol.mk SigmaPiDelta.pi (n + 1)).DefinableRel₄
      (V := V) (LowerPiTrue lowerSigma) :=
  lowerPiTrue_definable hLower

example {lowerSigma : V → V → V → Prop} {n : ℕ}
    (hLower : (HierarchySymbol.mk SigmaPiDelta.sigma (n + 1)).DefinableRel₃
      (V := V) lowerSigma) :
    (HierarchySymbol.mk SigmaPiDelta.pi (n + 1)).DefinableRel₄
      (V := V) (SigmaRecordValid lowerSigma) :=
  sigmaRecordValid_definable hLower

example (n : ℕ) :
    (HierarchySymbol.mk Polarity.sigma (n + 1)).DefinableRel₃
      (V := V) (SigmaTrue n) :=
  sigmaTrue_definable n

example (n : ℕ) :
    (HierarchySymbol.mk Polarity.pi (n + 1)).DefinableRel₃
      (V := V) (PiTrue n) :=
  piTrue_definable n

#print axioms truthState.definable
#print axioms truthRecord.definable
#print axioms recordBound.definable
#print axioms recordFree.definable
#print axioms recordFormula.definable
#print axioms recordWitness.definable
#print axioms HasTruthState.definable
#print axioms lowerPiTrue_definable
#print axioms sigmaRecordValid_definable
#print axioms sigmaTrue_definable
#print axioms piTrue_definable

end LeanProofs.BoundedPAConsistency.FixedLevelTruth
