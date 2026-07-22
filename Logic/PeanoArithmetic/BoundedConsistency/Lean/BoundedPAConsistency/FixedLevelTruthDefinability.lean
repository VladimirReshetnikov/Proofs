import BoundedPAConsistency.FixedLevelTruth

/-!
# Definability of externally indexed partial truth

The truth predicates in `FixedLevelTruth` recurse in Lean only on the external
standard level.  This file performs the matching metatheoretic recursion on
their representing formulas.  At level `n`, `SigmaTrue n` is represented by a
`Sigma_(n+1)` formula and `PiTrue n` by a `Pi_(n+1)` formula.

The one-level increase in the successor step is genuine: validity of a
certificate is Pi-oriented at the preceding level, while existence of the
certificate is an unbounded existential quantifier.  All quantifiers internal
to one certificate record are bounded and therefore do not increase the
hierarchy level.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelTruth

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

private abbrev SigmaLevel (n : ℕ) : HierarchySymbol :=
  ⟨SigmaPiDelta.sigma, n⟩

private abbrev PiLevel (n : ℕ) : HierarchySymbol :=
  ⟨SigmaPiDelta.pi, n⟩

/-! ## A small hierarchy-promotion lemma

Foundation exposes promotion at the syntactic `Hierarchy` layer.  This local
wrapper is the one alternation used below: a Pi-level certificate check is a
Sigma formula one level higher.  Keeping it local avoids a global instance
that could compete with Foundation's hierarchy instances.
-/

omit [V↓[ℒₒᵣ] ⊧* ISigma 1] in
private lemma pi_definable_accum {P : (Fin k → V) → Prop} {m : ℕ}
    (hP : (PiLevel m).Definable P) : (SigmaLevel (m + 1)).Definable P := by
  rcases hP with ⟨φ, hφ⟩
  exact ⟨HierarchySymbol.Semiformula.mkSigma φ.val
      (φ.pi_prop.accum Polarity.sigma), by
    intro v
    simpa using hφ.iff (v := v)⟩

/-! ## Definable record operations -/

noncomputable def truthRecordDef : HierarchySymbol.sigmaZero.Semisentence 5 :=
  .mkSigma
    “y bound free p witness.
      ∃ state <⁺ y,
        !pair₃Def state bound free p ∧ !pairDef y state witness”

noncomputable def recordBoundDef : HierarchySymbol.sigmaZero.Semisentence 2 :=
  .mkSigma
    “y r. ∃ state <⁺ r, !pi₁Def state r ∧ !pi₁Def y state”

noncomputable def recordFreeDef : HierarchySymbol.sigmaZero.Semisentence 2 :=
  .mkSigma
    “y r. ∃ state <⁺ r, !pi₁Def state r ∧
      ∃ tail <⁺ state, !pi₂Def tail state ∧ !pi₁Def y tail”

noncomputable def recordFormulaDef : HierarchySymbol.sigmaZero.Semisentence 2 :=
  .mkSigma
    “y r. ∃ state <⁺ r, !pi₁Def state r ∧
      ∃ tail <⁺ state, !pi₂Def tail state ∧ !pi₂Def y tail”

noncomputable def hasTruthStateDef : HierarchySymbol.sigmaZero.Semisentence 4 :=
  .mkSigma
    “C bound free p. ∃ witness < C, ∃ record < C,
      !truthRecordDef record bound free p witness ∧ record ∈ C”

instance truthState.defined :
    HierarchySymbol.DefinedFunction₃ (V := V) HierarchySymbol.sigmaZero
      (truthState : V → V → V → V) pair₃Def :=
  .mk fun v ↦ by
    simp [truthState, pair₃Def]
    intro h
    rw [h]
    simp

instance truthState.definable (G : HierarchySymbol) :
    G.DefinableFunction₃ (V := V) (truthState : V → V → V → V) := by
  exact truthState.defined.to_definable₀

instance truthRecord.defined :
    HierarchySymbol.DefinedFunction₄ (V := V) HierarchySymbol.sigmaZero
      (truthRecord : V → V → V → V → V) truthRecordDef :=
  .mk fun v ↦ by
    simp [truthRecordDef, truthRecord, truthState]
    intro h
    rw [h]
    simp

instance truthRecord.definable (G : HierarchySymbol) :
    G.DefinableFunction₄ (V := V)
      (truthRecord : V → V → V → V → V) := by
  exact truthRecord.defined.to_definable₀

instance recordBound.defined :
    HierarchySymbol.DefinedFunction₁ (V := V) HierarchySymbol.sigmaZero
      (recordBound : V → V) recordBoundDef := .mk fun v ↦ by
  simp [recordBoundDef, recordBound]

instance recordBound.definable (G : HierarchySymbol) :
    G.DefinableFunction₁ (V := V) (recordBound : V → V) := by
  exact recordBound.defined.to_definable₀

instance recordFree.defined :
    HierarchySymbol.DefinedFunction₁ (V := V) HierarchySymbol.sigmaZero
      (recordFree : V → V) recordFreeDef := .mk fun v ↦ by
  simp [recordFreeDef, recordFree]

instance recordFree.definable (G : HierarchySymbol) :
    G.DefinableFunction₁ (V := V) (recordFree : V → V) := by
  exact recordFree.defined.to_definable₀

instance recordFormula.defined :
    HierarchySymbol.DefinedFunction₁ (V := V) HierarchySymbol.sigmaZero
      (recordFormula : V → V) recordFormulaDef := .mk fun v ↦ by
  simp [recordFormulaDef, recordFormula]

instance recordFormula.definable (G : HierarchySymbol) :
    G.DefinableFunction₁ (V := V) (recordFormula : V → V) := by
  exact recordFormula.defined.to_definable₀

instance recordWitness.defined :
    HierarchySymbol.DefinedFunction₁ (V := V) HierarchySymbol.sigmaZero
      (recordWitness : V → V) pi₂Def := .mk fun v ↦ by
  simp [pi₂Def, recordWitness]
  constructor
  · rintro ⟨a, _, e⟩
    simp [show v 1 = pair a (v 0) from e]
  · intro h
    exact ⟨π₁ (v 1), by simp, by simp [h]⟩

instance recordWitness.definable (G : HierarchySymbol) :
    G.DefinableFunction₁ (V := V) (recordWitness : V → V) := by
  exact recordWitness.defined.to_definable₀

instance HasTruthState.defined :
    HierarchySymbol.DefinedRel₄ (V := V) HierarchySymbol.sigmaZero
      (HasTruthState : V → V → V → V → Prop) hasTruthStateDef :=
  .mk fun v ↦ by
    simp [hasTruthStateDef, HasTruthState]
    constructor
    · rintro ⟨w, hw, _, hmem⟩
      exact ⟨w, hw, hmem⟩
    · rintro ⟨w, hw, hmem⟩
      exact ⟨w, hw, lt_of_mem hmem, hmem⟩

instance HasTruthState.definable (G : HierarchySymbol) :
    G.DefinableRel₄ (V := V) (HasTruthState : V → V → V → V → Prop) := by
  exact HasTruthState.defined.to_definable₀

/-! ## Oriented domains at every positive hierarchy level -/

private lemma isSigmaCode_deltaOne :
    HierarchySymbol.deltaOne.DefinableRel (V := V) (IsSigmaCode ℒₒᵣ) := by
  unfold IsSigmaCode
  definability

private lemma isPiCode_deltaOne :
    HierarchySymbol.deltaOne.DefinableRel (V := V) (IsPiCode ℒₒᵣ) := by
  unfold IsPiCode
  definability

private lemma isSigmaCode_definable (G : Polarity) (m : ℕ) :
    G-[m + 1].DefinableRel (V := V) (IsSigmaCode ℒₒᵣ) :=
  HierarchySymbol.Definable.of_deltaOne isSigmaCode_deltaOne

private lemma isPiCode_definable (G : Polarity) (m : ℕ) :
    G-[m + 1].DefinableRel (V := V) (IsPiCode ℒₒᵣ) :=
  HierarchySymbol.Definable.of_deltaOne isPiCode_deltaOne

/-! ## The local certificate relations -/

theorem lowerPiTrue_definable {lowerSigma : V → V → V → Prop}
    {n : ℕ}
    (hLower : (SigmaLevel (n + 1)).DefinableRel₃ (V := V) lowerSigma) :
    (PiLevel (n + 1)).DefinableRel₄ (V := V)
      (LowerPiTrue lowerSigma) := by
  letI : (SigmaLevel (n + 1)).DefinableRel₃ (V := V) lowerSigma := hLower
  letI : (PiLevel (n + 1)).DefinableRel (V := V) (IsPiCode ℒₒᵣ) :=
    isPiCode_definable Polarity.pi n
  have hCode : (PiLevel (n + 1)).Definable (V := V)
      (fun v : Fin 4 → V ↦ IsPiCode ℒₒᵣ (v 0) (v 3)) :=
    HierarchySymbol.Definable.retraction
      (isPiCode_definable Polarity.pi n) ![0, 3]
  have hSigma : (SigmaLevel (n + 1)).Definable (V := V)
      (fun v : Fin 4 → V ↦ lowerSigma (v 1) (v 2) (neg ℒₒᵣ (v 3))) := by
    apply HierarchySymbol.DefinableRel₃.comp hLower
    · simp
    · simp
    · definability
  exact (hCode.and hSigma.notSigma).of_iff (by
    intro v
    simp [LowerPiTrue])

theorem sigmaRecordValid_definable
    {lowerSigma : V → V → V → Prop} {n : ℕ}
    (hLower : (SigmaLevel (n + 1)).DefinableRel₃ (V := V) lowerSigma) :
    (PiLevel (n + 1)).DefinableRel₄ (V := V)
      (SigmaRecordValid lowerSigma) := by
  letI : (SigmaLevel (n + 1)).DefinableRel₃ (V := V) lowerSigma := hLower
  letI : (PiLevel (n + 1)).DefinableRel₄ (V := V) (LowerPiTrue lowerSigma) :=
    lowerPiTrue_definable hLower
  letI : (PiLevel (n + 1)).DefinableRel (V := V) (IsSigmaCode ℒₒᵣ) :=
    isSigmaCode_definable Polarity.pi n
  unfold SigmaRecordValid
  definability

/-! ## External recursion on the represented truth formulas -/

theorem sigmaTrue_definable : ∀ n : ℕ,
    (SigmaLevel (n + 1)).DefinableRel₃ (V := V) (SigmaTrue n)
  | 0 => by
      change HierarchySymbol.sigmaOne.DefinableRel₃ (V := V) QFTrue
      exact QFTrue.definable
  | n + 1 => by
      have ih : (SigmaLevel (n + 1)).DefinableRel₃ (V := V) (SigmaTrue n) :=
        sigmaTrue_definable n
      have hvalidPi : (PiLevel (n + 1)).DefinableRel₄ (V := V)
          (SigmaRecordValid (SigmaTrue n)) :=
        sigmaRecordValid_definable ih
      have hvalidSigma : (SigmaLevel ((n + 1) + 1)).DefinableRel₄ (V := V)
          (SigmaRecordValid (SigmaTrue n)) :=
        pi_definable_accum hvalidPi
      change (SigmaLevel ((n + 1) + 1)).DefinableRel₃ (V := V)
        (fun bound free p ↦
          ∃ C,
            HasTruthState C bound free p ∧
            ∀ r ∈ C,
              SigmaRecordValid (SigmaTrue n)
                (levelCode n) (levelCode (n + 1)) C r)
      have hRecord : (SigmaLevel ((n + 1) + 1)).Definable (V := V)
          (fun v : Fin 5 → V ↦
            SigmaRecordValid (SigmaTrue n)
              (levelCode n) (levelCode (n + 1)) (v 1) (v 0)) := by
        apply HierarchySymbol.DefinableRel₄.comp hvalidSigma
        · simp
        · simp
        · simp
        · simp
      have hAll : (SigmaLevel ((n + 1) + 1)).Definable (V := V)
          (fun v : Fin 4 → V ↦
            ∀ r ∈ v 0,
              SigmaRecordValid (SigmaTrue n)
                (levelCode n) (levelCode (n + 1)) (v 0) r) := by
        exact HierarchySymbol.Definable.ball_mem Polarity.sigma (n + 1)
          (by simp) hRecord
      have hState : (SigmaLevel ((n + 1) + 1)).Definable (V := V)
          (fun v : Fin 4 → V ↦
            HasTruthState (v 0) (v 1) (v 2) (v 3)) := by
        exact HasTruthState.definable _
      have hBody : (SigmaLevel ((n + 1) + 1)).Definable (V := V)
          (fun v : Fin 4 → V ↦
            HasTruthState (v 0) (v 1) (v 2) (v 3) ∧
            ∀ r ∈ v 0,
              SigmaRecordValid (SigmaTrue n)
                (levelCode n) (levelCode (n + 1)) (v 0) r) :=
        hState.and hAll
      exact HierarchySymbol.Definable.exs hBody

theorem piTrue_definable (n : ℕ) :
    (PiLevel (n + 1)).DefinableRel₃ (V := V) (PiTrue n) := by
  have hsigma : (SigmaLevel (n + 1)).DefinableRel₃ (V := V) (SigmaTrue n) :=
    sigmaTrue_definable n
  letI : (SigmaLevel (n + 1)).DefinableRel₃ (V := V) (SigmaTrue n) := hsigma
  letI : (PiLevel (n + 1)).DefinableRel (V := V) (IsPiCode ℒₒᵣ) :=
    isPiCode_definable Polarity.pi n
  have hCode : (PiLevel (n + 1)).Definable (V := V)
      (fun v : Fin 3 → V ↦ IsPiCode ℒₒᵣ (levelCode n) (v 2)) := by
    apply HierarchySymbol.DefinableRel.comp
      (isPiCode_definable Polarity.pi n)
    · simp
    · simp
  have hSigma : (SigmaLevel (n + 1)).Definable (V := V)
      (fun v : Fin 3 → V ↦ SigmaTrue n (v 0) (v 1) (neg ℒₒᵣ (v 2))) := by
    apply HierarchySymbol.DefinableRel₃.comp hsigma
    · simp
    · simp
    · definability
  exact (hCode.and hSigma.notSigma).of_iff (by
    intro v
    simp [PiTrue])

end LeanProofs.BoundedPAConsistency.FixedLevelTruth
