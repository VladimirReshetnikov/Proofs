import BoundedPAConsistency.OrientedHierarchy
import BoundedPAConsistency.QuantifierFreeTransport

/-!
# Externally indexed partial truth on nonstandard formula codes

This module begins the positive-level partial-truth construction.  The level
is a Lean natural number, never a model element quantified over by one
arithmetic formula.  At level zero we reuse `QFTrue`.  At a successor level,
Sigma truth is witnessed by one internally finite HFS certificate which
traverses conjunctions, chooses a true disjunct, and records witnesses for
same-polarity existential quantifiers.  A quantifier-free formula or an
opposite universal head is a leaf; universal truth is the complement of
lower-level Sigma truth of its coded negation.

The record set is essential for nonstandard syntax.  Recursing in Lean over a
decoded formula would cover only standard codes, whereas an HFS certificate
can have nonstandard internal size in a nonstandard model of arithmetic.
Every child record contains a strictly smaller formula code, so later Tarski
proofs can validate certificates by model-internal induction.

This file establishes the semantic data structure.  Its compositional and
definability theorems are developed separately so that the certificate format
remains explicit and independently auditable.
-/

namespace LeanProofs.BoundedPAConsistency.FixedLevelTruth

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.OrientedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Interpret an external hierarchy level in the current arithmetic model. -/
noncomputable abbrev levelCode (n : ℕ) : V :=
  ORingStructure.numeral n

/-! ## Certificate records

A state is `pair₃ bound free formula`.  A record is the pair of a state and a
witness.  The witness is used only at an existential node; keeping one fixed
record format makes all child references bounded membership tests in a single
HFS set.
-/

noncomputable def truthState (bound free p : V) : V :=
  ⟪bound, free, p⟫

noncomputable def truthRecord (bound free p witness : V) : V :=
  ⟪truthState bound free p, witness⟫

noncomputable def recordBound (r : V) : V :=
  π₁ (π₁ r)

noncomputable def recordFree (r : V) : V :=
  π₁ (π₂ (π₁ r))

noncomputable def recordFormula (r : V) : V :=
  π₂ (π₂ (π₁ r))

noncomputable def recordWitness (r : V) : V :=
  π₂ r

@[simp] theorem recordBound_truthRecord (bound free p witness : V) :
    recordBound (truthRecord bound free p witness) = bound := by
  simp [recordBound, truthRecord, truthState]

@[simp] theorem recordFree_truthRecord (bound free p witness : V) :
    recordFree (truthRecord bound free p witness) = free := by
  simp [recordFree, truthRecord, truthState]

@[simp] theorem recordFormula_truthRecord (bound free p witness : V) :
    recordFormula (truthRecord bound free p witness) = p := by
  simp [recordFormula, truthRecord, truthState]

@[simp] theorem recordWitness_truthRecord (bound free p witness : V) :
    recordWitness (truthRecord bound free p witness) = witness := by
  simp [recordWitness, truthRecord]

/-- The certificate contains some record for the displayed semantic state.

The witness is explicitly bounded by `C`.  This does not constrain genuine
records: membership of the paired record in the HFS set already implies that
each projection is smaller than `C`.  The bound keeps this relation at the
bounded/Delta-one part of the eventual truth formula. -/
def HasTruthState (C bound free p : V) : Prop :=
  ∃ witness < C, truthRecord bound free p witness ∈ C

/-- Truth of a lower Pi-oriented leaf, parameterized by the already
constructed lower Sigma predicate. -/
def LowerPiTrue
    (lowerSigma : V → V → V → Prop)
    (lowerLevel bound free p : V) : Prop :=
  IsPiCode ℒₒᵣ lowerLevel p ∧
    ¬lowerSigma bound free (neg ℒₒᵣ p)

/-- Local closure condition for one successor-level certificate record.

Only the Sigma skeleton is traversed at this level.  Quantifier-free formulas
use the existing evaluator, while an opposite universal head terminates at
lower Pi truth.  Conjunction stores both children, disjunction stores one
chosen child, and an existential record stores its witness in
`recordWitness` and extends the de Bruijn environment.
-/
def SigmaRecordValid
    (lowerSigma : V → V → V → Prop)
    (lowerLevel upperLevel C r : V) : Prop :=
  let bound := recordBound r
  let free := recordFree r
  let p := recordFormula r
  IsSigmaCode ℒₒᵣ upperLevel p ∧
    (QFTrue bound free p ∨
     (∃ p₁ < p, ∃ p₂ < p,
        p = p₁ ^⋏ p₂ ∧
        HasTruthState C bound free p₁ ∧
        HasTruthState C bound free p₂) ∨
     (∃ p₁ < p, ∃ p₂ < p,
        p = p₁ ^⋎ p₂ ∧
        (HasTruthState C bound free p₁ ∨
         HasTruthState C bound free p₂)) ∨
     (∃ q < p,
        p = ^∃ q ∧
        HasTruthState C (bound ⁀' recordWitness r) free q) ∨
     (∃ q < p,
        p = ^∀ q ∧
        LowerPiTrue lowerSigma lowerLevel bound free p))

/-! ## External recursion on the truth level -/

/-- Sigma-oriented partial truth at an externally fixed hierarchy level.

The successor clause is intentionally a certificate predicate rather than a
host recursion on `p`.  Therefore `p`, `C`, and all records may be nonstandard
elements of the ambient model.
-/
noncomputable def SigmaTrue : ℕ → V → V → V → Prop
  | 0 => QFTrue
  | n + 1 => fun bound free p ↦
      ∃ C,
        HasTruthState C bound free p ∧
        ∀ r ∈ C,
          SigmaRecordValid (SigmaTrue n)
            (levelCode n) (levelCode (n + 1)) C r

/-- Pi-oriented truth is the complementary lower-polarity predicate on the
coded negation.  The explicit domain conjunct makes the definition total and
prevents claims outside the advertised fixed hierarchy level. -/
noncomputable def PiTrue (n : ℕ) (bound free p : V) : Prop :=
  IsPiCode ℒₒᵣ (levelCode n) p ∧
    ¬SigmaTrue n bound free (neg ℒₒᵣ p)

@[simp] theorem sigmaTrue_zero {bound free p : V} :
    SigmaTrue 0 bound free p ↔ QFTrue bound free p := by
  rfl

@[simp] theorem sigmaTrue_succ {n : ℕ} {bound free p : V} :
    SigmaTrue (n + 1) bound free p ↔
      ∃ C,
        HasTruthState C bound free p ∧
        ∀ r ∈ C,
          SigmaRecordValid (SigmaTrue n)
            (levelCode n) (levelCode (n + 1)) C r := by
  rfl

@[simp] theorem piTrue_iff {n : ℕ} {bound free p : V} :
    PiTrue n bound free p ↔
      IsPiCode ℒₒᵣ (levelCode n) p ∧
        ¬SigmaTrue n bound free (neg ℒₒᵣ p) := by
  rfl

lemma SigmaRecordValid.domain
    {lowerSigma : V → V → V → Prop}
    {lowerLevel upperLevel C r : V}
    (h : SigmaRecordValid lowerSigma lowerLevel upperLevel C r) :
    IsSigmaCode ℒₒᵣ upperLevel (recordFormula r) := by
  simpa [SigmaRecordValid] using h.1

/-- Every positive-level Sigma truth witness advertises the correct oriented
domain, including for nonstandard formula codes. -/
theorem SigmaTrue.domain_succ {n : ℕ} {bound free p : V}
    (h : SigmaTrue (n + 1) bound free p) :
    IsSigmaCode ℒₒᵣ (levelCode (n + 1)) p := by
  rcases h with ⟨C, ⟨w, hwC, hrecord⟩, hvalid⟩
  have hr := hvalid (truthRecord bound free p w) hrecord
  simpa using hr.domain

/-- Pi truth carries its oriented domain definitionally. -/
theorem PiTrue.domain {n : ℕ} {bound free p : V}
    (h : PiTrue n bound free p) :
    IsPiCode ℒₒᵣ (levelCode n) p :=
  h.1

end LeanProofs.BoundedPAConsistency.FixedLevelTruth
