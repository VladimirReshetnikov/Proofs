import BoundedPAConsistency.RestrictedDerivation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-!
# The internal bounded-proof and consistency sentences

`RestrictedDerivation T n d` checks the hierarchy bound at every node of the
model-internal derivation coded by `d`.  This file packages that checker into
the usual endpoint predicates:

* `RestrictedProof T n d p`: `d` is a restricted derivation of the singleton
  sequent containing the formula code `p`;
* `RestrictedProvable T n p`: some such `d` exists;
* `RestrictedConsistent T n`: falsity has no such proof.

All semantic equivalences below hold in an arbitrary, possibly nonstandard,
model of `I Sigma 1`.  In particular, the quantified proof code in the
consistency formula ranges over every model element, not merely codes coming
from standard Lean proof trees.

The final object-level theorem still requires a bounded-reflection argument:
one must prove the fixed external numeral instance of
`paRestrictedConsistencySentence` in PA.  This file deliberately does not
replace that missing argument with standard-model consistency.
-/

namespace LeanProofs.BoundedPAConsistency

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable (T : Theory L) [Theory.Δ₁ T]

/-! ## Restricted proof and provability -/

/-- A restricted derivation whose concluding sequent is exactly `{p}`. -/
def RestrictedProof (n d p : V) : Prop :=
  fstIdx d = {p} ∧ RestrictedDerivation T n d

/-- A Delta-one formula for `RestrictedProof`, with variables ordered as
`(n, d, p)`.  The two halves use the two presentations of the restricted
fixed point and the canonical HFS singleton graph. -/
noncomputable def restrictedProofDef :
    HierarchySymbol.deltaOne.Semisentence 3 := .mkDelta
  (.mkSigma
    “n d p. ∃ s, !insertDef s p 0 ∧ !fstIdxDef s d ∧
      !(restrictedDerivationDef T).sigma n d”)
  (.mkPi
    “n d p. ∀ s, !insertDef s p 0 → !fstIdxDef s d ∧
      !(restrictedDerivationDef T).pi n d”)

instance RestrictedProof.defined :
    HierarchySymbol.DefinedRel₃ (V := V) HierarchySymbol.deltaOne
      (RestrictedProof T) (restrictedProofDef T) := .mk ⟨by
  intro v
  simp [restrictedProofDef]
, by
  intro v
  simp [restrictedProofDef, RestrictedProof, eq_comm]
  intro _
  rw [singleton_eq_insert, emptyset_def]⟩

instance RestrictedProof.definable :
    HierarchySymbol.DefinableRel₃ (V := V) HierarchySymbol.deltaOne
      (RestrictedProof T) :=
  (RestrictedProof.defined (V := V) T).to_definable

/-- Provability by an all-occurrences bounded derivation. -/
def RestrictedProvable (n p : V) : Prop :=
  ∃ d, RestrictedProof T n d p

/-- A Sigma-one formula for restricted provability. -/
noncomputable def restrictedProvableDef :
    HierarchySymbol.sigmaOne.Semisentence 2 := .mkSigma
  “n p. ∃ d, !(restrictedProofDef T).sigma n d p”

instance RestrictedProvable.defined :
    HierarchySymbol.DefinedRel (V := V) HierarchySymbol.sigmaOne
      (RestrictedProvable T) (restrictedProvableDef T) := .mk fun v ↦ by
  simp [restrictedProvableDef, RestrictedProvable]

instance RestrictedProvable.definable :
    HierarchySymbol.DefinableRel (V := V) HierarchySymbol.sigmaOne
      (RestrictedProvable T) :=
  (RestrictedProvable.defined (V := V) T).to_definable

/-! ## Consistency and its fixed external instances -/

/-- No restricted proof of the internally coded falsum exists. -/
def RestrictedConsistent (n : V) : Prop :=
  ¬RestrictedProvable T n (qqFalsum : V)

/-- A Pi-one formula defining `RestrictedConsistent`.

`qqFalsumDef` is used instead of smuggling a semantic model element into the
syntax.  Its functionality reduces the displayed universal implication to
the intended single code `qqFalsum` in every model. -/
noncomputable def restrictedConsistentDef :
    HierarchySymbol.piOne.Semisentence 1 := .mkPi
  “n. ∀ bot, !qqFalsumDef bot → ¬!(restrictedProvableDef T) n bot”

instance RestrictedConsistent.defined :
    HierarchySymbol.DefinedPred (V := V) HierarchySymbol.piOne
      (RestrictedConsistent T) (restrictedConsistentDef T) := .mk fun v ↦ by
  simp [restrictedConsistentDef, RestrictedConsistent]

instance RestrictedConsistent.definable :
    HierarchySymbol.DefinablePred (V := V) HierarchySymbol.piOne
      (RestrictedConsistent T) :=
  (RestrictedConsistent.defined (V := V) T).to_definable

/-- The arithmetic sentence for one *external* natural-number bound.

This is a metatheoretic family of sentences.  It is intentionally not a
single sentence quantifying internally over all hierarchy levels. -/
noncomputable def restrictedConsistencySentence (n : ℕ) :
    HierarchySymbol.piOne.Sentence := .mkPi
  “!(restrictedConsistentDef T) !n”

@[simp] theorem eval_restrictedConsistencySentence_iff (n : ℕ) :
    ((restrictedConsistencySentence T n : ArithmeticSentence).Evalb
      (M := V) ![]) ↔
      RestrictedConsistent T (ORingStructure.numeral n : V) := by
  simp [restrictedConsistencySentence]

/-! ## Sanity checks and erasure -/

/-- Forgetting the hierarchy checks turns a restricted proof into the
ordinary Foundation proof predicate, even for a nonstandard proof code. -/
theorem RestrictedProof.erase {n d p : V}
    (h : RestrictedProof T n d p) : Proof T d p :=
  ⟨h.1, LeanProofs.BoundedPAConsistency.erase T h.2⟩

/-- Restricted provability is a subrelation of ordinary provability. -/
theorem RestrictedProvable.erase {n p : V}
    (h : RestrictedProvable T n p) : Provable T p := by
  rcases h with ⟨d, hd⟩
  exact ⟨d, hd.erase T⟩

/-- Ordinary model-internal consistency implies every restricted consistency
instance.  This is only a structural sanity theorem; it is not used as a
purported PA proof of its own consistency. -/
theorem restrictedConsistent_of_consistent (n : V)
    (hT : T.Consistent V) : RestrictedConsistent T n := by
  intro h
  exact hT h.erase

/-- The end formula of a restricted proof itself satisfies the advertised
bound.  This follows from the root fixed-point clause, so it also covers
nonstandard codes. -/
theorem bounded_formula_of_restrictedProof {n d p : V}
    (h : RestrictedProof T n d p) :
    QuantifierBoundedCode L n p := by
  have hb := allBounded_of_restricted T h.2
  exact hb p (by simp [h.1])

/-! ## The Peano-arithmetic specialization -/

/-- The exact Pi-one sentence whose PA derivability is required at external
level `n`. -/
noncomputable abbrev paRestrictedConsistencySentence (n : ℕ) :
    HierarchySymbol.piOne.Sentence :=
  restrictedConsistencySentence 𝗣𝗔 n

@[simp] theorem eval_paRestrictedConsistencySentence_iff (n : ℕ) :
    ((paRestrictedConsistencySentence n : ArithmeticSentence).Evalb
      (M := V) ![]) ↔
      RestrictedConsistent 𝗣𝗔 (ORingStructure.numeral n : V) := by
  exact eval_restrictedConsistencySentence_iff 𝗣𝗔 n

end LeanProofs.BoundedPAConsistency
