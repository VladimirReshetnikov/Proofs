import BoundedPAConsistency.CodedHierarchy
import BoundedPAConsistency.Internal
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic

/-!
# Coded derivations with a bound at every node

The ordinary Foundation proof predicate is a least fixed point of the local
one-sided sequent-calculus rules.  This file forms a second least fixed point
from exactly the same rules, but conjoins `AllBounded` at every node.  Doing
the check in the fixed-point clause is important: checking only the root
sequent would turn the purported bounded consistency sentence back into the
ordinary consistency sentence, since falsity itself is quantifier-free.

In this calculus every formula-valued rule parameter is displayed in either
the conclusion sequent or a premise sequent.  In particular, the cut formula
and its negation occur in the two premise sequents, and an axiom instance
occurs in the axiom node's sequent.  Thus checking every sequent of the coded
tree checks every formula occurrence.
-/

namespace LeanProofs.BoundedPAConsistency

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- Every member of the HFS-coded sequent is a well-formed formula whose
polarity-sensitive hierarchy rank is at most `n`. -/
def AllBounded (n s : V) : Prop :=
  ∀ p ∈ s, QuantifierBoundedCode L n p

/-- Delta-one formula for `AllBounded`.  The HFS bounded-membership binder
keeps both presentations at Delta one. -/
noncomputable def allBoundedDef :
    HierarchySymbol.deltaOne.Semisentence 2 := .mkDelta
  (.mkSigma
    “n s. ∀ p ∈' s, !(quantifierBoundedCodeDef L).sigma n p”)
  (.mkPi
    “n s. ∀ p ∈' s, !(quantifierBoundedCodeDef L).pi n p”)

instance AllBounded.defined :
    HierarchySymbol.DefinedRel (V := V) HierarchySymbol.deltaOne
      (AllBounded (L := L)) (allBoundedDef (L := L)) :=
  .mk ⟨by
    intro v
    simp [allBoundedDef]
  , by
    intro v
    simp [allBoundedDef, AllBounded]⟩

instance AllBounded.definable :
    HierarchySymbol.DefinableRel (V := V) HierarchySymbol.deltaOne
      (AllBounded (L := L)) :=
  (AllBounded.defined (V := V) (L := L)).to_definable

variable (T : Theory L) [Theory.Δ₁ T]

/-- One ordinary derivation step, additionally requiring the conclusion
sequent of this very node to obey the hierarchy bound. -/
def Phi (n : V) (C : Set V) (d : V) : Prop :=
  Derivation.Phi T C d ∧ AllBounded (L := L) n (fstIdx d)

/-- The restricted checker is the least fixed point of `Phi`; its single
parameter is the (possibly nonstandard) model element used as rank bound. -/
noncomputable def blueprint : Fixpoint.Blueprint 1 := ⟨.mkDelta
  (.mkSigma
    “d C n. !(Derivation.blueprint T).core.sigma d C ∧
      ∃ s, !fstIdxDef s d ∧ !(allBoundedDef (L := L)).sigma n s”)
  (.mkPi
    “d C n. !(Derivation.blueprint T).core.pi d C ∧
      ∀ s, !fstIdxDef s d → !(allBoundedDef (L := L)).pi n s”)
  ⟩

def construction : Fixpoint.Construction V (blueprint T) where
  Φ v C d := Phi T (v 0) C d
  defined := .mk ⟨by
    intro v
    simp [blueprint]
    intro _
    exact (Derivation.Phi_definable (V := V) T).defined.1.iff
      ![v 0, v 1]
  , by
    intro v
    simp [blueprint, Phi]
    intro _
    exact (Derivation.Phi_definable (V := V) T).defined.2
      ![v 0, v 1]⟩
  monotone := by
    rintro C C' hC v d ⟨hd, hb⟩
    change Derivation.Phi T C' d ∧ AllBounded (v 0) (fstIdx d)
    exact ⟨(Derivation.construction T).monotone (v := ![]) hC hd, hb⟩

instance construction.strongFinite :
    Fixpoint.Construction.StrongFinite V (construction (V := V) T) where
  strong_finite := by
    rintro C v d ⟨hd, hb⟩
    have hd' : Derivation.Phi T {y ∈ C | y < d} d :=
      Fixpoint.Construction.StrongFinite.strong_finite
        (c := Derivation.construction T) (v := ![]) hd
    change Derivation.Phi T {y ∈ C | y < d} d ∧
      AllBounded (v 0) (fstIdx d)
    exact ⟨hd', hb⟩

/-- The internally arithmetized, all-occurrences restricted derivation
predicate. -/
def RestrictedDerivation (n d : V) : Prop :=
  (construction (V := V) T).Fixpoint ![n] d

/-- A Delta-one formula defining `RestrictedDerivation`. -/
noncomputable def restrictedDerivationDef :
    HierarchySymbol.deltaOne.Semisentence 2 :=
  (blueprint T).fixpointDefΔ₁.rew (Rew.subst ![#1, #0])

instance RestrictedDerivation.defined :
    HierarchySymbol.DefinedRel (V := V) HierarchySymbol.deltaOne
      (RestrictedDerivation T)
      (restrictedDerivationDef T) := by
  constructor
  exact ⟨by
    simpa [restrictedDerivationDef] using
      (construction (V := V) T).fixpoint_definedΔ₁.proper.rew
        (Rew.subst ![#1, #0])
  , by
    intro v
    simp [restrictedDerivationDef, RestrictedDerivation,
      (construction (V := V) T).eval_fixpointDefΔ₁,
      Matrix.constant_eq_singleton]⟩

instance RestrictedDerivation.definable :
    HierarchySymbol.DefinableRel (V := V) HierarchySymbol.deltaOne
      (RestrictedDerivation T) :=
  (RestrictedDerivation.defined (V := V) (L := L) T).to_definable

/-! ## Structural facts about the checker -/

lemma restricted_case_iff {n d : V} :
    RestrictedDerivation T n d ↔
      Derivation.Phi T {e | RestrictedDerivation T n e} d ∧
        AllBounded (L := L) n (fstIdx d) := by
  change (construction (V := V) T).Fixpoint ![n] d ↔
    (construction (V := V) T).Φ ![n]
      {e | (construction (V := V) T).Fixpoint ![n] e} d
  exact (construction (V := V) T).case

/-- The root bound is not postulated separately: it follows from unfolding
the restricted least fixed point at its final node. -/
lemma allBounded_of_restricted {n d : V}
    (hd : RestrictedDerivation T n d) :
    AllBounded (L := L) n (fstIdx d) :=
  (restricted_case_iff T).mp hd |>.2

/-- Forgetting the extra node checks gives an ordinary Foundation derivation.
This proof is an induction on the restricted least fixed point, not an appeal
to standardness of the numeric proof code. -/
lemma erase {n d : V} (hd : RestrictedDerivation T n d) :
    Derivation T d := by
  apply (construction (V := V) T).induction (v := ![n])
    (Γ := SigmaPiDelta.sigma)
    (P := Derivation T)
    (by
      exact Derivation.definable'
        (V := V) (T := T) (Γ := SigmaPiDelta.sigma) (m := 0))
    ?_ d hd
  intro C hC x hx
  apply (Derivation.construction T).case.mpr
  exact (Derivation.construction T).monotone (v := ![])
    (fun y hy ↦ (hC y hy).2) hx.1

end LeanProofs.BoundedPAConsistency
