import BoundedPAConsistency.UniformInternalProvability

/-!
# Existential proof packages for uniform bounded consistency

The literal uniform theorem has been reduced to constructing a PA proof of
the `n`-th bounded-consistency instance for every element `n` of every PA
model. In a nonstandard model, a metatheoretic recursion over `Nat` cannot
produce those proof codes.

This module records a less restrictive route to the missing selector. A
`Package n z` witness may store the code of a level-specific partial-truth
formula together with codes of PA derivations for its Tarski, substitution,
axiom-soundness, and final consistency clauses. The relation is allowed to
have many witnesses. Consequently, it need not be the graph of a canonical
primitive-recursive compiler: Sigma-one induction only needs one base package
and a way to extend any package by one level.

The results below are an infrastructure reduction, not a construction of
those packages. In particular, the substantive base, successor, and final
proof-extraction obligations remain explicit hypotheses.
-/

namespace LeanProofs.BoundedPAConsistency.UniformProofPackage

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LeanProofs.BoundedPAConsistency
open LeanProofs.BoundedPAConsistency.UniformInternalProvability

variable {V : Type*} [ORingStructure V]

/-- There is some coded proof package at hierarchy level `n`.

Keeping the package contents abstract makes the induction lemma reusable while
still exposing its exact logical-complexity requirement. -/
def HasPARestrictedConsistencyProofPackage
    (Package : V → V → Prop) (n : V) : Prop :=
  ∃ z : V, Package n z

/-- Existentially forgetting a package code preserves Sigma-one definability.

`Definable.exs` places its freshly bound witness in coordinate zero. The
explicit coordinate swap below is therefore necessary because `Package`
takes the hierarchy level before the package code. -/
lemma hasPARestrictedConsistencyProofPackage_definable
    {Package : V → V → Prop}
    (hPackage : HierarchySymbol.sigmaOne.DefinableRel Package) :
    HierarchySymbol.sigmaOne.DefinablePred
      (HasPARestrictedConsistencyProofPackage Package) := by
  unfold HasPARestrictedConsistencyProofPackage
  apply HierarchySymbol.Definable.exs
  exact HierarchySymbol.DefinableRel.comp hPackage
    (HierarchySymbol.DefinableFunction.var 1)
    (HierarchySymbol.DefinableFunction.var 0)

variable [hISigma : V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Existential proof packages are sufficient for the model-internal selector.

The induction is PA-internal: `n` ranges over the ambient arithmetic model
`V`, so the conclusion includes nonstandard hierarchy levels. No uniqueness,
canonical choice, or definable function graph for package witnesses is used.
-/
theorem paRestrictedConsistencyProofSelectorIn_of_package
    {Package : V → V → Prop}
    (hPackage : HierarchySymbol.sigmaOne.DefinableRel Package)
    (hzero : ∃ z : V, Package 0 z)
    (hsucc : ∀ n z : V, Package n z →
      ∃ z' : V, Package (n + 1) z')
    (hfinal : ∀ n z : V, Package n z →
      ∃ d : V, Proof Peano d
        (substNumeral (⌜paRestrictedConsistencyTemplate⌝ : V) n)) :
    PARestrictedConsistencyProofSelectorIn V := by
  have hall : ∀ n : V,
      HasPARestrictedConsistencyProofPackage Package n := by
    intro n
    induction n using ISigma1.sigma1_succ_induction
    · exact hasPARestrictedConsistencyProofPackage_definable hPackage
    case zero => exact hzero
    case succ n ih =>
      rcases ih with ⟨z, hz⟩
      exact hsucc n z hz
  intro n
  rcases hall n with ⟨z, hz⟩
  exact hfinal n z hz

end LeanProofs.BoundedPAConsistency.UniformProofPackage
