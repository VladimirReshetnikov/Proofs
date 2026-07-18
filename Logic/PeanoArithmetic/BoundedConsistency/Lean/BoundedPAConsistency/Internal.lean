import Foundation.FirstOrder.Arithmetic.HFS.Fixpoint

/-!
# Infrastructure for the eventual internal bounded-reflection proof

The coded derivations in `Foundation` are least fixed points.  Their packaged
induction principle is deliberately calibrated to `I Sigma 1`, and therefore
only accepts a Sigma/Pi/Delta-one induction invariant.  A fixed partial truth
predicate for formulas with `n` quantifier groups generally has higher
arithmetical complexity.  In a model of full PA this is not an obstacle: the
model satisfies induction at every *fixed, metatheoretic* hierarchy level.

`inductionAtHierarchy` is the small missing bridge.  It is the existing
fixed-point induction proof with its hard-coded level `1` replaced by `m + 1`.
The successor is essential because membership in the coded least fixed point
is Delta-one.  This lemma does not postulate reflection and does not by itself
prove bounded consistency; it makes it possible to run the eventual
partial-truth invariant through a nonstandard coded derivation.
-/

namespace LeanProofs.BoundedPAConsistency.Internal

open LO FirstOrder
open LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V]

variable {k : Nat} {blueprint : Fixpoint.Blueprint k}

/--
Induction over a coded least fixed point with an invariant at an arbitrary
positive arithmetical-hierarchy level.

The extra model assumption is exactly the induction fragment used by the
proof.  A model of PA supplies it for every external `m`; no uniform internal
quantification over hierarchy levels is introduced here.
-/
theorem inductionAtHierarchy
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (construction : Fixpoint.Construction V blueprint)
    [construction.StrongFinite]
    (parameters : Fin k → V)
    {Γ : SigmaPiDelta} {m : Nat} {P : V → Prop}
    [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚺 (m + 1)]
    (hP : Γ-[m + 1]-Predicate P)
    (step : ∀ C : Set V,
      (∀ x ∈ C, construction.Fixpoint parameters x ∧ P x) →
      ∀ x, construction.Φ parameters C x → P x) :
    ∀ x, construction.Fixpoint parameters x → P x := by
  apply InductionOnHierarchy.order_induction_sigma
    (Γ := Γ) (m := m + 1)
    (P := fun x ↦ construction.Fixpoint parameters x → P x)
  · -- The fixed-point predicate is Delta-one, hence it is available at
    -- every positive level; implication then combines it with the invariant.
    apply HierarchySymbol.Definable.imp
      (HierarchySymbol.DefinablePred.comp
        (by
          apply HierarchySymbol.Definable.of_deltaOne
          exact
            ⟨blueprint.fixpointDefΔ₁.rew <|
                Rew.embSubsts <| #0 :> fun x ↦ &(parameters x),
              construction.fixpoint_definedΔ₁.proper.rew' _,
              by
                intro values
                simp [construction.eval_fixpointDefΔ₁]⟩)
        (by definability))
      (by definability)
  · intro x ih hx
    have hstep : construction.Φ parameters
        {y | construction.Fixpoint parameters y ∧ y < x} x :=
      Fixpoint.Construction.StrongFinite.strong_finite
        (construction.case.mp hx)
    exact step
      {y | construction.Fixpoint parameters y ∧ y < x}
      (by
        intro y hy
        exact ⟨hy.1, ih y hy.2 hy.1⟩)
      x hstep

section PeanoModel

variable [hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

local instance : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory hPA

/--
The form used by bounded reflection: full PA supplies both induction instances
needed by `inductionAtHierarchy` at each externally fixed level.
-/
theorem inductionInPeanoModel
    (construction : Fixpoint.Construction V blueprint)
    [construction.StrongFinite]
    (parameters : Fin k → V)
    {Γ : SigmaPiDelta} {m : Nat} {P : V → Prop}
    (hP : Γ-[m + 1]-Predicate P)
    (step : ∀ C : Set V,
      (∀ x ∈ C, construction.Fixpoint parameters x ∧ P x) →
      ∀ x, construction.Φ parameters C x → P x) :
    ∀ x, construction.Fixpoint parameters x → P x := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚺 (m + 1) := models_of_subtheory hPA
  exact inductionAtHierarchy construction parameters hP step

end PeanoModel

end LeanProofs.BoundedPAConsistency.Internal
