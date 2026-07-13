import NaturalDeduction.Calculus

/-!
# Monotonicity of entailment

This file proves the structural weakening theorem

`Γ ⊢ C  →  Δ ⊢ C` whenever every assumption in `Γ` also occurs in `Δ`.

The common natural-deduction calculus is parameterized by its zero-premise
logical axioms.  Consequently one constructive proof establishes monotonicity
for both intuitionistic logic and classical logic.
-/

namespace LeanProofs
namespace MonotonicityOfEntailment

open NaturalDeduction
open NaturalDeduction.Formula

/-- Every assumption in `Γ` is also available in `Δ`. -/
def Included {α : Type u} (Γ Δ : Context α) : Prop :=
  ∀ ⦃p⦄, p ∈ Γ → p ∈ Δ

namespace Included

/-- Context inclusion is preserved when the same local assumption is added to
both contexts. -/
theorem cons {α : Type u} {Γ Δ : Context α} {p : Formula α}
    (h : Included Γ Δ) : Included (p :: Γ) (p :: Δ) := by
  intro q hq
  cases hq with
  | head => exact List.Mem.head _
  | tail _ hq => exact List.Mem.tail _ (h hq)

/-- Adding one assumption enlarges a context. -/
theorem intoCons {α : Type u} {Γ : Context α} {p : Formula α} :
    Included Γ (p :: Γ) := by
  intro q hq
  exact List.Mem.tail _ hq

end Included

/-- General weakening (monotonicity): a derivation remains valid in every
larger context. -/
theorem derives_weaken {α : Type u} {extra : Formula α → Prop} {Γ : Context α}
    {p : Formula α} (h : Derives extra Γ p) :
    ∀ {Δ}, Included Γ Δ → Derives extra Δ p := by
  induction h with
  | assumption hp =>
      intro Δ hsub
      exact .assumption (hsub hp)
  | logicalAxiom hp =>
      intro Δ _
      exact .logicalAxiom hp
  | falseElim _ ih =>
      intro Δ hsub
      exact .falseElim (ih hsub)
  | andIntro _ _ ihp ihq =>
      intro Δ hsub
      exact .andIntro (ihp hsub) (ihq hsub)
  | andElimLeft _ ih =>
      intro Δ hsub
      exact .andElimLeft (ih hsub)
  | andElimRight _ ih =>
      intro Δ hsub
      exact .andElimRight (ih hsub)
  | orIntroLeft _ ih =>
      intro Δ hsub
      exact .orIntroLeft (ih hsub)
  | orIntroRight _ ih =>
      intro Δ hsub
      exact .orIntroRight (ih hsub)
  | orElim _ _ _ ihpq ihp ihq =>
      intro Δ hsub
      exact .orElim (ihpq hsub) (ihp hsub.cons) (ihq hsub.cons)
  | impIntro _ ih =>
      intro Δ hsub
      exact .impIntro (ih hsub.cons)
  | impElim _ _ ihpq ihp =>
      intro Δ hsub
      exact .impElim (ihpq hsub) (ihp hsub)

/-- The one-assumption weakening rule displayed as `Γ ⊢ C / Γ,A ⊢ C`. -/
theorem derives_addAssumption {α : Type u} {extra : Formula α → Prop}
    {Γ : Context α} {p a : Formula α} (h : Derives extra Γ p) :
    Derives extra (a :: Γ) p :=
  derives_weaken h Included.intoCons

/-- Monotonicity of intuitionistic entailment under arbitrary context
inclusion. -/
theorem intuitionistic_monotonicity {α : Type u} {Γ Δ : Context α}
    {p : Formula α} (hsub : Included Γ Δ) (h : IntuitionisticallyDerives Γ p) :
    IntuitionisticallyDerives Δ p :=
  derives_weaken h hsub

/-- Intuitionistic weakening by one assumption. -/
theorem intuitionistic_weakening {α : Type u} {Γ : Context α} {p a : Formula α}
    (h : IntuitionisticallyDerives Γ p) : IntuitionisticallyDerives (a :: Γ) p :=
  derives_addAssumption h

/-- Monotonicity of classical entailment under arbitrary context inclusion. -/
theorem classical_monotonicity {α : Type u} {Γ Δ : Context α}
    {p : Formula α} (hsub : Included Γ Δ) (h : ClassicallyDerives Γ p) :
    ClassicallyDerives Δ p :=
  derives_weaken h hsub

/-- Classical weakening by one assumption. -/
theorem classical_weakening {α : Type u} {Γ : Context α} {p a : Formula α}
    (h : ClassicallyDerives Γ p) : ClassicallyDerives (a :: Γ) p :=
  derives_addAssumption h

end MonotonicityOfEntailment
end LeanProofs
