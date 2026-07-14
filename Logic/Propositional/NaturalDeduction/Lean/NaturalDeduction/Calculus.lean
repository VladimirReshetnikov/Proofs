/-!
# Propositional natural deduction

A shared, dependency-free calculus for the structural propositional-logic
developments in this repository.  The calculus is parameterized by additional
zero-premise logical axioms:

* intuitionistic logic supplies none;
* classical logic supplies the law of excluded middle.

In particular, `falseElim` is part of intuitionistic natural deduction.  This
distinguishes intuitionistic logic from minimal logic, which omits that rule.
-/

namespace LeanProofs
namespace NaturalDeduction

/-- Propositional formulas.  Negation is implication to falsity. -/
inductive Formula (α : Type u) : Type u where
  | atom : α → Formula α
  | falsum : Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α
  | impl : Formula α → Formula α → Formula α
  deriving DecidableEq, Repr

namespace Formula

infixr:55 " ⋏ " => Formula.conj
infixr:50 " ⋎ " => Formula.disj
infixr:45 " ⇒ " => Formula.impl
prefix:60 "∼" => fun p => Formula.impl p Formula.falsum

end Formula

open Formula

/-- A proof context is a finite list of assumptions. -/
abbrev Context (α : Type u) := List (Formula α)

/-- Natural deduction with a parameter for additional zero-premise axioms. -/
inductive Derives {α : Type u} (extra : Formula α → Prop) :
    Context α → Formula α → Prop where
  | assumption {Γ p} : p ∈ Γ → Derives extra Γ p
  | logicalAxiom {Γ p} : extra p → Derives extra Γ p
  | falseElim {Γ p} : Derives extra Γ .falsum → Derives extra Γ p
  | andIntro {Γ p q} : Derives extra Γ p → Derives extra Γ q →
      Derives extra Γ (p ⋏ q)
  | andElimLeft {Γ p q} : Derives extra Γ (p ⋏ q) → Derives extra Γ p
  | andElimRight {Γ p q} : Derives extra Γ (p ⋏ q) → Derives extra Γ q
  | orIntroLeft {Γ p q} : Derives extra Γ p → Derives extra Γ (p ⋎ q)
  | orIntroRight {Γ p q} : Derives extra Γ q → Derives extra Γ (p ⋎ q)
  | orElim {Γ p q r} : Derives extra Γ (p ⋎ q) →
      Derives extra (p :: Γ) r → Derives extra (q :: Γ) r → Derives extra Γ r
  | impIntro {Γ p q} : Derives extra (p :: Γ) q → Derives extra Γ (p ⇒ q)
  | impElim {Γ p q} : Derives extra Γ (p ⇒ q) → Derives extra Γ p →
      Derives extra Γ q

/-- Intuitionistic natural deduction has no additional logical axioms. -/
abbrev IntuitionisticallyDerives {α : Type u} (Γ : Context α) (p : Formula α) : Prop :=
  Derives (fun _ => False) Γ p

/-- The additional axiom schema for classical natural deduction. -/
def ClassicalAxiom {α : Type u} (p : Formula α) : Prop :=
  ∃ q, p = (q ⋎ ∼q)

/-- Classical natural deduction is intuitionistic natural deduction extended
by excluded middle. -/
abbrev ClassicallyDerives {α : Type u} (Γ : Context α) (p : Formula α) : Prop :=
  Derives ClassicalAxiom Γ p

namespace Derives

/-- A derivation remains valid when its logical axiom set is enlarged. -/
theorem mapAxioms {α : Type u} {axiom₁ axiom₂ : Formula α → Prop}
    (hax : ∀ ⦃p⦄, axiom₁ p → axiom₂ p) {Γ : Context α} {p : Formula α}
    (h : Derives axiom₁ Γ p) : Derives axiom₂ Γ p := by
  induction h with
  | assumption hp => exact .assumption hp
  | logicalAxiom hp => exact .logicalAxiom (hax hp)
  | falseElim _ ih => exact .falseElim ih
  | andIntro _ _ ihp ihq => exact .andIntro ihp ihq
  | andElimLeft _ ih => exact .andElimLeft ih
  | andElimRight _ ih => exact .andElimRight ih
  | orIntroLeft _ ih => exact .orIntroLeft ih
  | orIntroRight _ ih => exact .orIntroRight ih
  | orElim _ _ _ ihpq ihp ihq => exact .orElim ihpq ihp ihq
  | impIntro _ ih => exact .impIntro ih
  | impElim _ _ ihpq ihp => exact .impElim ihpq ihp

end Derives

/-- Excluded middle is available in the classical calculus. -/
theorem classical_excludedMiddle {α : Type u} (Γ : Context α) (p : Formula α) :
    ClassicallyDerives Γ (p ⋎ ∼p) :=
  .logicalAxiom ⟨p, rfl⟩

/-- Every intuitionistic derivation is, in particular, a classical one. -/
theorem intuitionistic_to_classical {α : Type u} {Γ : Context α} {p : Formula α}
    (h : IntuitionisticallyDerives Γ p) : ClassicallyDerives Γ p :=
  h.mapAxioms (fun {_} hfalse => False.elim hfalse)

end NaturalDeduction
end LeanProofs

