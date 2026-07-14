import NaturalDeduction.Calculus

/-!
# Principle of explosion

The generic theorem derives an arbitrary `q` from proofs of `p` and `∼p`:

`Γ ⊢ p  →  Γ ⊢ ∼p  →  Γ ⊢ q`.

It uses implication elimination to derive falsity and then the intuitionistic
falsity-elimination rule.  Excluded middle is not used.  The exact sequent
`p, ∼p, Γ ⊢ q`, the conjunction form, and the closed implication form are
provided for both intuitionistic and classical natural deduction.
-/

namespace LeanProofs
namespace PrincipleOfExplosion

open NaturalDeduction
open NaturalDeduction.Formula

/-- Ex falso quodlibet for the common calculus.  This is the primitive
falsity-elimination rule, exposed as a named theorem. -/
theorem derives_exFalso {α : Type u} {extra : Formula α → Prop} {Γ : Context α}
    {q : Formula α} (hfalse : Derives extra Γ .falsum) : Derives extra Γ q :=
  .falseElim hfalse

/-- Deductive explosion: derive falsity by modus ponens from `p` and `∼p`,
then eliminate falsity. -/
theorem derives_explosion {α : Type u} {extra : Formula α → Prop} {Γ : Context α}
    {p q : Formula α} (hp : Derives extra Γ p) (hnp : Derives extra Γ (∼p)) :
    Derives extra Γ q :=
  derives_exFalso (.impElim hnp hp)

/-- Explosion from a proof of the single conjunction `p ⋏ ∼p`. -/
theorem derives_explosionFromConjunction {α : Type u}
    {extra : Formula α → Prop} {Γ : Context α} {p q : Formula α}
    (h : Derives extra Γ (p ⋏ ∼p)) : Derives extra Γ q :=
  derives_explosion (.andElimLeft h) (.andElimRight h)

/-- The exact sequent form `p, ∼p, Γ ⊢ q`. -/
theorem derives_explosion_sequent {α : Type u} (extra : Formula α → Prop)
    (Γ : Context α) (p q : Formula α) : Derives extra (p :: (∼p) :: Γ) q := by
  apply derives_explosion (p := p)
  · exact .assumption (List.Mem.head _)
  · exact .assumption (List.Mem.tail _ (List.Mem.head _))

/-- The single-contradictory-premise form `p ⋏ ∼p, Γ ⊢ q`. -/
theorem derives_explosion_conjSequent {α : Type u} (extra : Formula α → Prop)
    (Γ : Context α) (p q : Formula α) : Derives extra ((p ⋏ ∼p) :: Γ) q :=
  derives_explosionFromConjunction (.assumption (List.Mem.head _))

/-- The closed-under-the-context formula `(p ⋏ ∼p) ⇒ q`. -/
theorem derives_explosion_implication {α : Type u} (extra : Formula α → Prop)
    (Γ : Context α) (p q : Formula α) : Derives extra Γ ((p ⋏ ∼p) ⇒ q) :=
  .impIntro (derives_explosion_conjSequent extra Γ p q)

/-! ## Intuitionistic specializations -/

theorem intuitionistic_exFalso {α : Type u} {Γ : Context α} {q : Formula α}
    (hfalse : IntuitionisticallyDerives Γ .falsum) :
    IntuitionisticallyDerives Γ q :=
  derives_exFalso hfalse

theorem intuitionistic_explosion {α : Type u} {Γ : Context α} {p q : Formula α}
    (hp : IntuitionisticallyDerives Γ p) (hnp : IntuitionisticallyDerives Γ (∼p)) :
    IntuitionisticallyDerives Γ q :=
  derives_explosion hp hnp

theorem intuitionistic_explosionFromConjunction {α : Type u} {Γ : Context α}
    {p q : Formula α} (h : IntuitionisticallyDerives Γ (p ⋏ ∼p)) :
    IntuitionisticallyDerives Γ q :=
  derives_explosionFromConjunction h

theorem intuitionistic_explosion_sequent {α : Type u} (Γ : Context α)
    (p q : Formula α) : IntuitionisticallyDerives (p :: (∼p) :: Γ) q :=
  derives_explosion_sequent (fun _ => False) Γ p q

theorem intuitionistic_explosion_conjSequent {α : Type u} (Γ : Context α)
    (p q : Formula α) : IntuitionisticallyDerives ((p ⋏ ∼p) :: Γ) q :=
  derives_explosion_conjSequent (fun _ => False) Γ p q

theorem intuitionistic_explosion_implication {α : Type u} (Γ : Context α)
    (p q : Formula α) : IntuitionisticallyDerives Γ ((p ⋏ ∼p) ⇒ q) :=
  derives_explosion_implication (fun _ => False) Γ p q

/-! ## Classical specializations -/

theorem classical_exFalso {α : Type u} {Γ : Context α} {q : Formula α}
    (hfalse : ClassicallyDerives Γ .falsum) : ClassicallyDerives Γ q :=
  derives_exFalso hfalse

theorem classical_explosion {α : Type u} {Γ : Context α} {p q : Formula α}
    (hp : ClassicallyDerives Γ p) (hnp : ClassicallyDerives Γ (∼p)) :
    ClassicallyDerives Γ q :=
  derives_explosion hp hnp

theorem classical_explosionFromConjunction {α : Type u} {Γ : Context α}
    {p q : Formula α} (h : ClassicallyDerives Γ (p ⋏ ∼p)) :
    ClassicallyDerives Γ q :=
  derives_explosionFromConjunction h

theorem classical_explosion_sequent {α : Type u} (Γ : Context α)
    (p q : Formula α) : ClassicallyDerives (p :: (∼p) :: Γ) q :=
  derives_explosion_sequent ClassicalAxiom Γ p q

theorem classical_explosion_conjSequent {α : Type u} (Γ : Context α)
    (p q : Formula α) : ClassicallyDerives ((p ⋏ ∼p) :: Γ) q :=
  derives_explosion_conjSequent ClassicalAxiom Γ p q

theorem classical_explosion_implication {α : Type u} (Γ : Context α)
    (p q : Formula α) : ClassicallyDerives Γ ((p ⋏ ∼p) ⇒ q) :=
  derives_explosion_implication ClassicalAxiom Γ p q

end PrincipleOfExplosion
end LeanProofs
