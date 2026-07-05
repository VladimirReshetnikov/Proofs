/-!
# Nicod's single-axiom Sheffer-stroke calculus

This module formalizes the one-connective language of the Sheffer stroke
(`⊼`, semantically NAND), Nicod's single axiom schema

```text
(p ↑ (q ↑ r)) ↑ ((u ↑ (u ↑ u)) ↑ ((w ↑ q) ↑ ((p ↑ w) ↑ (p ↑ w))))
```

and Nicod's single inference rule

```text
(p ↑ (q ↑ r)), p ⊢ r.
```

Lean already uses `↑` as coercion notation, so the formal notation below uses
`⊼` for the same NAND connective.

The file proves the semantic core needed for the classical-propositional-logic
claim:

* the Sheffer stroke alone expresses the usual truth-functional connectives;
* the Nicod axiom schema is classically valid;
* the Nicod rule is classically sound;
* consequently every formula derivable in this one-axiom/one-rule calculus is
  a classical tautology.

The harder historical completeness direction is that this proof system derives
all classical tautologies; the present module sets up the exact syntax and
soundness infrastructure for that derivability theorem.
-/

namespace LeanProofs

namespace Nicod

/-- NAND on truth values. -/
def boolNand (p q : Bool) : Bool :=
  !(p && q)

/-- Formulas whose only logical connective is NAND. -/
inductive Formula (α : Type) : Type where
  | atom : α → Formula α
  | nand : Formula α → Formula α → Formula α
  deriving DecidableEq, Repr

namespace Formula

infixr:60 " ⊼ " => Formula.nand

/-- Boolean semantics for NAND-only formulas. -/
def eval (v : α → Bool) : Formula α → Bool
  | atom a => v a
  | p ⊼ q => boolNand (eval v p) (eval v q)

/-- Classical validity of a NAND-only formula. -/
def Valid (p : Formula α) : Prop :=
  ∀ v : α → Bool, p.eval v = true

/-- Nicod's single axiom schema, in NAND-only syntax. -/
def nicodAxiom (p q r u w : Formula α) : Formula α :=
  (p ⊼ (q ⊼ r)) ⊼
    ((u ⊼ (u ⊼ u)) ⊼
      ((w ⊼ q) ⊼ ((p ⊼ w) ⊼ (p ⊼ w))))

/-- The exact one-axiom/one-rule Nicod proof system. -/
inductive Provable : Formula α → Prop where
  | singleAxiom (p q r u w : Formula α) : Provable (nicodAxiom p q r u w)
  | rule {p q r : Formula α} :
      Provable (p ⊼ (q ⊼ r)) → Provable p → Provable r

/-- Nicod's axiom schema is a tautology under NAND semantics. -/
theorem nicodAxiom_valid (p q r u w : Formula α) :
    Valid (nicodAxiom p q r u w) := by
  intro v
  cases hp : eval v p <;> cases hq : eval v q <;> cases hr : eval v r <;>
    cases hu : eval v u <;> cases hw : eval v w <;>
    simp [nicodAxiom, eval, boolNand, hp, hq, hr, hu, hw]

/-- Nicod's inference rule is sound for classical NAND semantics. -/
theorem nicodRule_sound {p q r : Formula α}
    (hmain : Valid (p ⊼ (q ⊼ r))) (hp : Valid p) : Valid r := by
  intro v
  have hpv : eval v p = true := hp v
  have hmv : eval v (p ⊼ (q ⊼ r)) = true := hmain v
  cases hq : eval v q <;> cases hr : eval v r <;>
    simp [eval, boolNand, hpv, hq, hr] at hmv ⊢

/-- Soundness of the one-axiom/one-rule Nicod calculus. -/
theorem Provable.sound {p : Formula α} (h : Provable p) : Valid p := by
  induction h with
  | singleAxiom p q r u w => exact nicodAxiom_valid p q r u w
  | rule hmain hp ihmain ihp => exact nicodRule_sound ihmain ihp

end Formula

/-- A standard propositional language used only to state functional completeness. -/
inductive ClassicalFormula (α : Type) : Type where
  | atom : α → ClassicalFormula α
  | neg : ClassicalFormula α → ClassicalFormula α
  | and : ClassicalFormula α → ClassicalFormula α → ClassicalFormula α
  | or : ClassicalFormula α → ClassicalFormula α → ClassicalFormula α
  | imp : ClassicalFormula α → ClassicalFormula α → ClassicalFormula α
  | iff : ClassicalFormula α → ClassicalFormula α → ClassicalFormula α
  deriving DecidableEq, Repr

namespace ClassicalFormula

/-- Boolean semantics for the usual classical connectives. -/
def eval (v : α → Bool) : ClassicalFormula α → Bool
  | atom a => v a
  | neg p => !(eval v p)
  | and p q => eval v p && eval v q
  | or p q => eval v p || eval v q
  | imp p q => !(eval v p) || eval v q
  | iff p q => eval v p == eval v q

open Formula

/-- Translate ordinary classical formulas to NAND-only formulas. -/
def toNand : ClassicalFormula α → Formula α
  | atom a => Formula.atom a
  | neg p =>
      let p' := toNand p
      p' ⊼ p'
  | and p q =>
      let p' := toNand p
      let q' := toNand q
      let pq := p' ⊼ q'
      pq ⊼ pq
  | or p q =>
      let p' := toNand p
      let q' := toNand q
      (p' ⊼ p') ⊼ (q' ⊼ q')
  | imp p q =>
      let p' := toNand p
      let q' := toNand q
      p' ⊼ (q' ⊼ q')
  | iff p q =>
      let p' := toNand p
      let q' := toNand q
      let pq := p' ⊼ (q' ⊼ q')
      let qp := q' ⊼ (p' ⊼ p')
      let both := pq ⊼ qp
      both ⊼ both

private theorem eval_toNand_neg {p : ClassicalFormula α} (v : α → Bool)
    (hp : (toNand p).eval v = eval v p) :
    (toNand (neg p)).eval v = eval v (neg p) := by
  cases h : eval v p <;> simp [toNand, eval, Formula.eval, boolNand, hp, h]

private theorem eval_toNand_and {p q : ClassicalFormula α} (v : α → Bool)
    (hp : (toNand p).eval v = eval v p) (hq : (toNand q).eval v = eval v q) :
    (toNand (and p q)).eval v = eval v (and p q) := by
  cases hpv : eval v p <;> cases hqv : eval v q <;>
    simp [toNand, eval, Formula.eval, boolNand, hp, hq, hpv, hqv]

private theorem eval_toNand_or {p q : ClassicalFormula α} (v : α → Bool)
    (hp : (toNand p).eval v = eval v p) (hq : (toNand q).eval v = eval v q) :
    (toNand (or p q)).eval v = eval v (or p q) := by
  cases hpv : eval v p <;> cases hqv : eval v q <;>
    simp [toNand, eval, Formula.eval, boolNand, hp, hq, hpv, hqv]

private theorem eval_toNand_imp {p q : ClassicalFormula α} (v : α → Bool)
    (hp : (toNand p).eval v = eval v p) (hq : (toNand q).eval v = eval v q) :
    (toNand (imp p q)).eval v = eval v (imp p q) := by
  cases hpv : eval v p <;> cases hqv : eval v q <;>
    simp [toNand, eval, Formula.eval, boolNand, hp, hq, hpv, hqv]

private theorem eval_toNand_iff {p q : ClassicalFormula α} (v : α → Bool)
    (hp : (toNand p).eval v = eval v p) (hq : (toNand q).eval v = eval v q) :
    (toNand (iff p q)).eval v = eval v (iff p q) := by
  cases hpv : eval v p <;> cases hqv : eval v q <;>
    simp [toNand, eval, Formula.eval, boolNand, hp, hq, hpv, hqv]

/--
The Sheffer stroke is functionally complete for the usual classical
truth-functional connectives.
-/
theorem eval_toNand (v : α → Bool) :
    ∀ p : ClassicalFormula α, (toNand p).eval v = eval v p
  | atom _ => rfl
  | neg p => eval_toNand_neg v (eval_toNand v p)
  | and p q => eval_toNand_and v (eval_toNand v p) (eval_toNand v q)
  | or p q => eval_toNand_or v (eval_toNand v p) (eval_toNand v q)
  | imp p q => eval_toNand_imp v (eval_toNand v p) (eval_toNand v q)
  | iff p q => eval_toNand_iff v (eval_toNand v p) (eval_toNand v q)

/-- Validity is preserved by translation from usual classical formulas to NAND-only formulas. -/
theorem toNand_valid_iff {p : ClassicalFormula α} :
    Formula.Valid (toNand p) ↔ ∀ v : α → Bool, eval v p = true := by
  constructor
  · intro h v
    rw [← eval_toNand]
    exact h v
  · intro h v
    rw [eval_toNand]
    exact h v

end ClassicalFormula

/-- NAND as a connective on Lean propositions. -/
def propNand (p q : Prop) : Prop :=
  ¬ (p ∧ q)

infixr:60 " ⊼ₚ " => propNand

/-- The object-language NAND semantics agrees with the familiar propositional reading. -/
theorem prop_nand_not (p : Prop) : (p ⊼ₚ p) ↔ ¬ p := by
  constructor
  · intro h hp
    exact h ⟨hp, hp⟩
  · intro h hp
    exact h hp.1

/-- `p → q` expressed with NAND alone. -/
theorem prop_nand_imp (p q : Prop) : (p ⊼ₚ (q ⊼ₚ q)) ↔ (p → q) := by
  constructor
  · intro h hp
    by_cases hq : q
    · exact hq
    · exfalso
      exact h ⟨hp, fun hqq => hq hqq.1⟩
  · intro hpq h
    exact h.2 ⟨hpq h.1, hpq h.1⟩

/-- `p ∧ q` expressed with NAND alone. -/
theorem prop_nand_and (p q : Prop) : ((p ⊼ₚ q) ⊼ₚ (p ⊼ₚ q)) ↔ p ∧ q := by
  constructor
  · intro h
    by_cases hp : p
    · by_cases hq : q
      · exact ⟨hp, hq⟩
      · exfalso
        exact h ⟨fun hpq => hq hpq.2, fun hpq => hq hpq.2⟩
    · exfalso
      exact h ⟨fun hpq => hp hpq.1, fun hpq => hp hpq.1⟩
  · intro hpq h
    exact h.1 hpq

/-- `p ∨ q` expressed with NAND alone. -/
theorem prop_nand_or (p q : Prop) : ((p ⊼ₚ p) ⊼ₚ (q ⊼ₚ q)) ↔ p ∨ q := by
  constructor
  · intro h
    by_cases hp : p
    · exact Or.inl hp
    · by_cases hq : q
      · exact Or.inr hq
      · exfalso
        exact h ⟨fun hpp => hp hpp.1, fun hqq => hq hqq.1⟩
  · rintro (hp | hq) h
    · exact h.1 ⟨hp, hp⟩
    · exact h.2 ⟨hq, hq⟩

/-- Nicod's single axiom, read directly as a classical propositional tautology. -/
theorem prop_nicod_axiom (p q r u w : Prop) :
    ((p ⊼ₚ (q ⊼ₚ r)) ⊼ₚ
      ((u ⊼ₚ (u ⊼ₚ u)) ⊼ₚ
        ((w ⊼ₚ q) ⊼ₚ ((p ⊼ₚ w) ⊼ₚ (p ⊼ₚ w))))) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;>
    by_cases hu : u <;> by_cases hw : w <;>
    simp [propNand, hp, hq, hr, hu, hw]

/-- Nicod's single inference rule, read directly over propositions. -/
theorem prop_nicod_rule {p q r : Prop} :
    (p ⊼ₚ (q ⊼ₚ r)) → p → r := by
  intro h hp
  by_cases hr : r
  · exact hr
  · exfalso
    exact h ⟨hp, fun hqr => hr hqr.2⟩

end Nicod

end LeanProofs
