import ShefferStroke.Sheffer

/-!
# Nicod's single-axiom Sheffer-stroke calculus

This module formalizes Nicod's one-axiom/one-rule proof system over the
shared NAND-only language of `ShefferStroke.Sheffer`: the single axiom schema

```text
(p ↑ (q ↑ r)) ↑ ((u ↑ (u ↑ u)) ↑ ((w ↑ q) ↑ ((p ↑ w) ↑ (p ↑ w))))
```

and the single inference rule

```text
(p ↑ (q ↑ r)), p ⊢ r.
```

Lean already uses `↑` as coercion notation, so the formal notation below uses
`⊼` for the same NAND connective.

The file proves both the semantic core and the proof-theoretic implementation
claim:

* the Nicod axiom schema is classically valid and the Nicod rule is
  classically sound, so every derivable formula is a classical tautology;
* the shared Sheffer-stroke translation of classical formulas preserves
  validity, so the NAND language is expressively complete;
* Nicod's axiom and rule derive the three Lukasiewicz Hilbert axiom schemas
  for classical propositional logic, and derive standard modus ponens for
  NAND-defined implication;
* therefore every theorem of the standard Lukasiewicz propositional calculus
  translates to a theorem of the one-axiom/one-rule Nicod calculus.
-/

namespace LeanProofs

namespace Nicod

open Sheffer

/-- Formulas whose only logical connective is NAND: the shared stroke syntax. -/
abbrev Formula (α : Type u) : Type u := StrokeFormula α

namespace Formula

infixr:60 " ⊼ " => StrokeFormula.stroke

/-- Boolean semantics for NAND-only formulas. -/
def eval (v : α → Bool) : Formula α → Bool
  | .atom a => v a
  | p ⊼ q => boolNand (eval v p) (eval v q)

/-- Nicod's NAND-fixed semantics is the shared stroke semantics at `boolNand`. -/
theorem eval_eq_evalWith (v : α → Bool) :
    ∀ p : Formula α, eval v p = StrokeFormula.evalWith boolNand v p
  | .atom _ => rfl
  | .stroke p q => by
      simp [eval, StrokeFormula.evalWith, eval_eq_evalWith v p, eval_eq_evalWith v q]

/-- Classical validity of a NAND-only formula. -/
def Valid (p : Formula α) : Prop :=
  ∀ v : α → Bool, eval v p = true

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

/-- Implication expressed in the NAND-only language. -/
def imp (p q : Formula α) : Formula α :=
  p ⊼ (q ⊼ q)

/-- Negation expressed in the NAND-only language. -/
def neg (p : Formula α) : Formula α :=
  p ⊼ p

infixr:55 " ⇾ " => Formula.imp
prefix:70 "∼" => Formula.neg

/-- Nicod's axiom used as an inference schema.  This is Metamath's `nic-imp`. -/
theorem nicImp {p q r : Formula α} (u w : Formula α)
    (h : Provable (p ⊼ (q ⊼ r))) :
    Provable ((w ⊼ q) ⊼ ((p ⊼ w) ⊼ (p ⊼ w))) :=
  Provable.rule (Provable.singleAxiom p q r u w) h

/-- Lemma for the NAND identity theorem.  This is Metamath's `nic-idlem1`. -/
theorem nicIdlem1 (p q r u w : Formula α) :
    Provable ((w ⊼ (u ⊼ (u ⊼ u))) ⊼
      (((p ⊼ (q ⊼ r)) ⊼ w) ⊼ ((p ⊼ (q ⊼ r)) ⊼ w))) :=
  nicImp u w (Provable.singleAxiom p q r u p)

/-- Lemma for the NAND identity theorem.  This is Metamath's `nic-idlem2`. -/
theorem nicIdlem2 {eta p q r theta : Formula α} (u : Formula α)
    (h : Provable (eta ⊼ ((p ⊼ (q ⊼ r)) ⊼ theta))) :
    Provable ((theta ⊼ (u ⊼ (u ⊼ u))) ⊼ eta) := by
  have hmajor : Provable
      ((eta ⊼ ((p ⊼ (q ⊼ r)) ⊼ theta)) ⊼
        ((((theta ⊼ (u ⊼ (u ⊼ u))) ⊼ eta) ⊼
          ((theta ⊼ (u ⊼ (u ⊼ u))) ⊼ eta)))) :=
    nicImp eta eta (nicIdlem1 p q r u theta)
  exact Provable.rule hmajor h

/-- `p ⇾ p`, expressed as a NAND formula.  This is Metamath's `nic-id`. -/
theorem nicId (p : Formula α) : Provable (p ⊼ (p ⊼ p)) := by
  let i : Formula α := p ⊼ (p ⊼ p)
  let c : Formula α := (p ⊼ p) ⊼ ((p ⊼ p) ⊼ (p ⊼ p))
  have h1 : Provable (i ⊼ (i ⊼ c)) := by
    simpa [i, c, nicodAxiom] using (Provable.singleAxiom p p p p p)
  have h2 : Provable ((c ⊼ i) ⊼ i) := by
    simpa [i, c] using
      (nicIdlem2 (eta := i) (p := p) (q := p) (r := p) (theta := c) p h1)
  have h3 : Provable ((i ⊼ i) ⊼ ((c ⊼ i) ⊼ (c ⊼ i))) := by
    simpa [i, c] using
      (nicIdlem1 (p ⊼ p) (p ⊼ p) (p ⊼ p) p i)
  have h4 : Provable (((c ⊼ i) ⊼ i) ⊼ (i ⊼ i)) := by
    simpa [i, c] using
      (nicIdlem2 (eta := i ⊼ i) (p := c) (q := p) (r := p ⊼ p)
        (theta := c ⊼ i) p h3)
  exact Provable.rule h4 h2

/-- Symmetry of NAND in theorem form.  This is Metamath's `nic-swap`. -/
theorem nicSwap (p q : Formula α) :
    Provable ((q ⊼ p) ⊼ ((p ⊼ q) ⊼ (p ⊼ q))) :=
  Provable.rule (Provable.singleAxiom p p p p q) (nicId p)

/-- Inference version of `nicSwap`.  This is Metamath's `nic-isw1`. -/
theorem nicIsw1 {p q : Formula α} (h : Provable (q ⊼ p)) : Provable (p ⊼ q) :=
  Provable.rule (nicSwap p q) h

/-- Inference for swapping nested terms.  This is Metamath's `nic-isw2`. -/
theorem nicIsw2 {p q r : Formula α}
    (h : Provable (p ⊼ (q ⊼ r))) : Provable (p ⊼ (r ⊼ q)) := by
  have hmajor : Provable
      ((p ⊼ (q ⊼ r)) ⊼ (((r ⊼ q) ⊼ p) ⊼ ((r ⊼ q) ⊼ p))) :=
    nicImp p p (nicSwap q r)
  have htmp : Provable ((r ⊼ q) ⊼ p) := Provable.rule hmajor h
  exact nicIsw1 htmp

/-- Inference version of `nicImp` using a right-handed term. -/
theorem nicIimp1 {p q r u : Formula α}
    (hmain : Provable (p ⊼ (q ⊼ r))) (harg : Provable (u ⊼ q)) :
    Provable (u ⊼ p) := by
  have hmajor : Provable ((u ⊼ q) ⊼ ((p ⊼ u) ⊼ (p ⊼ u))) :=
    nicImp p u hmain
  have htmp : Provable (p ⊼ u) := Provable.rule hmajor harg
  exact nicIsw1 htmp

/-- Inference version of `nicImp` using a left-handed term. -/
theorem nicIimp2 {p q r u : Formula α}
    (hmain : Provable ((p ⊼ q) ⊼ (r ⊼ r))) (harg : Provable (u ⊼ p)) :
    Provable (u ⊼ (r ⊼ r)) := by
  exact nicIimp1 (nicIsw1 hmain) harg

/-- Remove the trailing term.  This is Metamath's `nic-idel`. -/
theorem nicIdel {p q r : Formula α}
    (h : Provable (p ⊼ (q ⊼ r))) : Provable (p ⊼ (q ⊼ q)) := by
  have hqqq : Provable ((q ⊼ q) ⊼ q) := nicIsw1 (nicId q)
  have hmajor : Provable
      (((q ⊼ q) ⊼ q) ⊼ ((p ⊼ (q ⊼ q)) ⊼ (p ⊼ (q ⊼ q)))) :=
    nicImp p (q ⊼ q) h
  exact Provable.rule hmajor hqqq

/-- Chained inference for NAND-encoded implication.  This is Metamath's `nic-ich`. -/
theorem nicIch {p q r : Formula α}
    (hpq : Provable (p ⊼ (q ⊼ q))) (hqr : Provable (q ⊼ (r ⊼ r))) :
    Provable (p ⊼ (r ⊼ r)) := by
  have hrq : Provable ((r ⊼ r) ⊼ q) := nicIsw1 hqr
  have hmajor : Provable
      (((r ⊼ r) ⊼ q) ⊼ ((p ⊼ (r ⊼ r)) ⊼ (p ⊼ (r ⊼ r)))) :=
    nicImp p (r ⊼ r) hpq
  exact Provable.rule hmajor hrq

/-- Double the terms, a contraposition-like inference.  This is Metamath's `nic-idbl`. -/
theorem nicIdbl {p q : Formula α}
    (hpq : Provable (p ⊼ (q ⊼ q))) :
    Provable ((q ⊼ q) ⊼ ((p ⊼ p) ⊼ (p ⊼ p))) := by
  have h1 : Provable ((q ⊼ q) ⊼ ((p ⊼ q) ⊼ (p ⊼ q))) :=
    nicImp p q hpq
  have h2 : Provable ((p ⊼ q) ⊼ ((p ⊼ p) ⊼ (p ⊼ p))) :=
    nicImp p p hpq
  exact nicIch h1 h2

/-- Extract one side of a NAND biconditional-definition shape. -/
theorem nicBi1 {p q : Formula α}
    (h : Provable ((p ⊼ q) ⊼ ((p ⊼ p) ⊼ (q ⊼ q)))) :
    Provable (p ⊼ (q ⊼ q)) := by
  have hp : Provable (p ⊼ (p ⊼ p)) := nicId p
  have h1 : Provable (p ⊼ (p ⊼ q)) := nicIimp1 h hp
  have h2 : Provable (p ⊼ (q ⊼ p)) := nicIsw2 h1
  exact nicIdel h2

/-- Extract the other side of a NAND biconditional-definition shape. -/
theorem nicBi2 {p q : Formula α}
    (h : Provable ((p ⊼ q) ⊼ ((p ⊼ p) ⊼ (q ⊼ q)))) :
    Provable (q ⊼ (p ⊼ p)) := by
  have h1 : Provable ((p ⊼ q) ⊼ ((q ⊼ q) ⊼ (p ⊼ p))) := nicIsw2 h
  have hq : Provable (q ⊼ (q ⊼ q)) := nicId q
  have h2 : Provable (q ⊼ (p ⊼ q)) := nicIimp1 h1 hq
  exact nicIdel h2

/-- The biconditional-definition justification shape. -/
theorem nicBijust (p : Formula α) :
    Provable ((p ⊼ p) ⊼ ((p ⊼ p) ⊼ (p ⊼ p))) :=
  nicSwap p p

/-- The NAND definition of implication, stated in Metamath's definition shape. -/
theorem nicDfim (p q : Formula α) :
    Provable (((p ⊼ (q ⊼ q)) ⊼ (p ⇾ q)) ⊼
      (((p ⊼ (q ⊼ q)) ⊼ (p ⊼ (q ⊼ q))) ⊼ ((p ⇾ q) ⊼ (p ⇾ q)))) := by
  simpa [imp] using nicBijust (p ⇾ q)

/-- The NAND definition of negation, stated in Metamath's definition shape. -/
theorem nicDfneg (p : Formula α) :
    Provable (((p ⊼ p) ⊼ ∼p) ⊼ (((p ⊼ p) ⊼ (p ⊼ p)) ⊼ (∼p ⊼ ∼p))) := by
  simpa [neg] using nicBijust (∼p)

/-- Standard modus ponens for NAND-defined implication. -/
theorem nicStdmp {p q : Formula α} (hp : Provable p) (hpq : Provable (p ⇾ q)) :
    Provable q :=
  Provable.rule hpq hp

/-- The first Lukasiewicz axiom schema, derived from Nicod's axiom and rule. -/
theorem nicLuk1 (p q r : Formula α) :
    Provable ((p ⇾ q) ⇾ ((q ⇾ r) ⇾ (p ⇾ r))) := by
  let c : Formula α := p ⇾ r
  let f : Formula α := (r ⊼ r) ⊼ q
  let d : Formula α := f ⊼ (c ⊼ c)
  let e : Formula α := (c ⊼ c) ⊼ f
  let x : Formula α := (q ⇾ r) ⇾ c
  have h3 : Provable ((p ⇾ q) ⊼ ((p ⊼ (p ⊼ p)) ⊼ d)) := by
    simpa [imp, c, f, d, nicodAxiom] using
      (Provable.singleAxiom p q q p (r ⊼ r))
  have h4 : Provable ((p ⇾ q) ⊼ (d ⊼ (p ⊼ (p ⊼ p)))) := nicIsw2 h3
  have h5 : Provable ((p ⇾ q) ⊼ (d ⊼ d)) := nicIdel h4
  have h8 : Provable ((c ⊼ c) ⊼ ((c ⊼ c) ⊼ (c ⊼ c))) := nicId (c ⊼ c)
  have h9 : Provable (d ⊼ (e ⊼ e)) := by
    simpa [c, d, e, f] using nicImp (c ⊼ c) f h8
  have h12 : Provable ((q ⇾ r) ⊼ (f ⊼ f)) := by
    simpa [imp, f] using nicSwap (r ⊼ r) q
  have h14 : Provable (e ⊼ (x ⊼ x)) := by
    simpa [imp, c, e, f, x] using nicImp (q ⇾ r) (c ⊼ c) h12
  have h15 : Provable (d ⊼ (x ⊼ x)) := nicIch h9 h14
  have h16 : Provable ((p ⇾ q) ⊼ (x ⊼ x)) := nicIch h5 h15
  simpa [imp, c, x] using h16

/-- The second Lukasiewicz axiom schema, derived from Nicod's axiom and rule. -/
theorem nicLuk2 (p : Formula α) : Provable (((∼p) ⇾ p) ⇾ p) := by
  simpa [imp, neg] using nicIsw1 (nicId (∼p))

/-- The third Lukasiewicz axiom schema, derived from Nicod's axiom and rule. -/
theorem nicLuk3 (p q : Formula α) : Provable (p ⇾ ((∼p) ⇾ q)) := by
  have hmain : Provable (((∼p) ⇾ q) ⊼ (((∼p) ⇾ q) ⊼ ((∼p) ⇾ q))) :=
    nicId ((∼p) ⇾ q)
  have hpnot : Provable (p ⊼ ∼p) := by
    simpa [neg] using nicId p
  have h : Provable (p ⊼ (((∼p) ⇾ q) ⊼ ((∼p) ⇾ q))) :=
    nicIimp2 hmain hpnot
  simpa [imp] using h

/--
The standard three-axiom Lukasiewicz Hilbert calculus for classical
propositional logic, expressed using the NAND-defined connectives `⇾` and `∼`.
-/
inductive LukasiewiczProvable : Formula α → Prop where
  | luk1 (p q r : Formula α) :
      LukasiewiczProvable ((p ⇾ q) ⇾ ((q ⇾ r) ⇾ (p ⇾ r)))
  | luk2 (p : Formula α) :
      LukasiewiczProvable (((∼p) ⇾ p) ⇾ p)
  | luk3 (p q : Formula α) :
      LukasiewiczProvable (p ⇾ ((∼p) ⇾ q))
  | mp {p q : Formula α} :
      LukasiewiczProvable p → LukasiewiczProvable (p ⇾ q) → LukasiewiczProvable q

/--
Every theorem of the standard Lukasiewicz Hilbert calculus is derivable in
Nicod's one-axiom/one-rule NAND calculus.
-/
theorem LukasiewiczProvable.toNicod {p : Formula α}
    (h : LukasiewiczProvable p) : Provable p := by
  induction h with
  | luk1 p q r => exact nicLuk1 p q r
  | luk2 p => exact nicLuk2 p
  | luk3 p q => exact nicLuk3 p q
  | mp _ _ ihp ihpq => exact nicStdmp ihp ihpq

/--
Nicod's system implements classical propositional calculus in the concrete
sense that it derives every formula provable in the standard Lukasiewicz
Hilbert calculus.
-/
theorem implementsLukasiewicz {p : Formula α}
    (h : LukasiewiczProvable p) : Provable p :=
  h.toNicod

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

/-- The implemented Lukasiewicz calculus is sound because its proofs translate to Nicod proofs. -/
theorem LukasiewiczProvable.sound {p : Formula α}
    (h : LukasiewiczProvable p) : Valid p :=
  h.toNicod.sound

end Formula

/--
The Sheffer stroke is functionally complete: validity is preserved by the
shared translation from ordinary classical formulas to NAND-only formulas.
-/
theorem toNand_valid_iff {p : Sheffer.ClassicalFormula α} :
    Formula.Valid (Sheffer.ClassicalFormula.toNand p) ↔
      ∀ v : α → Bool, Sheffer.ClassicalFormula.eval v p = true := by
  simp [Formula.Valid, Formula.eval_eq_evalWith, Sheffer.ClassicalFormula.eval_toNand]

/-- NAND as a connective on Lean propositions. -/
def propNand (p q : Prop) : Prop :=
  ¬ (p ∧ q)

infixr:60 " ⊼ₚ " => propNand

/-- The object-language NAND semantics agrees with the familiar propositional reading. -/
theorem prop_nand_not (p : Prop) : (p ⊼ₚ p) ↔ ¬ p := by
  by_cases hp : p <;> simp [propNand, hp]

/-- `p → q` expressed with NAND alone. -/
theorem prop_nand_imp (p q : Prop) : (p ⊼ₚ (q ⊼ₚ q)) ↔ (p → q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [propNand, hp, hq]

/-- `p ∧ q` expressed with NAND alone. -/
theorem prop_nand_and (p q : Prop) : ((p ⊼ₚ q) ⊼ₚ (p ⊼ₚ q)) ↔ p ∧ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [propNand, hp, hq]

/-- `p ∨ q` expressed with NAND alone. -/
theorem prop_nand_or (p q : Prop) : ((p ⊼ₚ p) ⊼ₚ (q ⊼ₚ q)) ↔ p ∨ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [propNand, hp, hq]

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
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;>
    simp [propNand, hp, hq, hr]

end Nicod

end LeanProofs
