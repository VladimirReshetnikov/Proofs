/-!
# The Sheffer-stroke language and classical translations

Shared core-only vocabulary for the single-binary-connective propositional
modules `LeanProofs.Nicod` (NAND syntax, Nicod's one-axiom calculus) and
`LeanProofs.WolframBoolean` (Wolfram's and Meredith's equational axioms):

* the two Boolean Sheffer strokes, NAND and NOR;
* formulas over one anonymous binary stroke;
* the ordinary classical propositional language;
* the truth-preserving translations from the classical language into pure
  stroke formulas, for both stroke conventions.

The module deliberately has no imports, so both consumers stay core-only.
-/

namespace LeanProofs

namespace Sheffer

/-- NAND on truth values. -/
def boolNand (p q : Bool) : Bool :=
  !(p && q)

/-- NOR on truth values, the order-dual Sheffer stroke. -/
def boolNor (p q : Bool) : Bool :=
  !(p || q)

/-- Formulas whose only logical connective is one anonymous binary stroke. -/
inductive StrokeFormula (α : Type u) : Type u where
  | atom : α → StrokeFormula α
  | stroke : StrokeFormula α → StrokeFormula α → StrokeFormula α
  deriving DecidableEq, Repr

namespace StrokeFormula

infixr:60 " ⊙ " => StrokeFormula.stroke

/-- Semantics of a stroke formula under a chosen truth-table operation. -/
def evalWith (op : Bool → Bool → Bool) (v : α → Bool) : StrokeFormula α → Bool
  | atom a => v a
  | p ⊙ q => op (evalWith op v p) (evalWith op v q)

end StrokeFormula

/-- A standard classical propositional language. -/
inductive ClassicalFormula (α : Type u) : Type u where
  | atom : α → ClassicalFormula α
  | neg : ClassicalFormula α → ClassicalFormula α
  | and : ClassicalFormula α → ClassicalFormula α → ClassicalFormula α
  | or : ClassicalFormula α → ClassicalFormula α → ClassicalFormula α
  | imp : ClassicalFormula α → ClassicalFormula α → ClassicalFormula α
  | iff : ClassicalFormula α → ClassicalFormula α → ClassicalFormula α
  deriving DecidableEq, Repr

namespace ClassicalFormula

open StrokeFormula

/-- Boolean semantics for the usual classical connectives. -/
def eval (v : α → Bool) : ClassicalFormula α → Bool
  | atom a => v a
  | neg p => !(eval v p)
  | and p q => eval v p && eval v q
  | or p q => eval v p || eval v q
  | imp p q => !(eval v p) || eval v q
  | iff p q => eval v p == eval v q

/-- Translate ordinary classical formulas to NAND-only stroke formulas. -/
def toNand : ClassicalFormula α → StrokeFormula α
  | atom a => StrokeFormula.atom a
  | neg p =>
      let p' := toNand p
      p' ⊙ p'
  | and p q =>
      let pq := toNand p ⊙ toNand q
      pq ⊙ pq
  | or p q =>
      (toNand p ⊙ toNand p) ⊙ (toNand q ⊙ toNand q)
  | imp p q =>
      toNand p ⊙ (toNand q ⊙ toNand q)
  | iff p q =>
      let p' := toNand p
      let q' := toNand q
      let both := (p' ⊙ (q' ⊙ q')) ⊙ (q' ⊙ (p' ⊙ p'))
      both ⊙ both

/-- Translate ordinary classical formulas to NOR-only stroke formulas. -/
def toNor : ClassicalFormula α → StrokeFormula α
  | atom a => StrokeFormula.atom a
  | neg p =>
      let p' := toNor p
      p' ⊙ p'
  | and p q =>
      (toNor p ⊙ toNor p) ⊙ (toNor q ⊙ toNor q)
  | or p q =>
      let pq := toNor p ⊙ toNor q
      pq ⊙ pq
  | imp p q =>
      let npq := (toNor p ⊙ toNor p) ⊙ toNor q
      npq ⊙ npq
  | iff p q =>
      let p' := toNor p
      let q' := toNor q
      let pq := ((p' ⊙ p') ⊙ q') ⊙ ((p' ⊙ p') ⊙ q')
      let qp := ((q' ⊙ q') ⊙ p') ⊙ ((q' ⊙ q') ⊙ p')
      (pq ⊙ pq) ⊙ (qp ⊙ qp)

/-- The Sheffer stroke read as NAND expresses every ordinary classical connective. -/
theorem eval_toNand (v : α → Bool) :
    ∀ p : ClassicalFormula α, (toNand p).evalWith boolNand v = eval v p
  | atom _ => rfl
  | neg p => by
      cases hp : eval v p <;>
        simp [toNand, eval, StrokeFormula.evalWith, boolNand, eval_toNand v p, hp]
  | and p q => by
      cases hp : eval v p <;> cases hq : eval v q <;>
        simp [toNand, eval, StrokeFormula.evalWith, boolNand,
          eval_toNand v p, eval_toNand v q, hp, hq]
  | or p q => by
      cases hp : eval v p <;> cases hq : eval v q <;>
        simp [toNand, eval, StrokeFormula.evalWith, boolNand,
          eval_toNand v p, eval_toNand v q, hp, hq]
  | imp p q => by
      cases hp : eval v p <;> cases hq : eval v q <;>
        simp [toNand, eval, StrokeFormula.evalWith, boolNand,
          eval_toNand v p, eval_toNand v q, hp, hq]
  | iff p q => by
      cases hp : eval v p <;> cases hq : eval v q <;>
        simp [toNand, eval, StrokeFormula.evalWith, boolNand,
          eval_toNand v p, eval_toNand v q, hp, hq]

/-- The Sheffer stroke read as NOR expresses every ordinary classical connective. -/
theorem eval_toNor (v : α → Bool) :
    ∀ p : ClassicalFormula α, (toNor p).evalWith boolNor v = eval v p
  | atom _ => rfl
  | neg p => by
      cases hp : eval v p <;>
        simp [toNor, eval, StrokeFormula.evalWith, boolNor, eval_toNor v p, hp]
  | and p q => by
      cases hp : eval v p <;> cases hq : eval v q <;>
        simp [toNor, eval, StrokeFormula.evalWith, boolNor,
          eval_toNor v p, eval_toNor v q, hp, hq]
  | or p q => by
      cases hp : eval v p <;> cases hq : eval v q <;>
        simp [toNor, eval, StrokeFormula.evalWith, boolNor,
          eval_toNor v p, eval_toNor v q, hp, hq]
  | imp p q => by
      cases hp : eval v p <;> cases hq : eval v q <;>
        simp [toNor, eval, StrokeFormula.evalWith, boolNor,
          eval_toNor v p, eval_toNor v q, hp, hq]
  | iff p q => by
      cases hp : eval v p <;> cases hq : eval v q <;>
        simp [toNor, eval, StrokeFormula.evalWith, boolNor,
          eval_toNor v p, eval_toNor v q, hp, hq]

end ClassicalFormula

end Sheffer

end LeanProofs
