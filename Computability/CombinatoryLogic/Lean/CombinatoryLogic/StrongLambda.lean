import CombinatoryLogic.Lambda

/-!
# Strong reduction and Church numerals for untyped lambda calculus

This module complements the weak contextual reduction in `Lambda` with full
contextual beta reduction.  In particular, `StrongStep.lamBody` permits a
reduction below a binder.  It also fixes the canonical closed Church numeral
syntax `λf. λx. fⁿ x` and establishes its basic syntactic properties.
-/

namespace CombinatoryLogic.Lambda

namespace Term

/-- One full contextual beta step, including reduction below lambdas. -/
inductive StrongStep : {n : Nat} → Term n → Term n → Prop where
  | beta {n : Nat} (body : Term (n + 1)) (argument : Term n) :
      StrongStep (.lam body ⬝ argument) (substTop argument body)
  | appLeft {n : Nat} {function function' : Term n} (argument : Term n)
      (step : StrongStep function function') :
      StrongStep (function ⬝ argument) (function' ⬝ argument)
  | appRight {n : Nat} (function : Term n) {argument argument' : Term n}
      (step : StrongStep argument argument') :
      StrongStep (function ⬝ argument) (function ⬝ argument')
  | lamBody {n : Nat} {body body' : Term (n + 1)}
      (step : StrongStep body body') :
      StrongStep (.lam body) (.lam body')

/-- Reflexive-transitive full beta reduction. -/
abbrev StrongSteps {n : Nat} := Reduction.Star (@StrongStep n)

/-- Positive full beta reduction. -/
abbrev StrongStepsPlus {n : Nat} := Reduction.Plus (@StrongStep n)

namespace StrongStepsPlus

/-- Every positive full reduction is also a reflexive-transitive reduction. -/
theorem toStrongSteps {n : Nat} {a b : Term n} (h : StrongStepsPlus a b) :
    StrongSteps a b :=
  Reduction.Plus.toStar h

end StrongStepsPlus

/-- Every weak contextual beta step is a full contextual beta step. -/
theorem step_toStrongStep {n : Nat} {a b : Term n} (h : Step a b) :
    StrongStep a b := by
  induction h with
  | beta body argument => exact .beta body argument
  | appLeft argument _ ih => exact .appLeft argument ih
  | appRight function _ ih => exact .appRight function ih

/-- Weak reflexive-transitive reduction embeds in full beta reduction. -/
theorem steps_toStrongSteps {n : Nat} {a b : Term n} (h : Steps a b) :
    StrongSteps a b := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (step_toStrongStep step)

/-- Weak positive reduction embeds in positive full beta reduction. -/
theorem stepsPlus_toStrongStepsPlus {n : Nat} {a b : Term n}
    (h : StepsPlus a b) : StrongStepsPlus a b := by
  induction h with
  | single step => exact .single (step_toStrongStep step)
  | tail _ step ih => exact .tail ih (step_toStrongStep step)

/-- A term is in strong normal form when it has no full beta successor. -/
def StrongNormal {n : Nat} (term : Term n) : Prop :=
  ∀ ⦃next : Term n⦄, ¬ StrongStep term next

/-- A term strongly normalizes when it reaches a strong normal form. -/
def StrongNormalizes {n : Nat} (term : Term n) : Prop :=
  ∃ normal : Term n, StrongSteps term normal ∧ StrongNormal normal

/-- Left-associated application to a list of arguments. -/
def applyMany {n : Nat} : Term n → List (Term n) → Term n
  | head, [] => head
  | head, argument :: arguments => applyMany (head ⬝ argument) arguments

/-- `function` iterated `count` times on `argument`. -/
def iterApp {n : Nat} (function : Term n) : Nat → Term n → Term n
  | 0, argument => argument
  | count + 1, argument => function ⬝ iterApp function count argument

/-- The open body `fⁿ x`, where variable zero is `x` and variable one is `f`. -/
def churchBody : Nat → Term 2
  | 0 => .var 0
  | count + 1 => .var 1 ⬝ churchBody count

/-- The canonical closed Church numeral `λf. λx. fⁿ x`. -/
def church (count : Nat) : Term 0 :=
  .lam (.lam (churchBody count))

@[simp] theorem churchBody_zero : churchBody 0 = .var 0 := rfl

@[simp] theorem churchBody_succ (count : Nat) :
    churchBody (count + 1) = .var 1 ⬝ churchBody count := rfl

/-- `churchBody` is precisely the generic iterated-application helper. -/
theorem churchBody_eq_iterApp (count : Nat) :
    churchBody count = iterApp (.var 1) count (.var 0) := by
  induction count with
  | zero => rfl
  | succ count ih => simp [churchBody, iterApp, ih]

/-- Variables are strong normal forms. -/
theorem var_strongNormal {n : Nat} (index : Fin n) :
    StrongNormal (.var index) := by
  intro next step
  cases step

/-- Applying a variable to a strong normal form remains strongly normal. -/
theorem appVar_strongNormal {n : Nat} (index : Fin n) {argument : Term n}
    (hArgument : StrongNormal argument) :
    StrongNormal (.var index ⬝ argument) := by
  intro next step
  cases step with
  | appLeft _ functionStep => exact var_strongNormal index functionStep
  | appRight _ argumentStep => exact hArgument argumentStep

/-- Abstracting a strong normal body preserves strong normality. -/
theorem lam_strongNormal {n : Nat} {body : Term (n + 1)}
    (hBody : StrongNormal body) : StrongNormal (.lam body) := by
  intro next step
  cases step with
  | lamBody bodyStep => exact hBody bodyStep

/-- Every canonical Church body is a strong normal form. -/
theorem churchBody_strongNormal (count : Nat) :
    StrongNormal (churchBody count) := by
  induction count with
  | zero => exact var_strongNormal 0
  | succ count ih => exact appVar_strongNormal 1 ih

/-- Every canonical closed Church numeral is a strong normal form. -/
theorem church_strongNormal (count : Nat) : StrongNormal (church count) :=
  lam_strongNormal (lam_strongNormal (churchBody_strongNormal count))

/-- Every canonical closed Church numeral strongly normalizes (in zero steps). -/
theorem church_strongNormalizes (count : Nat) :
    StrongNormalizes (church count) :=
  ⟨church count, .refl, church_strongNormal count⟩

/-- The open Church bodies encode their iteration counts injectively. -/
theorem churchBody_injective : Function.Injective churchBody := by
  intro left
  induction left with
  | zero =>
      intro right equality
      cases right with
      | zero => rfl
      | succ right => cases equality
  | succ left ih =>
      intro right equality
      cases right with
      | zero => cases equality
      | succ right =>
          exact congrArg Nat.succ (ih (Term.app.inj equality).2)

/-- Canonical closed Church numeral syntax is injective. -/
theorem church_injective : Function.Injective church := by
  intro left right equality
  exact churchBody_injective (Term.lam.inj (Term.lam.inj equality))

end Term

end CombinatoryLogic.Lambda
