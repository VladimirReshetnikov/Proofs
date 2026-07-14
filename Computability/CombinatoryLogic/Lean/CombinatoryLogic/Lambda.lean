import CombinatoryLogic.Reduction

/-!
# Scope-safe untyped lambda calculus

`Term n` has exactly `n` variables, represented by `Fin n`; a lambda body is a
`Term (n+1)`.  This indexed presentation is the strictly-positive Lean
equivalent of the usual `Option`-scoped syntax.  Reduction is weak contextual
beta: application contexts reduce, lambda bodies do not.
-/

namespace CombinatoryLogic.Lambda

/-- Untyped lambda terms in a context of `n` variables. -/
inductive Term : Nat → Type where
  | var {n : Nat} (index : Fin n) : Term n
  | app {n : Nat} (function argument : Term n) : Term n
  | lam {n : Nat} (body : Term (n + 1)) : Term n
  deriving Repr

namespace Term

infixl:70 " ⬝ " => app

/-- Rename all variables. -/
def rename {n m : Nat} (f : Fin n → Fin m) : Term n → Term m
  | .var index => .var (f index)
  | .app function argument => rename f function ⬝ rename f argument
  | .lam body => .lam (rename (Fin.cases 0 (Fin.succ ∘ f)) body)

/-- Lift a simultaneous substitution through one binder. -/
def liftSubst {n m : Nat} (σ : Fin n → Term m) : Fin (n + 1) → Term (m + 1) :=
  Fin.cases (.var 0) (fun index => rename Fin.succ (σ index))

/-- A lifted substitution fixes the variable introduced by the binder. -/
@[simp] theorem liftSubst_zero (σ : Fin n → Term m) :
    liftSubst σ (0 : Fin (n + 1)) = .var 0 := rfl

/-- A lifted substitution weakens the image of every pre-existing variable. -/
@[simp] theorem liftSubst_succ (σ : Fin n → Term m) (index : Fin n) :
    liftSubst σ index.succ = rename Fin.succ (σ index) := rfl

/-- Explicit form of `liftSubst_succ` at the first pre-existing variable. -/
@[simp] theorem liftSubst_one (σ : Fin (n + 1) → Term m) :
    liftSubst σ (1 : Fin (n + 2)) = rename Fin.succ (σ 0) := by
  have indexEquality :
      (1 : Fin (n + 2)) = Fin.succ (0 : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  rw [indexEquality]
  exact liftSubst_succ σ 0

/-- Explicit form of `liftSubst_succ` at the second pre-existing variable. -/
@[simp] theorem liftSubst_two (σ : Fin (n + 2) → Term m) :
    liftSubst σ (2 : Fin (n + 3)) =
      rename Fin.succ (σ (1 : Fin (n + 2))) := by
  have indexEquality :
      (2 : Fin (n + 3)) = Fin.succ (1 : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  rw [indexEquality]
  exact liftSubst_succ σ 1

/-- Capture-avoiding simultaneous substitution. -/
def bind {n m : Nat} (σ : Fin n → Term m) : Term n → Term m
  | .var index => σ index
  | .app function argument => bind σ function ⬝ bind σ argument
  | .lam body => .lam (bind (liftSubst σ) body)

/-- Substitute an argument for variable zero and lower the remaining variables. -/
def substTop {n : Nat} (argument : Term n) (body : Term (n + 1)) : Term n :=
  bind (Fin.cases argument .var) body

/-- One weak contextual beta step. -/
inductive Step {n : Nat} : Term n → Term n → Prop where
  | beta (body : Term (n + 1)) (argument : Term n) :
      Step (.lam body ⬝ argument) (substTop argument body)
  | appLeft {function function' : Term n} (argument : Term n)
      (step : Step function function') :
      Step (function ⬝ argument) (function' ⬝ argument)
  | appRight (function : Term n) {argument argument' : Term n}
      (step : Step argument argument') :
      Step (function ⬝ argument) (function ⬝ argument')

abbrev Steps {n : Nat} := Reduction.Star (@Step n)
abbrev StepsPlus {n : Nat} := Reduction.Plus (@Step n)

namespace StepsPlus

theorem toSteps {n : Nat} {a b : Term n} (h : StepsPlus a b) : Steps a b :=
  Reduction.Plus.toStar h

end StepsPlus

/-- The usual self-application kernel `λx. x x`. -/
def omegaKernel : Term 0 := .lam (.var 0 ⬝ .var 0)

/-- The standard looping closed lambda term. -/
def omega : Term 0 := omegaKernel ⬝ omegaKernel

/-- Weak beta reduction returns `omega` to itself in one genuine step. -/
theorem omega_cycle : StepsPlus omega omega := by
  exact .single (.beta (.var 0 ⬝ .var 0) omegaKernel)

end Term

end CombinatoryLogic.Lambda
