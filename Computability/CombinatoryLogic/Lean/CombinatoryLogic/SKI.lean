import CombinatoryLogic.Reduction

/-!
# The untyped SKI combinator calculus

This module gives the syntax and the full context closure of the three usual
head reductions.  `Steps` is reflexive-transitive closure; `StepsPlus` records
one or more genuine reduction steps.
-/

namespace CombinatoryLogic.SKI

/-- Terms of the untyped SKI combinator calculus. -/
inductive Term where
  | s
  | k
  | i
  | app (function argument : Term)
  deriving DecidableEq, Repr

namespace Term

/-- Left-associative application. -/
infixl:70 " ⬝ " => app

/-- Number of leaves and application nodes in an SKI term. -/
def size : Term → Nat
  | .s | .k | .i => 1
  | .app function argument => size function + size argument + 1

/-- One SKI contraction, closed under every application context. -/
inductive Step : Term → Term → Prop where
  | i (x : Term) : Step (i ⬝ x) x
  | k (x y : Term) : Step (k ⬝ x ⬝ y) x
  | s (x y z : Term) : Step (s ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
  | appLeft {function function' : Term} (argument : Term)
      (step : Step function function') :
      Step (function ⬝ argument) (function' ⬝ argument)
  | appRight (function : Term) {argument argument' : Term}
      (step : Step argument argument') :
      Step (function ⬝ argument) (function ⬝ argument')

/-- Zero or more SKI reductions. -/
abbrev Steps := Reduction.Star Step

/-- One or more SKI reductions. -/
abbrev StepsPlus := Reduction.Plus Step

namespace Steps

theorem single {a b : Term} (h : Step a b) : Steps a b :=
  Reduction.Star.single h

theorem trans {a b c : Term} (hab : Steps a b) (hbc : Steps b c) : Steps a c :=
  Reduction.Star.trans hab hbc

theorem appLeft {a b : Term} (argument : Term) (h : Steps a b) :
    Steps (a ⬝ argument) (b ⬝ argument) := by
  induction h with
  | refl => exact Reduction.Star.refl
  | tail _ step ih =>
      exact Reduction.Star.tail ih (.appLeft argument step)

theorem appRight (function : Term) {a b : Term} (h : Steps a b) :
    Steps (function ⬝ a) (function ⬝ b) := by
  induction h with
  | refl => exact Reduction.Star.refl
  | tail _ step ih =>
      exact Reduction.Star.tail ih (.appRight function step)

theorem app {f f' x x' : Term} (hf : Steps f f') (hx : Steps x x') :
    Steps (f ⬝ x) (f' ⬝ x') :=
  (hf.appLeft x).trans (hx.appRight f')

end Steps

namespace StepsPlus

theorem single {a b : Term} (h : Step a b) : StepsPlus a b :=
  Reduction.Plus.single h

theorem trans {a b c : Term} (hab : StepsPlus a b) (hbc : StepsPlus b c) :
    StepsPlus a c :=
  Reduction.Plus.trans hab hbc

theorem appLeft {a b : Term} (argument : Term) (h : StepsPlus a b) :
    StepsPlus (a ⬝ argument) (b ⬝ argument) := by
  induction h with
  | single step => exact .single (.appLeft argument step)
  | tail _ step ih => exact .tail ih (.appLeft argument step)

theorem appRight (function : Term) {a b : Term} (h : StepsPlus a b) :
    StepsPlus (function ⬝ a) (function ⬝ b) := by
  induction h with
  | single step => exact .single (.appRight function step)
  | tail _ step ih => exact .tail ih (.appRight function step)

theorem toSteps {a b : Term} (h : StepsPlus a b) : Steps a b :=
  Reduction.Plus.toStar h

end StepsPlus

/-- The usual self-application kernel `S I I`. -/
def omegaKernel : Term := s ⬝ i ⬝ i

/-- The standard looping SKI term `(S I I) (S I I)`. -/
def omega : Term := omegaKernel ⬝ omegaKernel

/-- `omega` returns to itself after three genuine SKI steps. -/
theorem omega_cycle : StepsPlus omega omega := by
  let w := omegaKernel
  have h₁ : Step (w ⬝ w) (i ⬝ w ⬝ (i ⬝ w)) := by
    exact .s i i w
  have h₂ : Step (i ⬝ w ⬝ (i ⬝ w)) (w ⬝ (i ⬝ w)) := by
    exact .appLeft (i ⬝ w) (.i w)
  have h₃ : Step (w ⬝ (i ⬝ w)) (w ⬝ w) := by
    exact .appRight w (.i w)
  exact (Reduction.Plus.single h₁).tail h₂ |>.tail h₃

end Term

end CombinatoryLogic.SKI
