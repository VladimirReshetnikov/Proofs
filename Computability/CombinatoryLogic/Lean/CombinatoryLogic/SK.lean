import CombinatoryLogic.Reduction

/-!
# The untyped SK combinator calculus

Pure SK has only `S`, `K`, and application.  Its one-step relation is the full
context closure of the two head contractions.
-/

namespace CombinatoryLogic.SK

/-- Terms of the pure SK combinator calculus. -/
inductive Term where
  | s
  | k
  | app (function argument : Term)
  deriving DecidableEq, Repr

namespace Term

/-- Left-associative application. -/
infixl:70 " ⬝ " => app

/-- Number of leaves and application nodes in an SK term. -/
def size : Term → Nat
  | .s | .k => 1
  | .app function argument => size function + size argument + 1

/-- The derived identity combinator `S K K`. -/
def i : Term := s ⬝ k ⬝ k

/-- One SK contraction, closed under every application context. -/
inductive Step : Term → Term → Prop where
  | k (x y : Term) : Step (k ⬝ x ⬝ y) x
  | s (x y z : Term) : Step (s ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
  | appLeft {function function' : Term} (argument : Term)
      (step : Step function function') :
      Step (function ⬝ argument) (function' ⬝ argument)
  | appRight (function : Term) {argument argument' : Term}
      (step : Step argument argument') :
      Step (function ⬝ argument) (function ⬝ argument')

/-- Zero or more SK reductions. -/
abbrev Steps := Reduction.Star Step

/-- One or more SK reductions. -/
abbrev StepsPlus := Reduction.Plus Step

namespace Steps

theorem single {a b : Term} (h : Step a b) : Steps a b := Reduction.Star.single h

theorem trans {a b c : Term} (hab : Steps a b) (hbc : Steps b c) : Steps a c :=
  Reduction.Star.trans hab hbc

theorem appLeft {a b : Term} (argument : Term) (h : Steps a b) :
    Steps (a ⬝ argument) (b ⬝ argument) := by
  induction h with
  | refl => exact Reduction.Star.refl
  | tail _ step ih => exact .tail ih (.appLeft argument step)

theorem appRight (function : Term) {a b : Term} (h : Steps a b) :
    Steps (function ⬝ a) (function ⬝ b) := by
  induction h with
  | refl => exact Reduction.Star.refl
  | tail _ step ih => exact .tail ih (.appRight function step)

theorem app {f f' x x' : Term} (hf : Steps f f') (hx : Steps x x') :
    Steps (f ⬝ x) (f' ⬝ x') :=
  (hf.appLeft x).trans (hx.appRight f')

end Steps

namespace StepsPlus

theorem single {a b : Term} (h : Step a b) : StepsPlus a b := Reduction.Plus.single h

theorem trans {a b c : Term} (hab : StepsPlus a b) (hbc : StepsPlus b c) :
    StepsPlus a c := Reduction.Plus.trans hab hbc

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

/-- The derived `S K K` has the identity head behavior. -/
theorem i_head (x : Term) : StepsPlus (i ⬝ x) x := by
  apply StepsPlus.trans (StepsPlus.single (.s k k x))
  exact StepsPlus.single (.k x (k ⬝ x))

/-- The standard self-application kernel, using the derived identity. -/
def omegaKernel : Term := s ⬝ i ⬝ i

/-- The standard looping SK term. -/
def omega : Term := omegaKernel ⬝ omegaKernel

/-- `omega` returns to itself after a nonempty SK reduction. -/
theorem omega_cycle : StepsPlus omega omega := by
  let w := omegaKernel
  apply StepsPlus.trans (StepsPlus.single (.s i i w))
  apply StepsPlus.trans ((i_head w).appLeft (i ⬝ w))
  exact (i_head w).appRight w

end Term

end CombinatoryLogic.SK
