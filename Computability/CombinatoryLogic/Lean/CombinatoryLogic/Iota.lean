import CombinatoryLogic.Reduction

/-!
# The pure universal-iota calculus and its runtime

`Iota.Term` is genuine source syntax: its only leaf is `iota`.  Reduction uses
the separate `Iota.Runtime.Term`, whose auxiliary `S` and `K` atoms are exposed
by the defining contraction `ι x ↦ x S K`.  The type boundary makes it
impossible to construct an impure source program.
-/

namespace CombinatoryLogic.Iota

/-- Pure source terms: universal iota and application only. -/
inductive Term where
  | iota
  | app (function argument : Term)
  deriving DecidableEq, Repr

namespace Term

/-- Left-associative pure application. -/
infixl:70 " ⬝ " => app

/-- Number of leaves and application nodes in a pure iota term. -/
def size : Term → Nat
  | .iota => 1
  | .app function argument => size function + size argument + 1

end Term

namespace Runtime

/-- Runtime terms, including the `S` and `K` atoms exposed by iota contraction. -/
inductive Term where
  | iota
  | s
  | k
  | app (function argument : Term)
  deriving DecidableEq, Repr

namespace Term

/-- Left-associative runtime application. -/
infixl:70 " ⬝ " => app

/-- Embed a pure source term into runtime syntax. -/
def embed : Iota.Term → Term
  | .iota => .iota
  | .app function argument => embed function ⬝ embed argument

@[simp] theorem embed_iota : embed .iota = .iota := rfl

@[simp] theorem embed_app (function argument : Iota.Term) :
    embed (.app function argument) = embed function ⬝ embed argument := rfl

/-- The source-to-runtime inclusion loses no syntax. -/
theorem embed_injective : Function.Injective embed := by
  intro a
  induction a with
  | iota =>
      intro b h
      cases b with
      | iota => rfl
      | app => simp [embed] at h
  | app f x ihf ihx =>
      intro b h
      cases b with
      | iota => simp [embed] at h
      | app f' x' =>
          have parts := Term.app.inj (by simpa [embed] using h)
          have hf : f = f' := ihf parts.1
          have hx : x = x' := ihx parts.2
          cases hf
          cases hx
          rfl

/-- One runtime contraction, closed under every application context. -/
inductive Step : Term → Term → Prop where
  | iota (x : Term) : Step (iota ⬝ x) (x ⬝ s ⬝ k)
  | k (x y : Term) : Step (k ⬝ x ⬝ y) x
  | s (x y z : Term) : Step (s ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
  | appLeft {function function' : Term} (argument : Term)
      (step : Step function function') :
      Step (function ⬝ argument) (function' ⬝ argument)
  | appRight (function : Term) {argument argument' : Term}
      (step : Step argument argument') :
      Step (function ⬝ argument) (function ⬝ argument')

/-- Zero or more runtime reductions. -/
abbrev Steps := Reduction.Star Step

/-- One or more runtime reductions. -/
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
  | tail _ step ih => exact Reduction.Star.tail ih (.appLeft argument step)

theorem appRight (function : Term) {a b : Term} (h : Steps a b) :
    Steps (function ⬝ a) (function ⬝ b) := by
  induction h with
  | refl => exact Reduction.Star.refl
  | tail _ step ih => exact Reduction.Star.tail ih (.appRight function step)

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

end Term

end Runtime

/-- Reduction between pure terms, defined by embedding both endpoints into the runtime. -/
def Reaches (source target : Term) : Prop :=
  Runtime.Term.Steps (Runtime.Term.embed source) (Runtime.Term.embed target)

/-- Positive reduction between pure terms through the runtime inclusion. -/
def ReachesPlus (source target : Term) : Prop :=
  Runtime.Term.StepsPlus (Runtime.Term.embed source) (Runtime.Term.embed target)

end CombinatoryLogic.Iota
