import Std

/-!
# Dependency-free reduction closures

Small reflexive-transitive and positive transitive closures shared by the SKI
and iota calculi.  Keeping them here makes this project independent of mathlib.
-/

namespace CombinatoryLogic.Reduction

universe u
variable {α : Type u} {r : α → α → Prop} {a b c : α}

/-- Reflexive-transitive closure of a relation. -/
inductive Star (r : α → α → Prop) (a : α) : α → Prop where
  | refl : Star r a a
  | tail {b c : α} : Star r a b → r b c → Star r a c

namespace Star

theorem single (h : r a b) : Star r a b :=
  .tail .refl h

theorem trans (hab : Star r a b) (hbc : Star r b c) : Star r a c := by
  induction hbc with
  | refl => exact hab
  | tail _ step ih => exact .tail ih step

end Star

/-- Positive transitive closure: one or more relation steps. -/
inductive Plus (r : α → α → Prop) (a : α) : α → Prop where
  | single {b : α} : r a b → Plus r a b
  | tail {b c : α} : Plus r a b → r b c → Plus r a c

namespace Plus

theorem trans (hab : Plus r a b) (hbc : Plus r b c) : Plus r a c := by
  induction hbc with
  | single step => exact .tail hab step
  | tail _ step ih => exact .tail ih step

theorem toStar (h : Plus r a b) : Star r a b := by
  induction h with
  | single step => exact Star.single step
  | tail _ step ih => exact .tail ih step

private theorem ofStarThenStep {a b c : α} (hab : Star r a b) (step : r b c) :
    Plus r a c := by
  induction hab generalizing c with
  | refl => exact .single step
  | tail _ previous ih => exact .tail (ih previous) step

theorem transRight (hab : Star r a b) (hbc : Plus r b c) : Plus r a c := by
  induction hbc with
  | single step => exact ofStarThenStep hab step
  | tail _ step ih => exact .tail ih step

end Plus

end CombinatoryLogic.Reduction
