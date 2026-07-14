/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in ../LICENSE-Apache-2.0.
Authors: Thomas Waring

Adapted and modified from leanprover/cslib's
`Cslib/Languages/CombinatoryLogic/Evaluation.lean` (blob
500a2f66a63c1395bef36ac2a101d31fd9e1776f at repository commit
e5ed905c3d004cdbf7ee1ed17ad7bee19abd7915) to
`CombinatoryLogic.SKI.Term`, its context-closed `Step` relation, and the
repository-local `Reduction.Star`. Recursion- and Rice-theorem material from
the upstream file is intentionally not included. See
../THIRD_PARTY_NOTICES.md.
-/

import CombinatoryLogic.SKIConfluence
import Mathlib.Tactic

/-!
# Evaluation and normal forms for SKI

`evalStep` implements one deterministic normal-order contraction, returning a
proof of `RedexFree` when no contraction is available.  The evaluator is
proved sound for the local context-closed `Step`.  Confluence then gives
uniqueness of redex-free normal forms.
-/

namespace CombinatoryLogic.SKI.Term

/-- A term is in normal form when it has no one-step reduct. -/
def Normal (term : Term) : Prop :=
  ∀ ⦃target : Term⦄, ¬Step term target

/-- The syntactic predicate that a term contains no SKI redex. -/
def RedexFree : Term → Prop
  | s => True
  | k => True
  | i => True
  | s ⬝ x => x.RedexFree
  | k ⬝ x => x.RedexFree
  | i ⬝ _ => False
  | s ⬝ x ⬝ y => x.RedexFree ∧ y.RedexFree
  | k ⬝ _ ⬝ _ => False
  | i ⬝ _ ⬝ _ => False
  | s ⬝ _ ⬝ _ ⬝ _ => False
  | k ⬝ _ ⬝ _ ⬝ _ => False
  | i ⬝ _ ⬝ _ ⬝ _ => False
  | a ⬝ b ⬝ c ⬝ d ⬝ e =>
      RedexFree (a ⬝ b ⬝ c ⬝ d) ∧ RedexFree e

/--
One normal-order evaluation step, or a proof that the input is redex-free.
-/
def evalStep : (term : Term) → PLift term.RedexFree ⊕ Term
  | s => Sum.inl (.up trivial)
  | k => Sum.inl (.up trivial)
  | i => Sum.inl (.up trivial)
  | s ⬝ x =>
      match x.evalStep with
      | Sum.inl proof => Sum.inl proof
      | Sum.inr x' => Sum.inr (s ⬝ x')
  | k ⬝ x =>
      match x.evalStep with
      | Sum.inl proof => Sum.inl proof
      | Sum.inr x' => Sum.inr (k ⬝ x')
  | i ⬝ x => Sum.inr x
  | s ⬝ x ⬝ y =>
      match x.evalStep, y.evalStep with
      | Sum.inl xProof, Sum.inl yProof =>
          Sum.inl (.up ⟨xProof.down, yProof.down⟩)
      | Sum.inl _, Sum.inr y' => Sum.inr (s ⬝ x ⬝ y')
      | Sum.inr x', _ => Sum.inr (s ⬝ x' ⬝ y)
  | k ⬝ x ⬝ _ => Sum.inr x
  | i ⬝ x ⬝ y => Sum.inr (x ⬝ y)
  | s ⬝ x ⬝ y ⬝ z => Sum.inr (x ⬝ z ⬝ (y ⬝ z))
  | k ⬝ x ⬝ _ ⬝ z => Sum.inr (x ⬝ z)
  | i ⬝ x ⬝ y ⬝ z => Sum.inr (x ⬝ y ⬝ z)
  | a ⬝ b ⬝ c ⬝ d ⬝ e =>
      match evalStep (a ⬝ b ⬝ c ⬝ d), evalStep e with
      | Sum.inl leftProof, Sum.inl rightProof =>
          Sum.inl (.up ⟨leftProof.down, rightProof.down⟩)
      | Sum.inl _, Sum.inr e' => Sum.inr (a ⬝ b ⬝ c ⬝ d ⬝ e')
      | Sum.inr prefix', _ => Sum.inr (prefix' ⬝ e)

/-- `evalStep`'s right branch is a genuine ordinary reduction step. -/
theorem evalStep_right_correct :
    (source target : Term) → evalStep source = Sum.inr target → Step source target
  | s ⬝ x, target, equality =>
      match hx : evalStep x with
      | Sum.inl _ => by simp only [hx, evalStep, reduceCtorEq] at equality
      | Sum.inr x' => by
          simp only [evalStep, hx, Sum.inr.injEq] at equality
          rw [← equality]
          exact .appRight s (evalStep_right_correct x x' hx)
  | k ⬝ x, target, equality =>
      match hx : evalStep x with
      | Sum.inl _ => by simp only [hx, evalStep, reduceCtorEq] at equality
      | Sum.inr x' => by
          simp only [evalStep, hx, Sum.inr.injEq] at equality
          rw [← equality]
          exact .appRight k (evalStep_right_correct x x' hx)
  | i ⬝ x, target, equality => Sum.inr.inj equality ▸ .i x
  | s ⬝ x ⬝ y, target, equality =>
      match hx : evalStep x, hy : evalStep y with
      | Sum.inl _, Sum.inl _ => by
          simp only [hx, hy, evalStep, reduceCtorEq] at equality
      | Sum.inl _, Sum.inr y' => by
          simp only [hx, hy, evalStep, Sum.inr.injEq] at equality
          rw [← equality]
          exact .appRight (s ⬝ x) (evalStep_right_correct y y' hy)
      | Sum.inr x', _ => by
          simp only [hx, hy, evalStep, Sum.inr.injEq] at equality
          rw [← equality]
          exact .appLeft y (.appRight s (evalStep_right_correct x x' hx))
  | k ⬝ x ⬝ y, target, equality => Sum.inr.inj equality ▸ .k x y
  | i ⬝ x ⬝ y, target, equality =>
      Sum.inr.inj equality ▸ .appLeft y (.i x)
  | s ⬝ x ⬝ y ⬝ z, target, equality =>
      Sum.inr.inj equality ▸ .s x y z
  | k ⬝ x ⬝ y ⬝ z, target, equality =>
      Sum.inr.inj equality ▸ .appLeft z (.k x y)
  | i ⬝ x ⬝ y ⬝ z, target, equality =>
      Sum.inr.inj equality ▸ .appLeft z (.appLeft y (.i x))
  | a ⬝ b ⬝ c ⬝ d ⬝ e, target, equality =>
      match prefixEquality : evalStep (a ⬝ b ⬝ c ⬝ d),
          rightEquality : evalStep e with
      | Sum.inl _, Sum.inl _ => by
          simp only [prefixEquality, rightEquality, evalStep, reduceCtorEq] at equality
      | Sum.inl _, Sum.inr e' => by
          simp only [prefixEquality, rightEquality, evalStep, Sum.inr.injEq] at equality
          rw [← equality]
          exact .appRight (a ⬝ b ⬝ c ⬝ d)
            (evalStep_right_correct e e' rightEquality)
      | Sum.inr prefix', _ => by
          simp only [prefixEquality, rightEquality, evalStep, Sum.inr.injEq] at equality
          rw [← equality]
          exact .appLeft e
            (evalStep_right_correct (a ⬝ b ⬝ c ⬝ d) prefix' prefixEquality)

/-- Every SKI term has positive syntax size. -/
theorem size_pos (term : Term) : 0 < term.size := by
  induction term with
  | s | k | i => simp [size]
  | app function argument functionIH argumentIH =>
      simp only [size]
      omega

/-- Ordinary SKI reduction is irreflexive. -/
theorem step_ne {source target : Term} (reduction : Step source target) :
    source ≠ target := by
  induction reduction with
  | i argument =>
      intro equality
      have sizeEquality := congrArg size equality
      have positive := size_pos argument
      simp only [size] at sizeEquality
      omega
  | k first second =>
      intro equality
      have sizeEquality := congrArg size equality
      have firstPositive := size_pos first
      have secondPositive := size_pos second
      simp only [size] at sizeEquality
      omega
  | s first second third =>
      intro equality
      have argumentEquality := (Term.app.inj equality).2
      have sizeEquality := congrArg size argumentEquality
      have secondPositive := size_pos second
      simp only [size] at sizeEquality
      omega
  | appLeft argument _ ih =>
      intro equality
      exact ih (Term.app.inj equality).1
  | appRight function _ ih =>
      intro equality
      exact ih (Term.app.inj equality).2

/-- If a term is operationally normal, `evalStep` certifies it redex-free. -/
theorem redexFree_of_normal {term : Term} (normal : Normal term) :
    term.RedexFree := by
  match equality : evalStep term with
  | Sum.inl proof => exact proof.down
  | Sum.inr target =>
      exact (normal (evalStep_right_correct term target equality)).elim

/-- A syntactically redex-free term has no ordinary reduction step. -/
theorem RedexFree.normal {term : Term} (redexFree : term.RedexFree) :
    Normal term := by
  intro target reduction
  match term, redexFree, target, reduction with
  | s ⬝ x, hx, s ⬝ y, .appRight _ childReduction =>
      exact (RedexFree.normal (term := x) hx) childReduction
  | k ⬝ x, hx, k ⬝ y, .appRight _ childReduction =>
      exact (RedexFree.normal (term := x) hx) childReduction
  | s ⬝ _ ⬝ _, ⟨hx, _⟩, s ⬝ _ ⬝ _,
      .appLeft _ (.appRight _ childReduction) =>
        exact hx.normal childReduction
  | s ⬝ _ ⬝ _, ⟨_, hy⟩, s ⬝ _ ⬝ _, .appRight _ childReduction =>
      exact hy.normal childReduction
  | _ ⬝ _ ⬝ _ ⬝ _ ⬝ _, ⟨hPrefix, _⟩, _ ⬝ _,
      .appLeft _ prefixReduction =>
        exact hPrefix.normal prefixReduction
  | _ ⬝ _ ⬝ _ ⬝ _ ⬝ _, ⟨_, hArgument⟩, _ ⬝ _,
      .appRight _ argumentReduction =>
        exact hArgument.normal argumentReduction

/-- Redex-freedom is equivalent to absence of one-step reductions. -/
theorem redexFree_iff {term : Term} : term.RedexFree ↔ Normal term :=
  ⟨RedexFree.normal, redexFree_of_normal⟩

/-- Descriptive alias for `redexFree_iff`. -/
theorem redexFree_iff_normal {term : Term} : term.RedexFree ↔ Normal term :=
  redexFree_iff

/-- `evalStep`'s left branch exactly recognizes redex-free terms. -/
theorem redexFree_iff_evalStep {term : Term} :
    term.RedexFree ↔ (evalStep term).isLeft = true := by
  constructor
  · intro redexFree
    match equality : evalStep term with
    | Sum.inl _ => rfl
    | Sum.inr target =>
        exact (redexFree.normal
          (evalStep_right_correct term target equality)).elim
  · intro isLeft
    match equality : evalStep term with
    | Sum.inl proof => exact proof.down
    | Sum.inr _ => rw [equality] at isLeft; cases isLeft

instance : DecidablePred RedexFree := fun _ =>
  decidable_of_iff' _ redexFree_iff_evalStep

/-- A redex-free term's only multi-step reduct is itself. -/
theorem redexFree_iff_steps_eq {term : Term} :
    term.RedexFree ↔ ∀ target, Steps term target ↔ term = target := by
  constructor
  · intro redexFree target
    constructor
    · intro reduction
      induction reduction with
      | refl => rfl
      | tail initialSteps step ih =>
          exact (redexFree.normal (by simpa [ih] using step)).elim
    · intro equality
      subst target
      exact .refl
  · intro onlySelf
    rw [redexFree_iff_normal]
    intro target reduction
    have equality : term = target :=
      (onlySelf target).1 (Steps.single reduction)
    exact step_ne reduction equality

/-- If a term is joinable with a redex-free term, it reduces to that term. -/
theorem steps_to_redexFree_of_joinable {source normal : Term}
    (normalFree : normal.RedexFree) (joinable : Joinable source normal) :
    Steps source normal := by
  obtain ⟨common, fromSource, fromNormal⟩ := joinable
  have normalEquality : normal = common :=
    (redexFree_iff_steps_eq.1 normalFree common).1 fromNormal
  simpa [normalEquality] using fromSource

/-- If two reducts share a source and one is normal, the other reduces to it. -/
theorem confluent_redexFree {source reduct normal : Term}
    (toReduct : Steps source reduct) (toNormal : Steps source normal)
    (normalFree : normal.RedexFree) : Steps reduct normal := by
  obtain ⟨common, fromReduct, fromNormal⟩ :=
    steps_confluent toReduct toNormal
  have normalEquality : normal = common :=
    (redexFree_iff_steps_eq.1 normalFree common).1 fromNormal
  simpa [normalEquality] using fromReduct

/-- Redex-free normal forms reached from the same source are unique. -/
theorem unique_normal_form {source left right : Term}
    (toLeft : Steps source left) (toRight : Steps source right)
    (leftFree : left.RedexFree) (rightFree : right.RedexFree) : left = right := by
  exact (redexFree_iff_steps_eq.1 leftFree right).1
    (confluent_redexFree toLeft toRight rightFree)

/-- Joinable redex-free terms are equal. -/
theorem eq_of_joinable_redexFree {left right : Term}
    (joinable : Joinable left right)
    (leftFree : left.RedexFree) (rightFree : right.RedexFree) : left = right := by
  exact (redexFree_iff_steps_eq.1 leftFree right).1
    (steps_to_redexFree_of_joinable rightFree joinable)

end CombinatoryLogic.SKI.Term
