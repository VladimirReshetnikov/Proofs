/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in ../LICENSE-Apache-2.0.
Authors: Thomas Waring

Adapted and modified from leanprover/cslib's
`Cslib/Languages/CombinatoryLogic/Confluence.lean` (blob
9fc3c7d18b2fc9eddaa63a59f90b8967c59a3743 at repository commit
e5ed905c3d004cdbf7ee1ed17ad7bee19abd7915) to
`CombinatoryLogic.SKI.Term`, its context-closed `Step` relation, and the
repository-local `Reduction.Star`. See ../THIRD_PARTY_NOTICES.md.
-/

import CombinatoryLogic.SKI

/-!
# Confluence of SKI reduction

This is the Tait--Martin-Loef parallel-reduction proof of Church--Rosser for
the local SKI calculus.  `ParallelReduction` contracts any collection of
disjoint redexes in one step.  It has the diamond property, and its
reflexive-transitive closure is the same as ordinary SKI reduction.
-/

namespace CombinatoryLogic.SKI.Term

/-! ## A small closure lemma independent of mathlib -/

namespace ConfluenceSupport

universe u

variable {α : Type u} {relation : α → α → Prop}

/-- A head-oriented presentation of reflexive-transitive closure. -/
inductive ForwardStar (relation : α → α → Prop) : α → α → Prop where
  | refl (a : α) : ForwardStar relation a a
  | head {a b c : α} :
      relation a b → ForwardStar relation b c → ForwardStar relation a c

namespace ForwardStar

theorem trans {a b c : α} (left : ForwardStar relation a b)
    (right : ForwardStar relation b c) : ForwardStar relation a c := by
  induction left with
  | refl => exact right
  | head step rest ih => exact .head step (ih right)

theorem toStar {a b : α} :
    ForwardStar relation a b → Reduction.Star relation a b
  | .refl _ => .refl
  | .head step rest =>
      Reduction.Star.trans (Reduction.Star.single step) (toStar rest)

theorem ofStar {a b : α} :
    Reduction.Star relation a b → ForwardStar relation a b
  | .refl => .refl _
  | .tail path step =>
      trans (ofStar path) (.head step (.refl _))

/-- One diamond step commutes with an arbitrary forward path. -/
theorem strip
    (diamond : ∀ ⦃a b c : α⦄, relation a b → relation a c →
      ∃ d, relation b d ∧ relation c d)
    {a b c : α} (step : relation a b) (path : ForwardStar relation a c) :
    ∃ d, ForwardStar relation b d ∧ ForwardStar relation c d := by
  induction path generalizing b with
  | refl =>
      exact ⟨b, .refl b, .head step (.refl b)⟩
  | head first rest ih =>
      obtain ⟨middle, fromB, fromHead⟩ := diamond step first
      obtain ⟨common, fromMiddle, fromC⟩ := ih fromHead
      exact ⟨common, .head fromB fromMiddle, fromC⟩

/-- Diamond reduction has a confluent reflexive-transitive closure. -/
theorem confluent
    (diamond : ∀ ⦃a b c : α⦄, relation a b → relation a c →
      ∃ d, relation b d ∧ relation c d)
    {a b c : α} (left : ForwardStar relation a b)
    (right : ForwardStar relation a c) :
    ∃ d, ForwardStar relation b d ∧ ForwardStar relation c d := by
  induction left generalizing c with
  | refl => exact ⟨c, right, .refl c⟩
  | head first rest ih =>
      obtain ⟨middle, fromHead, fromC⟩ := strip diamond first right
      obtain ⟨common, fromB, fromMiddle⟩ := ih fromHead
      exact ⟨common, fromB, trans fromC fromMiddle⟩

end ForwardStar

/-- Diamond reduction has a confluent repository-local `Reduction.Star`. -/
theorem star_confluent
    (diamond : ∀ ⦃a b c : α⦄, relation a b → relation a c →
      ∃ d, relation b d ∧ relation c d)
    {a b c : α} (left : Reduction.Star relation a b)
    (right : Reduction.Star relation a c) :
    ∃ d, Reduction.Star relation b d ∧ Reduction.Star relation c d := by
  obtain ⟨common, fromB, fromC⟩ :=
    ForwardStar.confluent diamond (ForwardStar.ofStar left) (ForwardStar.ofStar right)
  exact ⟨common, ForwardStar.toStar fromB, ForwardStar.toStar fromC⟩

end ConfluenceSupport

/-! ## Parallel SKI reduction -/

/-- A reduction step allowing simultaneous reduction of disjoint redexes. -/
inductive ParallelReduction : Term → Term → Prop where
  /-- Parallel reduction is reflexive. -/
  | refl (term : Term) : ParallelReduction term term
  /-- Parallel reduction contains the `I` contraction. -/
  | i (argument : Term) : ParallelReduction (i ⬝ argument) argument
  /-- Parallel reduction contains the `K` contraction. -/
  | k (first second : Term) : ParallelReduction (k ⬝ first ⬝ second) first
  /-- Parallel reduction contains the `S` contraction. -/
  | s (first second third : Term) :
      ParallelReduction (s ⬝ first ⬝ second ⬝ third)
        (first ⬝ third ⬝ (second ⬝ third))
  /-- Both children of an application may reduce simultaneously. -/
  | app {function function' argument argument' : Term} :
      ParallelReduction function function' →
      ParallelReduction argument argument' →
      ParallelReduction (function ⬝ argument) (function' ⬝ argument')

/-- Every parallel reduction is an ordinary multi-step reduction. -/
theorem steps_of_parallelReduction {source target : Term}
    (reduction : ParallelReduction source target) : Steps source target := by
  induction reduction with
  | refl => exact .refl
  | i argument => exact Steps.single (.i argument)
  | k first second => exact Steps.single (.k first second)
  | s first second third => exact Steps.single (.s first second third)
  | app functionReduction argumentReduction functionIH argumentIH =>
      exact Steps.app functionIH argumentIH

/-- Every ordinary one-step reduction is a parallel reduction. -/
theorem parallelReduction_of_step {source target : Term}
    (reduction : Step source target) : ParallelReduction source target := by
  induction reduction with
  | i argument => exact .i argument
  | k first second => exact .k first second
  | s first second third => exact .s first second third
  | appLeft argument _ ih => exact .app ih (.refl argument)
  | appRight function _ ih => exact .app (.refl function) ih

/-- Ordinary multi-step reduction embeds in parallel multi-step reduction. -/
theorem parallelSteps_of_steps {source target : Term}
    (reduction : Steps source target) :
    Reduction.Star ParallelReduction source target := by
  induction reduction with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (parallelReduction_of_step step)

/-- Parallel multi-step reduction embeds in ordinary multi-step reduction. -/
theorem steps_of_parallelSteps {source target : Term}
    (reduction : Reduction.Star ParallelReduction source target) :
    Steps source target := by
  induction reduction with
  | refl => exact .refl
  | tail _ step ih => exact Steps.trans ih (steps_of_parallelReduction step)

/-! ## Partially applied primitive combinators -/

theorem i_irreducible (target : Term) (reduction : ParallelReduction i target) :
    target = i := by
  cases reduction
  rfl

theorem k_irreducible (target : Term) (reduction : ParallelReduction k target) :
    target = k := by
  cases reduction
  rfl

theorem kApplied_irreducible (argument target : Term)
    (reduction : ParallelReduction (k ⬝ argument) target) :
    ∃ argument', ParallelReduction argument argument' ∧ target = k ⬝ argument' := by
  cases reduction with
  | refl => exact ⟨argument, .refl argument, rfl⟩
  | app functionReduction argumentReduction =>
      rename_i functionTarget argumentTarget
      rw [k_irreducible functionTarget functionReduction]
      exact ⟨argumentTarget, argumentReduction, rfl⟩

theorem s_irreducible (target : Term) (reduction : ParallelReduction s target) :
    target = s := by
  cases reduction
  rfl

theorem sApplied_irreducible (argument target : Term)
    (reduction : ParallelReduction (s ⬝ argument) target) :
    ∃ argument', ParallelReduction argument argument' ∧ target = s ⬝ argument' := by
  cases reduction with
  | refl => exact ⟨argument, .refl argument, rfl⟩
  | app functionReduction argumentReduction =>
      rename_i functionTarget argumentTarget
      rw [s_irreducible functionTarget functionReduction]
      exact ⟨argumentTarget, argumentReduction, rfl⟩

theorem sAppliedTwice_irreducible (first second target : Term)
    (reduction : ParallelReduction (s ⬝ first ⬝ second) target) :
    ∃ first' second',
      ParallelReduction first first' ∧ ParallelReduction second second' ∧
        target = s ⬝ first' ⬝ second' := by
  cases reduction with
  | refl => exact ⟨first, second, .refl first, .refl second, rfl⟩
  | app functionReduction secondReduction =>
      rename_i functionTarget secondTarget
      obtain ⟨firstTarget, firstReduction, functionEquality⟩ :=
        sApplied_irreducible first functionTarget functionReduction
      rw [functionEquality]
      exact ⟨firstTarget, secondTarget, firstReduction, secondReduction, rfl⟩

/-! ## The parallel diamond -/

/-- Parallel SKI reduction has the one-step diamond property. -/
theorem parallelReduction_diamond :
    ∀ {source left right : Term},
      ParallelReduction source left → ParallelReduction source right →
        ∃ common, ParallelReduction left common ∧ ParallelReduction right common := by
  intro source left right leftReduction rightReduction
  cases leftReduction
  case refl => exact ⟨right, rightReduction, .refl right⟩
  case app function function' argument argument' functionReduction argumentReduction =>
    cases rightReduction
    case refl =>
      exact ⟨function' ⬝ argument', .refl _,
        .app functionReduction argumentReduction⟩
    case app function'' argument'' functionReduction' argumentReduction' =>
      obtain ⟨functionCommon, functionLeft, functionRight⟩ :=
        parallelReduction_diamond functionReduction functionReduction'
      obtain ⟨argumentCommon, argumentLeft, argumentRight⟩ :=
        parallelReduction_diamond argumentReduction argumentReduction'
      exact ⟨functionCommon ⬝ argumentCommon,
        .app functionLeft argumentLeft,
        .app functionRight argumentRight⟩
    case i =>
      rw [i_irreducible function' functionReduction]
      exact ⟨argument', .i argument', argumentReduction⟩
    case k =>
      obtain ⟨first', firstReduction, functionEquality⟩ :=
        kApplied_irreducible right function' functionReduction
      rw [functionEquality]
      exact ⟨first', .k first' argument', firstReduction⟩
    case s first second =>
      obtain ⟨first', second', firstReduction, secondReduction,
          functionEquality⟩ :=
        sAppliedTwice_irreducible first second function' functionReduction
      rw [functionEquality]
      exact ⟨first' ⬝ argument' ⬝ (second' ⬝ argument'),
        .s first' second' argument',
        .app (.app firstReduction argumentReduction)
          (.app secondReduction argumentReduction)⟩
  case i =>
    cases rightReduction
    case refl => exact ⟨left, .refl left, .i left⟩
    case app functionTarget argumentTarget functionReduction argumentReduction =>
      rw [i_irreducible functionTarget functionReduction]
      exact ⟨argumentTarget, argumentReduction, .i argumentTarget⟩
    case i => exact ⟨left, .refl left, .refl left⟩
  case k second =>
    cases rightReduction
    case refl => exact ⟨left, .refl left, .k left second⟩
    case app functionTarget secondTarget functionReduction secondReduction =>
      obtain ⟨firstTarget, firstReduction, functionEquality⟩ :=
        kApplied_irreducible left functionTarget functionReduction
      rw [functionEquality]
      exact ⟨firstTarget, firstReduction, .k firstTarget secondTarget⟩
    case k => exact ⟨left, .refl left, .refl left⟩
  case s first second third =>
    cases rightReduction
    case refl =>
      exact ⟨first ⬝ third ⬝ (second ⬝ third), .refl _,
        .s first second third⟩
    case app functionTarget thirdTarget functionReduction thirdReduction =>
      obtain ⟨firstTarget, secondTarget, firstReduction, secondReduction,
          functionEquality⟩ :=
        sAppliedTwice_irreducible first second functionTarget functionReduction
      rw [functionEquality]
      exact ⟨firstTarget ⬝ thirdTarget ⬝ (secondTarget ⬝ thirdTarget),
        .app (.app firstReduction thirdReduction)
          (.app secondReduction thirdReduction),
        .s firstTarget secondTarget thirdTarget⟩
    case s =>
      exact ⟨first ⬝ third ⬝ (second ⬝ third), .refl _, .refl _⟩

/-! ## Church--Rosser -/

/-- Ordinary SKI multi-step reduction is confluent. -/
theorem steps_confluent {source left right : Term}
    (leftReduction : Steps source left) (rightReduction : Steps source right) :
    ∃ common, Steps left common ∧ Steps right common := by
  obtain ⟨common, fromLeft, fromRight⟩ :=
    ConfluenceSupport.star_confluent
      (fun {_ _ _} first second => parallelReduction_diamond first second)
      (parallelSteps_of_steps leftReduction)
      (parallelSteps_of_steps rightReduction)
  exact ⟨common, steps_of_parallelSteps fromLeft, steps_of_parallelSteps fromRight⟩

/-- Two terms are joinable when they have an ordinary common reduct. -/
def Joinable (left right : Term) : Prop :=
  ∃ common, Steps left common ∧ Steps right common

/-- Joinability of SKI terms is an equivalence relation. -/
theorem joinable_equivalence : Equivalence Joinable := by
  refine ⟨?_, ?_, ?_⟩
  · intro term
    exact ⟨term, .refl, .refl⟩
  · intro left right join
    obtain ⟨common, fromLeft, fromRight⟩ := join
    exact ⟨common, fromRight, fromLeft⟩
  · intro first second third firstSecond secondThird
    obtain ⟨leftCommon, firstReduction, secondReductionLeft⟩ := firstSecond
    obtain ⟨rightCommon, secondReductionRight, thirdReduction⟩ := secondThird
    obtain ⟨common, fromLeft, fromRight⟩ :=
      steps_confluent secondReductionLeft secondReductionRight
    exact ⟨common, Steps.trans firstReduction fromLeft,
      Steps.trans thirdReduction fromRight⟩

end CombinatoryLogic.SKI.Term
