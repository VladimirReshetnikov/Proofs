/-
WIP SNAPSHOT — INTENTIONALLY DISABLED.

This Church-observation development has not yet passed the repository's Lean
gate. It is preserved verbatim below for continuation, but the entire source
is commented out so this checkpoint does not expose unverified declarations.

/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in ../LICENSE-Apache-2.0.
Authors: Thomas Waring

The `churchK` normal-form argument is adapted and modified from
leanprover/cslib's `Cslib/Languages/CombinatoryLogic/Evaluation.lean`
(blob 500a2f66a63c1395bef36ac2a101d31fd9e1776f at repository commit
e5ed905c3d004cdbf7ee1ed17ad7bee19abd7915). It is connected here to the
local `IsChurch`, `toChurch`, and `ObservesChurch` relations. See
../THIRD_PARTY_NOTICES.md.
-/

import CombinatoryLogic.SKIArithmetic
import CombinatoryLogic.SKIEvaluation

/-!
# Confluence and Church-numeral observations

Applying an extensional Church representative to `K` twice produces the
redex-free spine `churchK n`.  Confluence therefore makes this observation
single-valued, even though the representing SKI term itself need not be in
normal form.
-/

namespace CombinatoryLogic.SKI.Term

/-- A redex-free specialization of `Church n` obtained by iterating `K`. -/
def churchK : Nat → Term
  | 0 => k
  | n + 1 => k ⬝ churchK n

/-- `churchK` is exactly `Church` specialized to `K` and `K`. -/
theorem churchK_church : ∀ n, churchK n = Church n k k
  | 0 => rfl
  | n + 1 => by simp [churchK, Church, churchK_church n]

/-- Every specialized numeral probe is redex-free. -/
theorem churchK_redexFree : ∀ n, RedexFree (churchK n)
  | 0 => by simp [churchK, RedexFree]
  | n + 1 => by simpa [churchK, RedexFree] using churchK_redexFree n

/-- Exact local syntax size of the specialized numeral probe. -/
@[simp] theorem churchK_size : ∀ n, (churchK n).size = 2 * n + 1
  | 0 => rfl
  | n + 1 => by
      rw [churchK, size, churchK_size]
      omega

/-- The specialized numeral probes have distinct syntax. -/
theorem churchK_injective : Function.Injective churchK := by
  intro left right equality
  have sizeEquality := congrArg size equality
  simp only [churchK_size] at sizeEquality
  omega

/-- A one-shot observation of a Church numeral through two `K` arguments. -/
def ObservesChurch (n : Nat) (term : Term) : Prop :=
  Steps (term ⬝ k ⬝ k) (churchK n)

/-- Every extensional Church representative has its expected observation. -/
theorem observesChurch_of_isChurch {n : Nat} {term : Term}
    (isChurch : IsChurch n term) : ObservesChurch n term := by
  simpa only [ObservesChurch, churchK_church] using isChurch k k

/-- Observation is preserved backwards along ordinary reduction. -/
theorem ObservesChurch.of_steps {n : Nat} {source target : Term}
    (reduction : Steps source target) (observation : ObservesChurch n target) :
    ObservesChurch n source := by
  unfold ObservesChurch at observation ⊢
  exact (Steps.appLeft k (Steps.appLeft k reduction)).trans observation

/-- A single term cannot produce two distinct Church observations. -/
theorem observesChurch_unique {term : Term} {left right : Nat}
    (leftObservation : ObservesChurch left term)
    (rightObservation : ObservesChurch right term) : left = right := by
  apply churchK_injective
  exact unique_normal_form leftObservation rightObservation
    (churchK_redexFree left) (churchK_redexFree right)

/-- The canonical arithmetic representative has its canonical observation. -/
theorem toChurch_observes (n : Nat) : ObservesChurch n (toChurch n) :=
  observesChurch_of_isChurch (toChurch_correct n)

/-- The index of a Church representation of one fixed term is unique. -/
theorem isChurch_index_unique {term : Term} {left right : Nat}
    (leftChurch : IsChurch left term) (rightChurch : IsChurch right term) :
    left = right :=
  observesChurch_unique (observesChurch_of_isChurch leftChurch)
    (observesChurch_of_isChurch rightChurch)

/--
Joinable Church representatives have the same natural-number index.

This is the extensional Church-numeral injectivity theorem: confluence is used
after lifting the common reduct through the two probing applications.
-/
theorem isChurch_injective (leftTerm rightTerm : Term) (left right : Nat)
    (leftChurch : IsChurch left leftTerm)
    (rightChurch : IsChurch right rightTerm)
    (joinable : Joinable leftTerm rightTerm) : left = right := by
  obtain ⟨common, leftToCommon, rightToCommon⟩ := joinable
  have leftProbeToCommon :
      Steps (leftTerm ⬝ k ⬝ k) (common ⬝ k ⬝ k) :=
    Steps.appLeft k (Steps.appLeft k leftToCommon)
  have rightProbeToCommon :
      Steps (rightTerm ⬝ k ⬝ k) (common ⬝ k ⬝ k) :=
    Steps.appLeft k (Steps.appLeft k rightToCommon)
  have commonToLeft : Steps (common ⬝ k ⬝ k) (churchK left) :=
    confluent_redexFree leftProbeToCommon
      (observesChurch_of_isChurch leftChurch) (churchK_redexFree left)
  have commonToRight : Steps (common ⬝ k ⬝ k) (churchK right) :=
    confluent_redexFree rightProbeToCommon
      (observesChurch_of_isChurch rightChurch) (churchK_redexFree right)
  exact churchK_injective
    (unique_normal_form commonToLeft commonToRight
      (churchK_redexFree left) (churchK_redexFree right))

end CombinatoryLogic.SKI.Term
-/
