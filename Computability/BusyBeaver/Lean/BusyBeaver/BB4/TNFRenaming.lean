/-
  BusyBeaverBB4/TNFRenaming.lean

  Semantic state renaming for four-state Rado machines.  This is the
  equivalence used by the tree-normal-form search when a transition first
  enters an as-yet unnamed state.
-/

import BusyBeaver.BB4.Search

namespace SetTheory
namespace BusyBeaver
namespace BB4
namespace TNF

/-- A deliberately tiny permutation interface, kept local so the standalone
SetTheory development does not acquire a Mathlib dependency merely for state
renaming. -/
structure Perm where
  toFun : Fin 4 -> Fin 4
  invFun : Fin 4 -> Fin 4
  left_inv : forall state, invFun (toFun state) = state
  right_inv : forall state, toFun (invFun state) = state

instance : CoeFun Perm (fun _ => Fin 4 -> Fin 4) :=
  ⟨Perm.toFun⟩

namespace Perm

def symm (permutation : Perm) : Perm where
  toFun := permutation.invFun
  invFun := permutation.toFun
  left_inv := permutation.right_inv
  right_inv := permutation.left_inv

@[simp]
theorem symm_apply_apply (permutation : Perm) (state : Fin 4) :
    permutation.symm (permutation state) = state :=
  permutation.left_inv state

@[simp]
theorem apply_symm_apply (permutation : Perm) (state : Fin 4) :
    permutation (permutation.symm state) = state :=
  permutation.right_inv state

theorem injective (permutation : Perm) : Function.Injective permutation := by
  intro left right hEq
  simpa using congrArg permutation.symm hEq

private def swapFun (left right state : Fin 4) : Fin 4 :=
  if state = left then right else if state = right then left else state

def swap (left right : Fin 4) : Perm where
  toFun := swapFun left right
  invFun := swapFun left right
  left_inv := by
    intro state
    by_cases hLeft : state = left
    · subst state
      by_cases hEq : right = left
      · subst right
        simp [swapFun]
      · simp [swapFun, hEq]
    · by_cases hRight : state = right
      · subst state
        simp [swapFun, hLeft]
      · simp [swapFun, hLeft, hRight]
  right_inv := by
    intro state
    by_cases hLeft : state = left
    · subst state
      by_cases hEq : right = left
      · subst right
        simp [swapFun]
      · simp [swapFun, hEq]
    · by_cases hRight : state = right
      · subst state
        simp [swapFun, hLeft]
      · simp [swapFun, hLeft, hRight]

@[simp]
theorem swap_apply_left (left right : Fin 4) : swap left right left = right := by
  simp [swap, swapFun]

theorem swap_apply_of_ne_of_ne {left right state : Fin 4}
    (hLeft : state ≠ left) (hRight : state ≠ right) :
    swap left right state = state := by
  simp [swap, swapFun, hLeft, hRight]

end Perm

namespace Rename

def action (equiv : Perm) (value : Action 4) : Action 4 where
  write := value.write
  move := value.move
  next := value.next.map equiv

def machine (equiv : Perm) (value : Machine 4) : Machine 4 where
  transition state bit := action equiv (value.transition (equiv.symm state) bit)

def config (equiv : Perm) (value : Config 4) : Config 4 where
  state := value.state.map equiv
  head := value.head
  tape := value.tape

@[simp]
theorem config_state (equiv : Perm) (value : Config 4) :
    (config equiv value).state = value.state.map equiv :=
  rfl

@[simp]
theorem config_head (equiv : Perm) (value : Config 4) :
    (config equiv value).head = value.head :=
  rfl

@[simp]
theorem config_tape (equiv : Perm) (value : Config 4) :
    (config equiv value).tape = value.tape :=
  rfl

@[simp]
theorem config_initial (equiv : Perm)
    (hStart : equiv (0 : Fin 4) = 0) :
    config equiv (initial 4) = initial 4 := by
  simp [config, initial, startState, hStart]

@[simp]
theorem step (equiv : Perm) (value : Machine 4)
    (cfg : Config 4) :
    (machine equiv value).step (config equiv cfg) =
      config equiv (value.step cfg) := by
  cases cfg with
  | mk state head tape =>
      cases state with
      | none => rfl
      | some state =>
          simp [machine, action, config, Machine.step]

@[simp]
theorem runFrom (equiv : Perm) (value : Machine 4)
    (cfg : Config 4) : forall steps,
    (machine equiv value).runFrom (config equiv cfg) steps =
      config equiv (value.runFrom cfg steps)
  | 0 => rfl
  | steps + 1 => by
      simp [Machine.runFrom, runFrom equiv value cfg steps]

@[simp]
theorem run (equiv : Perm) (value : Machine 4)
    (hStart : equiv (0 : Fin 4) = 0) : forall steps,
    (machine equiv value).run steps = config equiv (value.run steps)
  | 0 => by simp [Machine.run, config_initial equiv hStart]
  | steps + 1 => by
      simp [Machine.run, run equiv value hStart steps]

/-- State permutation preserves halting and the exact busy-beaver score. -/
theorem haltsWithScore_iff (equiv : Perm)
    (value : Machine 4) (hStart : equiv (0 : Fin 4) = 0) (score : Nat) :
    (machine equiv value).HaltsWithScore score ↔ value.HaltsWithScore score := by
  constructor
  · rintro ⟨steps, hState, hScore⟩
    rw [run equiv value hStart steps] at hState hScore
    refine ⟨steps, ?_, ?_⟩
    · cases hOriginal : (value.run steps).state with
      | none => rfl
      | some state => simp [config, hOriginal] at hState
    · simpa [config] using hScore
  · rintro ⟨steps, hState, hScore⟩
    refine ⟨steps, ?_, ?_⟩
    · rw [run equiv value hStart steps]
      simp [config, hState]
    · rw [run equiv value hStart steps]
      simpa [config] using hScore

def FixesPrefix (used : Nat) (equiv : Perm) : Prop :=
  forall state, state.val < used -> equiv state = state

theorem swap_fixesPrefix {used : Nat} {left right : Fin 4}
    (hLeft : used <= left.val) (hRight : used <= right.val) :
    FixesPrefix used (Perm.swap left right) := by
  intro state hState
  apply Perm.swap_apply_of_ne_of_ne
  · intro hEq
    subst left
    omega
  · intro hEq
    subst right
    omega

theorem fixesPrefix_zero {used : Nat} (hUsed : 0 < used)
    {equiv : Perm} (hFix : FixesPrefix used equiv) :
    equiv (0 : Fin 4) = 0 :=
  hFix 0 hUsed

end Rename

end TNF
end BB4
end BusyBeaver
end SetTheory
