/-
  BusyBeaverBB4/TNFReflection.lean

  Exact left/right reflection of Rado machines.  The reflected blank run has
  the same states and score, with every tape coordinate and head negated.
-/

import SetTheory.BusyBeaverBB4.TNF

namespace SetTheory
namespace BusyBeaver
namespace BB4
namespace TNF
namespace Reflect

def tape (value : Tape) : Tape :=
  value.map fun position => -position

theorem mem_tape_neg_iff (value : Tape) (position : Int) :
    -position ∈ tape value ↔ position ∈ value := by
  constructor
  · intro hMem
    rcases List.mem_map.mp hMem with ⟨source, hSource, hEq⟩
    have hPosition : source = position := by omega
    simpa [hPosition] using hSource
  · intro hMem
    exact List.mem_map.mpr ⟨position, hMem, rfl⟩

@[simp]
theorem read (value : Tape) (position : Int) :
    Tape.read (tape value) (-position) = Tape.read value position := by
  simp [Tape.read, mem_tape_neg_iff]

private theorem bne_neg_iff (left right : Int) :
    (-left != -right) = (left != right) := by
  by_cases hEq : left = right
  · subst right
    simp
  · have hNeg : -left ≠ -right := by omega
    exact Eq.trans (bne_iff_ne.mpr hNeg) (bne_iff_ne.mpr hEq).symm

@[simp]
theorem tape_filter_ne (value : Tape) (position : Int) :
    tape (value.filter fun source => source != position) =
      (tape value).filter fun source => source != -position := by
  induction value with
  | nil => rfl
  | cons head tail ih =>
      by_cases hEq : head != position
      · have hNeg : (-head != -position) = true := by
          simpa [bne_neg_iff] using hEq
        simp [tape, List.filter, hEq, hNeg]
        simpa [tape] using ih
      · have hFalse : (head != position) = false := Bool.eq_false_iff.mpr hEq
        have hNeg : (-head != -position) = false := by
          simpa [bne_neg_iff] using hFalse
        simp [tape, List.filter, hFalse, hNeg]
        simpa [tape] using ih

@[simp]
theorem write (value : Tape) (position : Int) (bit : Bool) :
    tape (Tape.write value position bit) =
      Tape.write (tape value) (-position) bit := by
  cases bit
  · simp [Tape.write, tape_filter_ne]
  · by_cases hMem : position ∈ value
    · have hNeg : -position ∈ tape value :=
        (mem_tape_neg_iff value position).2 hMem
      simp [Tape.write, hMem, hNeg]
    · have hNeg : -position ∉ tape value := by
        simpa [mem_tape_neg_iff] using hMem
      simp [Tape.write, hMem, tape]

def move : Move -> Move
  | .left => .right
  | .right => .left

@[simp]
theorem move_apply (direction : Move) (position : Int) :
    (move direction).apply (-position) = -(direction.apply position) := by
  cases direction <;> simp [move, Move.apply] <;> omega

def action (value : Action 4) : Action 4 where
  write := value.write
  move := move value.move
  next := value.next

def goAction (value : GoAction) : GoAction where
  write := value.write
  move := move value.move
  next := value.next

@[simp]
theorem goAction_toAction (value : GoAction) :
    (goAction value).toAction = action value.toAction := by
  cases value
  rfl

def machine (value : Machine 4) : Machine 4 where
  transition state bit := action (value.transition state bit)

def config (value : Config 4) : Config 4 where
  state := value.state
  head := -value.head
  tape := tape value.tape

@[simp]
theorem config_state (value : Config 4) : (config value).state = value.state :=
  rfl

@[simp]
theorem config_tape_length (value : Config 4) :
    (config value).tape.length = value.tape.length := by
  simp [config, tape]

@[simp]
theorem config_initial : config (initial 4) = initial 4 := by
  simp [config, initial, tape, startState]

@[simp]
theorem step (value : Machine 4) (cfg : Config 4) :
    (machine value).step (config cfg) = config (value.step cfg) := by
  cases cfg with
  | mk state head valueTape =>
      cases state with
      | none => rfl
      | some state =>
          simp [machine, action, config, Machine.step]

@[simp]
theorem stepGo (cfg : Config 4) (value : GoAction) :
    stepGo (config cfg) (goAction value) = config (stepGo cfg value) := by
  cases cfg
  cases value
  simp [BB4.stepGo, stepAction, goAction, config,
    GoAction.toAction]

@[simp]
theorem runFrom (value : Machine 4) (cfg : Config 4) : forall steps,
    (machine value).runFrom (config cfg) steps = config (value.runFrom cfg steps)
  | 0 => rfl
  | steps + 1 => by
      simp [Machine.runFrom, runFrom value cfg steps]

@[simp]
theorem run (value : Machine 4) : forall steps,
    (machine value).run steps = config (value.run steps)
  | 0 => by simp [Machine.run]
  | steps + 1 => by
      simp [Machine.run, run value steps]

/-- Reflection preserves halting and the exact busy-beaver score. -/
theorem haltsWithScore_iff (value : Machine 4) (score : Nat) :
    (machine value).HaltsWithScore score ↔ value.HaltsWithScore score := by
  constructor
  · rintro ⟨steps, hState, hScore⟩
    rw [run value steps] at hState hScore
    exact ⟨steps, by simpa [config] using hState,
      by simpa [config, tape] using hScore⟩
  · rintro ⟨steps, hState, hScore⟩
    refine ⟨steps, ?_, ?_⟩
    · rw [run value steps]
      simpa [config] using hState
    · rw [run value steps]
      simpa [config, tape] using hScore

end Reflect
end TNF
end BB4
end BusyBeaver
end SetTheory
