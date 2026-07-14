/-
  BusyBeaverBB3/Partial.lean

  Partial-machine semantics used by the three-state nonhalting certificates.

  A partial machine has no halting action: an undefined transition means that
  execution stops.  Its tape is a zipper centered at the head, with the two
  infinite sides indexed nearest cell first.  This presentation makes local
  window invariants independent of integer-coordinate arithmetic.  The final
  section proves, once and for all, that it faithfully simulates the finite-
  support Rado machines from `BusyBeaver.lean`.
-/

import BusyBeaver.BB3.Search

set_option maxRecDepth 10000

namespace SetTheory
namespace BusyBeaver
namespace BB3

universe u v u' v'

/-! ## Generic partial machines on zipper tapes -/

/-- A continuing transition of a generic partial Turing machine. -/
structure PAction (State : Type u) (Symbol : Type v) where
  write : Symbol
  move : Move
  next : State
  deriving DecidableEq, Repr

namespace PAction

/-- Map the state and symbol components of a continuing action. -/
def map {State : Type u} {Symbol : Type v}
    {State' : Type u'} {Symbol' : Type v'}
    (fState : State -> State') (fSymbol : Symbol -> Symbol')
    (action : PAction State Symbol) : PAction State' Symbol' where
  write := fSymbol action.write
  move := action.move
  next := fState action.next

end PAction

/-- A partial machine.  `none` denotes an undefined (hence stopping)
transition; every `some` action continues in an operational state. -/
abbrev PTM (State : Type u) (Symbol : Type v) :=
  State -> Symbol -> Option (PAction State Symbol)

/-- A relative-head tape configuration.  Both sides are nearest-cell first. -/
structure PConfig (State : Type u) (Symbol : Type v) where
  state : State
  left : Nat -> Symbol
  center : Symbol
  right : Nat -> Symbol

namespace PConfig

@[ext]
theorem ext {State : Type u} {Symbol : Type v}
    {first second : PConfig State Symbol}
    (hState : first.state = second.state)
    (hLeft : forall n, first.left n = second.left n)
    (hCenter : first.center = second.center)
    (hRight : forall n, first.right n = second.right n) :
    first = second := by
  cases first with
  | mk firstState firstLeft firstCenter firstRight =>
      cases second with
      | mk secondState secondLeft secondCenter secondRight =>
          simp only at hState hLeft hCenter hRight
          subst secondState
          subst secondCenter
          have hLeftEq : firstLeft = secondLeft := funext hLeft
          have hRightEq : firstRight = secondRight := funext hRight
          subst secondLeft
          subst secondRight
          rfl

/-- The blank zipper in a chosen start state. -/
def blank {State : Type u} {Symbol : Type v}
    (start : State) (blankSymbol : Symbol) : PConfig State Symbol where
  state := start
  left := fun _ => blankSymbol
  center := blankSymbol
  right := fun _ => blankSymbol

/-- Map a zipper configuration pointwise. -/
def map {State : Type u} {Symbol : Type v}
    {State' : Type u'} {Symbol' : Type v'}
    (fState : State -> State') (fSymbol : Symbol -> Symbol')
    (cfg : PConfig State Symbol) : PConfig State' Symbol' where
  state := fState cfg.state
  left := fun n => fSymbol (cfg.left n)
  center := fSymbol cfg.center
  right := fun n => fSymbol (cfg.right n)

@[simp]
theorem map_blank {State : Type u} {Symbol : Type v}
    {State' : Type u'} {Symbol' : Type v'}
    (fState : State -> State') (fSymbol : Symbol -> Symbol')
    (start : State) (blankSymbol : Symbol) :
    (blank start blankSymbol).map fState fSymbol =
      blank (fState start) (fSymbol blankSymbol) := by
  rfl

end PConfig

namespace PTM

/-- Execute a known continuing action on a zipper. -/
def stepAction {State : Type u} {Symbol : Type v}
    (cfg : PConfig State Symbol) (action : PAction State Symbol) :
    PConfig State Symbol :=
  match action.move with
  | Move.right =>
      { state := action.next
        left := fun
          | 0 => action.write
          | n + 1 => cfg.left n
        center := cfg.right 0
        right := fun n => cfg.right (n + 1) }
  | Move.left =>
      { state := action.next
        left := fun n => cfg.left (n + 1)
        center := cfg.left 0
        right := fun
          | 0 => action.write
          | n + 1 => cfg.right n }

/-- Execute one partial-machine transition, failing at an undefined slot. -/
def step? {State : Type u} {Symbol : Type v}
    (M : PTM State Symbol) (cfg : PConfig State Symbol) :
    Option (PConfig State Symbol) :=
  (M cfg.state cfg.center).map (stepAction cfg)

/-- Execute exactly `steps` partial-machine transitions. -/
def run? {State : Type u} {Symbol : Type v}
    (M : PTM State Symbol) (cfg : PConfig State Symbol) :
    Nat -> Option (PConfig State Symbol)
  | 0 => some cfg
  | steps + 1 => (run? M cfg steps).bind (step? M)

@[simp]
theorem run?_zero {State : Type u} {Symbol : Type v}
    (M : PTM State Symbol) (cfg : PConfig State Symbol) :
    run? M cfg 0 = some cfg :=
  rfl

@[simp]
theorem run?_succ {State : Type u} {Symbol : Type v}
    (M : PTM State Symbol) (cfg : PConfig State Symbol) (steps : Nat) :
    run? M cfg (steps + 1) = (run? M cfg steps).bind (step? M) :=
  rfl

/-- A partial machine runs forever from a specified zipper configuration. -/
def NonhaltsFrom {State : Type u} {Symbol : Type v}
    (M : PTM State Symbol) (cfg : PConfig State Symbol) : Prop :=
  forall steps, exists result, run? M cfg steps = some result

/-- A partial machine runs forever from a blank zipper. -/
def Nonhalts {State : Type u} {Symbol : Type v}
    (M : PTM State Symbol) (start : State) (blankSymbol : Symbol) : Prop :=
  M.NonhaltsFrom (PConfig.blank start blankSymbol)

theorem NonhaltsFrom.step_defined {State : Type u} {Symbol : Type v}
    {M : PTM State Symbol} {cfg : PConfig State Symbol}
    (h : M.NonhaltsFrom cfg) : exists next, M.step? cfg = some next := by
  rcases h 1 with ⟨next, hnext⟩
  exact ⟨next, by simpa [run?] using hnext⟩

/-! ## Monotonicity under extensions -/

/-- `larger.Extends smaller` means that every transition defined by `smaller`
is defined identically by `larger`. -/
def Extends {State : Type u} {Symbol : Type v}
    (larger smaller : PTM State Symbol) : Prop :=
  forall state symbol action,
    smaller state symbol = some action -> larger state symbol = some action

theorem Extends.refl {State : Type u} {Symbol : Type v}
    (M : PTM State Symbol) : M.Extends M := by
  intro state symbol action h
  exact h

theorem Extends.trans {State : Type u} {Symbol : Type v}
    {first second third : PTM State Symbol}
    (hSecond : second.Extends first) (hThird : third.Extends second) :
    third.Extends first := by
  intro state symbol action h
  exact hThird state symbol action (hSecond state symbol action h)

theorem Extends.step?_eq {State : Type u} {Symbol : Type v}
    {smaller larger : PTM State Symbol} (hExt : larger.Extends smaller)
    {cfg result : PConfig State Symbol}
    (hStep : smaller.step? cfg = some result) :
    larger.step? cfg = some result := by
  unfold step? at hStep ⊢
  cases hLookup : smaller cfg.state cfg.center with
  | none => simp [hLookup] at hStep
  | some action =>
      have hLarger := hExt cfg.state cfg.center action hLookup
      simpa [hLookup, hLarger] using hStep

theorem Extends.run?_eq {State : Type u} {Symbol : Type v}
    {smaller larger : PTM State Symbol} (hExt : larger.Extends smaller) :
    forall {cfg : PConfig State Symbol} {steps : Nat} {result : PConfig State Symbol},
      smaller.run? cfg steps = some result ->
      larger.run? cfg steps = some result := by
  intro cfg steps
  induction steps with
  | zero =>
      intro result hRun
      simpa [run?] using hRun
  | succ steps ih =>
      intro result hRun
      simp only [run?_succ] at hRun ⊢
      cases hMiddle : smaller.run? cfg steps with
      | none => simp [hMiddle] at hRun
      | some middle =>
          have hMiddle' := ih hMiddle
          have hStep : smaller.step? middle = some result := by
            simpa [hMiddle] using hRun
          simpa [hMiddle'] using hExt.step?_eq hStep

theorem Extends.nonhaltsFrom {State : Type u} {Symbol : Type v}
    {smaller larger : PTM State Symbol} (hExt : larger.Extends smaller)
    {cfg : PConfig State Symbol} (h : smaller.NonhaltsFrom cfg) :
    larger.NonhaltsFrom cfg := by
  intro steps
  rcases h steps with ⟨result, hRun⟩
  exact ⟨result, hExt.run?_eq hRun⟩

theorem Extends.nonhalts {State : Type u} {Symbol : Type v}
    {smaller larger : PTM State Symbol} (hExt : larger.Extends smaller)
    {start : State} {blankSymbol : Symbol}
    (h : smaller.Nonhalts start blankSymbol) :
    larger.Nonhalts start blankSymbol :=
  hExt.nonhaltsFrom h

/-! ## Simulation by state/symbol projection -/

/-- Every defined source transition projects to the corresponding target
transition.  The target may additionally define transitions absent upstream. -/
def Projects {SourceState : Type u} {SourceSymbol : Type v}
    {TargetState : Type u'} {TargetSymbol : Type v'}
    (source : PTM SourceState SourceSymbol)
    (target : PTM TargetState TargetSymbol)
    (fState : SourceState -> TargetState)
    (fSymbol : SourceSymbol -> TargetSymbol) : Prop :=
  forall state symbol action,
    source state symbol = some action ->
    target (fState state) (fSymbol symbol) =
      some (action.map fState fSymbol)

theorem stepAction_map {SourceState : Type u} {SourceSymbol : Type v}
    {TargetState : Type u'} {TargetSymbol : Type v'}
    (fState : SourceState -> TargetState)
    (fSymbol : SourceSymbol -> TargetSymbol)
    (cfg : PConfig SourceState SourceSymbol)
    (action : PAction SourceState SourceSymbol) :
    (stepAction cfg action).map fState fSymbol =
      stepAction (cfg.map fState fSymbol) (action.map fState fSymbol) := by
  rcases action with ⟨write, move, next⟩
  cases move
  · apply PConfig.ext
    · rfl
    · intro n
      rfl
    · rfl
    · intro n
      cases n <;> rfl
  · apply PConfig.ext
    · rfl
    · intro n
      cases n <;> rfl
    · rfl
    · intro n
      rfl

theorem Projects.step?_map {SourceState : Type u} {SourceSymbol : Type v}
    {TargetState : Type u'} {TargetSymbol : Type v'}
    {source : PTM SourceState SourceSymbol}
    {target : PTM TargetState TargetSymbol}
    {fState : SourceState -> TargetState}
    {fSymbol : SourceSymbol -> TargetSymbol}
    (hProj : Projects source target fState fSymbol)
    {cfg result : PConfig SourceState SourceSymbol}
    (hStep : source.step? cfg = some result) :
    target.step? (cfg.map fState fSymbol) =
      some (result.map fState fSymbol) := by
  unfold step? at hStep ⊢
  cases hLookup : source cfg.state cfg.center with
  | none => simp [hLookup] at hStep
  | some action =>
      have hTarget := hProj cfg.state cfg.center action hLookup
      have hResult : stepAction cfg action = result := by
        simpa [hLookup] using hStep
      subst result
      change
        (target (fState cfg.state) (fSymbol cfg.center)).map
            (stepAction (cfg.map fState fSymbol)) =
          some ((stepAction cfg action).map fState fSymbol)
      rw [hTarget]
      simp only [Option.map_some]
      exact congrArg some (stepAction_map fState fSymbol cfg action).symm

theorem Projects.run?_map {SourceState : Type u} {SourceSymbol : Type v}
    {TargetState : Type u'} {TargetSymbol : Type v'}
    {source : PTM SourceState SourceSymbol}
    {target : PTM TargetState TargetSymbol}
    {fState : SourceState -> TargetState}
    {fSymbol : SourceSymbol -> TargetSymbol}
    (hProj : Projects source target fState fSymbol) :
    forall {cfg : PConfig SourceState SourceSymbol} {steps : Nat}
      {result : PConfig SourceState SourceSymbol},
      source.run? cfg steps = some result ->
      target.run? (cfg.map fState fSymbol) steps =
        some (result.map fState fSymbol) := by
  intro cfg steps
  induction steps with
  | zero =>
      intro result hRun
      have hResult : cfg = result := by simpa [run?] using hRun
      subst result
      rfl
  | succ steps ih =>
      intro result hRun
      simp only [run?_succ] at hRun ⊢
      cases hMiddle : source.run? cfg steps with
      | none => simp [hMiddle] at hRun
      | some middle =>
          have hMiddle' := ih hMiddle
          have hStep : source.step? middle = some result := by
            simpa [hMiddle] using hRun
          simpa [hMiddle'] using hProj.step?_map hStep

theorem Projects.nonhaltsFrom {SourceState : Type u} {SourceSymbol : Type v}
    {TargetState : Type u'} {TargetSymbol : Type v'}
    {source : PTM SourceState SourceSymbol}
    {target : PTM TargetState TargetSymbol}
    {fState : SourceState -> TargetState}
    {fSymbol : SourceSymbol -> TargetSymbol}
    (hProj : Projects source target fState fSymbol)
    {cfg : PConfig SourceState SourceSymbol}
    (h : source.NonhaltsFrom cfg) :
    target.NonhaltsFrom (cfg.map fState fSymbol) := by
  intro steps
  rcases h steps with ⟨result, hRun⟩
  exact ⟨result.map fState fSymbol, hProj.run?_map hRun⟩

theorem Projects.nonhalts {SourceState : Type u} {SourceSymbol : Type v}
    {TargetState : Type u'} {TargetSymbol : Type v'}
    {source : PTM SourceState SourceSymbol}
    {target : PTM TargetState TargetSymbol}
    {fState : SourceState -> TargetState}
    {fSymbol : SourceSymbol -> TargetSymbol}
    (hProj : Projects source target fState fSymbol)
    {start : SourceState} {blankSymbol : SourceSymbol}
    (h : source.Nonhalts start blankSymbol) :
    target.Nonhalts (fState start) (fSymbol blankSymbol) := by
  simpa [Nonhalts] using hProj.nonhaltsFrom h

/-! ## Total Rado machines viewed as partial machines -/

/-- Forget the halt action of a total Rado machine. -/
def ofMachine {states : Nat} (M : Machine states) : PTM (Fin states) Bool :=
  fun state symbol =>
    let action := M.transition state symbol
    action.next.map fun next =>
      { write := action.write, move := action.move, next := next }

end PTM

/-! ## Integer-tape / zipper bridge -/

namespace LocalConfig

/-- Absolute position of the `n`th cell to the left of the head. -/
def leftPos {states : Nat} (cfg : Config states) (n : Nat) : Int :=
  cfg.head - (n + 1)

/-- Absolute position of the `n`th cell to the right of the head. -/
def rightPos {states : Nat} (cfg : Config states) (n : Nat) : Int :=
  cfg.head + (n + 1)

/-- Convert an active finite-support configuration to a relative zipper.
Halted configurations have no partial-machine configuration. -/
def toPConfig? {states : Nat} (cfg : Config states) :
    Option (PConfig (Fin states) Bool) :=
  cfg.state.map fun state =>
    { state := state
      left := fun n => Tape.read cfg.tape (leftPos cfg n)
      center := Tape.read cfg.tape cfg.head
      right := fun n => Tape.read cfg.tape (rightPos cfg n) }

end LocalConfig

namespace PTM

/-- Converting a total-machine configuration to a zipper commutes with one
step.  This is the only proof that depends on the finite-support integer tape. -/
theorem ofMachine_step_toPConfig? {states : Nat} (M : Machine states)
    (cfg : Config states) :
    (LocalConfig.toPConfig? cfg).bind (ofMachine M).step? =
      LocalConfig.toPConfig? (M.step cfg) := by
  rcases cfg with ⟨state, head, tape⟩
  cases state with
  | none => rfl
  | some state =>
      cases hAction : M.transition state (Tape.read tape head) with
      | mk write move next =>
          cases next with
          | none =>
              simp [LocalConfig.toPConfig?, Machine.step, step?, ofMachine,
                hAction]
          | some next =>
              cases move with
              | left =>
                  simp only [LocalConfig.toPConfig?, Machine.step, step?, ofMachine,
                    hAction, Option.map_some, Option.bind_some]
                  apply congrArg some
                  apply PConfig.ext
                  · rfl
                  · intro n
                    simp only [stepAction, LocalConfig.leftPos, Move.apply]
                    rw [Tape.read_write_of_ne]
                    · congr 1 <;> omega
                    · omega
                  · simp only [stepAction, LocalConfig.leftPos, Move.apply]
                    rw [Tape.read_write_of_ne]
                    · congr 1 <;> omega
                    · omega
                  · intro n
                    cases n with
                    | zero =>
                        simp [stepAction, LocalConfig.rightPos, Move.apply]
                    | succ n =>
                        simp only [stepAction, LocalConfig.rightPos, Move.apply]
                        rw [Tape.read_write_of_ne]
                        · congr 1 <;> omega
                        · omega
              | right =>
                  simp only [LocalConfig.toPConfig?, Machine.step, step?, ofMachine,
                    hAction, Option.map_some, Option.bind_some]
                  apply congrArg some
                  apply PConfig.ext
                  · rfl
                  · intro n
                    cases n with
                    | zero =>
                        simp [stepAction, LocalConfig.leftPos, Move.apply]
                    | succ n =>
                        simp only [stepAction, LocalConfig.leftPos, Move.apply]
                        rw [Tape.read_write_of_ne]
                        · congr 1 <;> omega
                        · omega
                  · simp only [stepAction, LocalConfig.rightPos, Move.apply]
                    rw [Tape.read_write_of_ne]
                    · congr 1 <;> omega
                    · omega
                  · intro n
                    simp only [stepAction, LocalConfig.rightPos, Move.apply]
                    rw [Tape.read_write_of_ne]
                    · congr 1 <;> omega
                    · omega

/-- The zipper execution of `ofMachine M` is exactly the conversion of local
Rado execution, as long as the chosen initial local configuration is active. -/
theorem ofMachine_runFrom_toPConfig? {states : Nat} (M : Machine states)
    {cfg : Config states} {pcfg : PConfig (Fin states) Bool}
    (hCfg : LocalConfig.toPConfig? cfg = some pcfg) :
    forall steps,
      (ofMachine M).run? pcfg steps =
        LocalConfig.toPConfig? (M.runFrom cfg steps) := by
  intro steps
  induction steps with
  | zero => simpa [run?, Machine.runFrom] using hCfg.symm
  | succ steps ih =>
      rw [run?_succ, ih, ofMachine_step_toPConfig?]
      rfl

theorem initial_three_toPConfig? :
    LocalConfig.toPConfig? (initial 3) =
      some (PConfig.blank (0 : Fin 3) false) := by
  rfl

/-- Nonhalting of the partial view of a concrete three-state machine implies
nonhalting of that machine in the repository's local Rado semantics. -/
theorem ofMachine_nonhalts_run_three {M : Machine 3}
    (h : (ofMachine M).Nonhalts (0 : Fin 3) false) :
    forall steps, (M.run steps).state ≠ none := by
  intro steps hHalted
  rcases h steps with ⟨result, hRun⟩
  have hBridge := ofMachine_runFrom_toPConfig? M initial_three_toPConfig? steps
  have hRunFrom : M.runFrom (initial 3) steps = M.run steps := by
    simpa [Machine.run] using (Machine.run_add_eq_runFrom M 0 steps).symm
  rw [hRunFrom] at hBridge
  simp [LocalConfig.toPConfig?, hHalted] at hBridge
  rw [hBridge] at hRun
  contradiction

end PTM

/-! ## Three-state partial tables -/

namespace PTable

/-- Interpret an assigned lazy-search table as a generic partial machine. -/
def toPTM (table : PTable) : PTM (Fin 3) Bool :=
  fun state symbol =>
    (table state symbol).map fun action =>
      { write := action.write, move := action.move, next := action.next }

@[simp]
theorem toPTM_apply (table : PTable) (state : Fin 3) (symbol : Bool) :
    table.toPTM state symbol =
      (table state symbol).map fun action =>
        ({ write := action.write, move := action.move, next := action.next } :
          PAction (Fin 3) Bool) :=
  rfl

/-- The partial view of an agreeing total machine extends the assigned table. -/
theorem ofMachine_extends {table : PTable} {M : Machine 3}
    (hAgree : table.Agrees M) :
    (PTM.ofMachine M).Extends table.toPTM := by
  intro state symbol action hAction
  cases hLookup : table state symbol with
  | none => simp [toPTM, hLookup] at hAction
  | some goAction =>
      have hEq :
          ({ write := goAction.write, move := goAction.move, next := goAction.next } :
            PAction (Fin 3) Bool) = action := by
        simpa [toPTM, hLookup] using hAction
      subst action
      have hTransition := hAgree state symbol goAction hLookup
      unfold PTM.ofMachine
      rw [← hTransition]
      rfl

/-- A nonhalting partial table rules out halting for every agreeing concrete
three-state Rado machine. -/
theorem nonhalts_machine_of_agrees {table : PTable} {M : Machine 3}
    (hTable : table.toPTM.Nonhalts (0 : Fin 3) false)
    (hAgree : table.Agrees M) :
    forall steps, (M.run steps).state ≠ none := by
  apply PTM.ofMachine_nonhalts_run_three
  exact (ofMachine_extends hAgree).nonhalts hTable

end PTable

end BB3
end BusyBeaver
end SetTheory
