/-
  BusyBeaverBB4/TNFProbe.lean

  Bounded structural instrumentation for `TNF.checkRoot`.  This is not used by
  any proof; it exists only to compare the normalized and raw DFS frontiers.
-/

import SetTheory.BusyBeaverBB4.TNFRoot

namespace SetTheory
namespace BusyBeaver
namespace BB4
namespace TNFProbe

structure Work where
  fuel : Nat
  used : Nat
  table : PTable
  cfg : Config 4
  atRoot : Bool := false

structure State where
  pending : List Work
  nodes : Nat := 0
  assignedSteps : Nat := 0
  freshSlots : Nat := 0
  safeHaltBranches : Nat := 0
  unsafeHalts : Nat := 0
  haltedSafe : Nat := 0
  haltedUnsafe : Nat := 0
  leaves : Nat := 0

structure Summary where
  pending : Nat
  nodes : Nat
  assignedSteps : Nat
  freshSlots : Nat
  safeHaltBranches : Nat
  unsafeHalts : Nat
  haltedSafe : Nat
  haltedUnsafe : Nat
  leaves : Nat
  deriving Repr

def step (state : State) : State :=
  match state.pending with
  | [] => state
  | work :: rest =>
      let state := { state with pending := rest, nodes := state.nodes + 1 }
      match work.cfg.state with
      | none =>
          if work.cfg.tape.length <= 13 then
            { state with haltedSafe := state.haltedSafe + 1 }
          else
            { state with haltedUnsafe := state.haltedUnsafe + 1 }
      | some current =>
          match work.fuel with
          | 0 => { state with leaves := state.leaves + 1 }
          | fuel + 1 =>
              let bit := Tape.read work.cfg.tape work.cfg.head
              match work.table current bit with
              | some action =>
                  { state with
                    pending :=
                      { fuel, used := work.used, table := work.table,
                        cfg := stepGo work.cfg action } :: state.pending
                    assignedSteps := state.assignedSteps + 1 }
              | none =>
                  if haltWritesSafe work.cfg then
                    let actions :=
                      if work.atRoot then TNF.rootActions
                      else TNF.canonicalActions work.used
                    let children := actions.map fun action =>
                      { fuel
                        used := TNF.grow work.used action
                        table := work.table.set current bit action
                        cfg := stepGo work.cfg action
                        atRoot := false }
                    { state with
                      pending := children ++ state.pending
                      freshSlots := state.freshSlots + 1
                      safeHaltBranches := state.safeHaltBranches + 1 }
                  else
                    { state with
                      freshSlots := state.freshSlots + 1
                      unsafeHalts := state.unsafeHalts + 1 }

def run : Nat -> State -> State
  | 0, state => state
  | budget + 1, state =>
      if state.pending.isEmpty then state else run budget (step state)

def initialState : State :=
  { pending :=
      [{ fuel := 107
         used := 1
         table := PTable.empty
         cfg := initial 4
         atRoot := true }] }

def summarize (state : State) : Summary :=
  { pending := state.pending.length
    nodes := state.nodes
    assignedSteps := state.assignedSteps
    freshSlots := state.freshSlots
    safeHaltBranches := state.safeHaltBranches
    unsafeHalts := state.unsafeHalts
    haltedSafe := state.haltedSafe
    haltedUnsafe := state.haltedUnsafe
    leaves := state.leaves }

def probe (budget : Nat) : Summary :=
  summarize (run budget initialState)

end TNFProbe
end BB4
end BusyBeaver
end SetTheory
