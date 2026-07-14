/-
  BusyBeaver/BB4/Probe.lean

  Bounded, non-proof-facing instrumentation for the raw lazy search.  It uses
  an explicit DFS worklist, so every evaluation has a caller-selected node
  budget and cannot accidentally launch an unbounded full enumeration.
-/

import BusyBeaver.BB4.Leaf

namespace SetTheory
namespace BusyBeaver
namespace BB4
namespace Probe

structure Work where
  fuel : Nat
  table : PTable
  cfg : Config 4

structure Failure where
  table : List (Option GoAction)
  cfg : Config 4
  deriving Repr

structure State where
  pending : List Work
  nodes : Nat := 0
  assignedSteps : Nat := 0
  freshSlots : Nat := 0
  safeHaltBranches : Nat := 0
  unsafeHalts : Nat := 0
  haltedSafe : Nat := 0
  haltedUnsafe : Nat := 0
  completeLeaves : Nat := 0
  ngramLeaves : Nat := 0
  sporadic1Leaves : Nat := 0
  sporadic2Leaves : Nat := 0
  failedLeaves : Nat := 0
  firstFailure : Option Failure := none

structure Summary where
  pending : Nat
  nodes : Nat
  assignedSteps : Nat
  freshSlots : Nat
  safeHaltBranches : Nat
  unsafeHalts : Nat
  haltedSafe : Nat
  haltedUnsafe : Nat
  completeLeaves : Nat
  ngramLeaves : Nat
  sporadic1Leaves : Nat
  sporadic2Leaves : Nat
  failedLeaves : Nat
  firstFailure : Option Failure
  deriving Repr

def snapshot (table : PTable) : List (Option GoAction) :=
  [ table 0 false, table 0 true,
    table 1 false, table 1 true,
    table 2 false, table 2 true,
    table 3 false, table 3 true ]

/-- Result tags: 0 complete, 1 n-gram, 2/3 sporadic, 4 failure. -/
def fullClass (table : PTable) : Nat :=
  if tableComplete table then 0
  else if NGram.runPasses table NGram.passes then 1
  else if tableMatches table Sporadic.machine1Fin then 2
  else if tableMatches table Sporadic.machine2Fin then 3
  else 4

/-- Cheap classification omitting all n-gram construction. -/
def cheapClass (table : PTable) : Nat :=
  if tableComplete table then 0
  else if tableMatches table Sporadic.machine1Fin then 2
  else if tableMatches table Sporadic.machine2Fin then 3
  else 4

private def recordClass (kind : Nat) (work : Work) (state : State) : State :=
  match kind with
  | 0 => { state with completeLeaves := state.completeLeaves + 1 }
  | 1 => { state with ngramLeaves := state.ngramLeaves + 1 }
  | 2 => { state with sporadic1Leaves := state.sporadic1Leaves + 1 }
  | 3 => { state with sporadic2Leaves := state.sporadic2Leaves + 1 }
  | _ =>
      { state with
        failedLeaves := state.failedLeaves + 1
        firstFailure := state.firstFailure.orElse
          (fun _ => some { table := snapshot work.table, cfg := work.cfg }) }

def step (classify : PTable -> Nat) (state : State) : State :=
  match state.pending with
  | [] => state
  | work :: rest =>
      let state := { state with pending := rest, nodes := state.nodes + 1 }
      match work.cfg.state with
      | none =>
          if work.cfg.tape.length ≤ 13 then
            { state with haltedSafe := state.haltedSafe + 1 }
          else
            { state with haltedUnsafe := state.haltedUnsafe + 1 }
      | some q =>
          match work.fuel with
          | 0 => recordClass (classify work.table) work state
          | fuel + 1 =>
              let bit := Tape.read work.cfg.tape work.cfg.head
              match work.table q bit with
              | some action =>
                  { state with
                    pending :=
                      { fuel, table := work.table,
                        cfg := stepGo work.cfg action } :: state.pending
                    assignedSteps := state.assignedSteps + 1 }
              | none =>
                  if haltWritesSafe work.cfg then
                    let children := actionList.map fun action =>
                      { fuel,
                        table := work.table.set q bit action,
                        cfg := stepGo work.cfg action }
                    { state with
                      pending := children ++ state.pending
                      freshSlots := state.freshSlots + 1
                      safeHaltBranches := state.safeHaltBranches + 1 }
                  else
                    { state with
                      freshSlots := state.freshSlots + 1
                      unsafeHalts := state.unsafeHalts + 1 }

def run (classify : PTable -> Nat) : Nat -> State -> State
  | 0, state => state
  | budget + 1, state =>
      if state.pending.isEmpty then state
      else run classify budget (step classify state)

def initialState : State :=
  { pending := [{ fuel := 107, table := PTable.empty, cfg := initial 4 }] }

def summarize (state : State) : Summary :=
  { pending := state.pending.length
    nodes := state.nodes
    assignedSteps := state.assignedSteps
    freshSlots := state.freshSlots
    safeHaltBranches := state.safeHaltBranches
    unsafeHalts := state.unsafeHalts
    haltedSafe := state.haltedSafe
    haltedUnsafe := state.haltedUnsafe
    completeLeaves := state.completeLeaves
    ngramLeaves := state.ngramLeaves
    sporadic1Leaves := state.sporadic1Leaves
    sporadic2Leaves := state.sporadic2Leaves
    failedLeaves := state.failedLeaves
    firstFailure := state.firstFailure }

def cheap (budget : Nat) : Summary :=
  summarize (run cheapClass budget initialState)

def full (budget : Nat) : Summary :=
  summarize (run fullClass budget initialState)

end Probe
end BB4
end BusyBeaver
end SetTheory
