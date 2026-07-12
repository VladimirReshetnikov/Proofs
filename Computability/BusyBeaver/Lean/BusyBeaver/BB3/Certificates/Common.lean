/-
  BusyBeaverBB3/Certificates/Common.lean

  Shared definitions for the twelve kernel-computed first-transition shards of
  the exhaustive three-state score search.
-/

import BusyBeaver.BB3.NGramBuilder

namespace SetTheory
namespace BusyBeaver
namespace BB3
namespace Certificates

private abbrev A : Fin 3 := 0
private abbrev B : Fin 3 := 1
private abbrev C : Fin 3 := 2

def a00 : GoAction := { write := false, move := .left, next := A }
def a01 : GoAction := { write := false, move := .left, next := B }
def a02 : GoAction := { write := false, move := .left, next := C }
def a03 : GoAction := { write := false, move := .right, next := A }
def a04 : GoAction := { write := false, move := .right, next := B }
def a05 : GoAction := { write := false, move := .right, next := C }
def a06 : GoAction := { write := true, move := .left, next := A }
def a07 : GoAction := { write := true, move := .left, next := B }
def a08 : GoAction := { write := true, move := .left, next := C }
def a09 : GoAction := { write := true, move := .right, next := A }
def a10 : GoAction := { write := true, move := .right, next := B }
def a11 : GoAction := { write := true, move := .right, next := C }

theorem actionList_eq :
    actionList = [a00, a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11] :=
  rfl

/-- The search below the root continuing action.  The root itself consumes one
of the global search's 21 units of simulation fuel. -/
def firstBranch (action : GoAction) : Bool :=
  checkFrom NGram.leaf 20
    (PTable.empty.set (0 : Fin 3) false action)
    (stepGo (initial 3) action)

/-- The search below two freshly assigned transitions.  This is used to split
the first-action branches whose target state is `B` or `C`; their next blank
read reaches a genuinely fresh slot. -/
def secondBranch (first second : GoAction) : Bool :=
  checkFrom NGram.leaf 19
    ((PTable.empty.set (0 : Fin 3) false first).set first.next false second)
    (stepGo (stepGo (initial 3) first) second)

/-- A third freshly assigned blank-read transition, immediately after the
first two actions. -/
def thirdFreshBranch (first second third : GoAction) : Bool :=
  checkFrom NGram.leaf 18
    (((PTable.empty.set (0 : Fin 3) false first).set first.next false second).set
      second.next false third)
    (stepGo (stepGo (stepGo (initial 3) first) second) third)

/-- A third freshly assigned marked-read transition, immediately after the
first two actions.  This occurs when the first action writes a mark at the
origin and the second action returns to it. -/
def thirdMarkedBranch (first second third : GoAction) : Bool :=
  checkFrom NGram.leaf 18
    (((PTable.empty.set (0 : Fin 3) false first).set first.next false second).set
      second.next true third)
    (stepGo (stepGo (stepGo (initial 3) first) second) third)

/-- The special `A0, B0, A0, B1` rebound prefix: after the second action the
machine executes the already assigned first action once more, then reaches a
fresh marked-symbol transition in the first action's target state. -/
def reboundBranch (first second third : GoAction) : Bool :=
  checkFrom NGram.leaf 17
    (((PTable.empty.set (0 : Fin 3) false first).set first.next false second).set
      first.next true third)
    (stepGo (stepGo (stepGo (stepGo (initial 3) first) second) first) third)

end Certificates
end BB3
end BusyBeaver
end SetTheory
