/-
  BusyBeaverBB4/Certificates/Common.lean

  Shared action names and the first two explicit TNF search levels for the
  kernel-sharded four-state coverage certificate.
-/

import BusyBeaver.BB4.Leaf
import BusyBeaver.BB4.TNFRoot

namespace SetTheory
namespace BusyBeaver
namespace BB4
namespace Certificates

private abbrev A : Fin 4 := 0
private abbrev B : Fin 4 := 1
private abbrev C : Fin 4 := 2
private abbrev D : Fin 4 := 3

def a00 : GoAction := { write := false, move := .left, next := A }
def a01 : GoAction := { write := false, move := .left, next := B }
def a02 : GoAction := { write := false, move := .left, next := C }
def a03 : GoAction := { write := false, move := .left, next := D }
def a04 : GoAction := { write := false, move := .right, next := A }
def a05 : GoAction := { write := false, move := .right, next := B }
def a06 : GoAction := { write := false, move := .right, next := C }
def a07 : GoAction := { write := false, move := .right, next := D }
def a08 : GoAction := { write := true, move := .left, next := A }
def a09 : GoAction := { write := true, move := .left, next := B }
def a10 : GoAction := { write := true, move := .left, next := C }
def a11 : GoAction := { write := true, move := .left, next := D }
def a12 : GoAction := { write := true, move := .right, next := A }
def a13 : GoAction := { write := true, move := .right, next := B }
def a14 : GoAction := { write := true, move := .right, next := C }
def a15 : GoAction := { write := true, move := .right, next := D }

theorem actionList_eq :
    actionList =
      [a00, a01, a02, a03, a04, a05, a06, a07,
       a08, a09, a10, a11, a12, a13, a14, a15] :=
  rfl

theorem canonicalActions_one_eq :
    TNF.canonicalActions 1 = [a00, a01, a04, a05, a08, a09, a12, a13] := by
  decide

theorem canonicalActions_two_eq :
    TNF.canonicalActions 2 =
      [a00, a01, a02, a04, a05, a06, a08, a09, a10, a12, a13, a14] := by
  decide

theorem canonicalActions_three_eq :
    TNF.canonicalActions 3 =
      [a00, a01, a02, a03, a04, a05, a06, a07,
       a08, a09, a10, a11, a12, a13, a14, a15] := by
  decide

theorem canonicalActions_four_eq :
    TNF.canonicalActions 4 =
      [a00, a01, a02, a03, a04, a05, a06, a07,
       a08, a09, a10, a11, a12, a13, a14, a15] := by
  decide

theorem rootActions_eq : TNF.rootActions = [a04, a05, a12, a13] := by
  decide

/-- The TNF subtree below one continuing root action. -/
def rootBranch (action : GoAction) : Bool :=
  TNF.checkFrom leaf 106 (TNF.grow 1 action)
    (PTable.empty.set A false action) (stepGo (initial 4) action)

/-- The subtree below the fresh blank-read slot reached immediately after a
root action targeting `B`. -/
def secondBranch (first second : GoAction) : Bool :=
  TNF.checkFrom leaf 105 (TNF.grow (TNF.grow 1 first) second)
    ((PTable.empty.set A false first).set first.next false second)
    (stepGo (stepGo (initial 4) first) second)

end Certificates
end BB4
end BusyBeaver
end SetTheory
