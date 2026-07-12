/-
  BusyBeaverBB3/NGramBuilder.lean

  Executable builders for Boolean and write-history n-gram closed-position-set
  certificates.  This module deliberately contains no semantic soundness
  theorem: it computes a candidate and then asks the proof-facing
  `NGramCPS.Valid` checker to verify every finite closure obligation.
-/

import BusyBeaver.BB3.Complete
import BusyBeaver.BB3.NGramCPS

set_option maxRecDepth 10000

namespace SetTheory
namespace BusyBeaver
namespace BB3
namespace NGram

/-! ## Proof-facing certificate aliases -/

abbrev MidWord (symbol : Type) := NGramCPS.MidWord (Fin 3) symbol
abbrev AbstractState (symbol : Type) := NGramCPS.Cert (Fin 3) symbol

private def insertNew [DecidableEq α]
    (value : α) (values : List α) : List α × Bool :=
  if value ∈ values then (values, false) else (value :: values, true)

/-- Select precisely the overlapping edge words required by `ClosedAt`. -/
private def matchingEdges [DecidableEq symbol] (edges : List (List symbol))
    (width : Nat) (tail : List symbol) : List (List symbol) :=
  edges.filter fun edge => edge.take (width - 1) = tail

private def addMids [DecidableEq symbol] (candidates : List (MidWord symbol))
    (mids : List (MidWord symbol)) : List (MidWord symbol) × Bool :=
  candidates.foldl (fun (mids, changed) mid =>
    let (mids, fresh) := insertNew mid mids
    (mids, changed || fresh)) (mids, false)

/-! ## Fixed-point construction -/

private def updateMid [DecidableEq symbol] (blank : symbol)
    (transition : PTM (Fin 3) symbol) (leftWidth rightWidth : Nat)
    (abstract : AbstractState symbol) (mid : MidWord symbol) :
    Option (AbstractState symbol × Bool) := do
  let _leftHead :: leftTail := mid.left | none
  let _rightHead :: rightTail := mid.right | none
  let action <- transition mid.state mid.center
  match action.move with
  | .right =>
      let (leftWords, edgeFresh) := insertNew mid.left abstract.leftWords
      let candidates :=
        (matchingEdges abstract.rightWords rightWidth rightTail).map fun edge =>
          NGramCPS.rightSuccessor action mid edge leftWidth blank
      let (mids, midFresh) := addMids candidates abstract.mids
      some ({ abstract with leftWords := leftWords, mids := mids },
        edgeFresh || midFresh)
  | .left =>
      let (rightWords, edgeFresh) := insertNew mid.right abstract.rightWords
      let candidates :=
        (matchingEdges abstract.leftWords leftWidth leftTail).map fun edge =>
          NGramCPS.leftSuccessor action mid edge rightWidth blank
      let (mids, midFresh) := addMids candidates abstract.mids
      some ({ abstract with rightWords := rightWords, mids := mids },
        edgeFresh || midFresh)

private def updateRound [DecidableEq symbol] (blank : symbol)
    (transition : PTM (Fin 3) symbol) (leftWidth rightWidth : Nat)
    (work : List (MidWord symbol)) (abstract : AbstractState symbol) :
    Option (AbstractState symbol × Bool) :=
  work.foldlM (fun (abstract, changed) mid => do
    let (abstract, fresh) <-
      updateMid blank transition leftWidth rightWidth abstract mid
    pure (abstract, changed || fresh)) (abstract, false)

private def closeToFixedPoint [DecidableEq symbol] (blank : symbol)
    (transition : PTM (Fin 3) symbol) (leftWidth rightWidth : Nat) :
    Nat -> AbstractState symbol -> Option (AbstractState symbol)
  | 0, _ => none
  | gas + 1, abstract =>
      match updateRound blank transition leftWidth rightWidth
          abstract.mids abstract with
      | none => none
      | some (abstract', changed) =>
          if changed then
            closeToFixedPoint blank transition leftWidth rightWidth gas abstract'
          else
            some abstract'

/-- Build a candidate abstract state from the constant blank zipper. -/
def buildCandidate [DecidableEq symbol] (blank : symbol)
    (transition : PTM (Fin 3) symbol)
    (leftWidth rightWidth gas : Nat) : Option (AbstractState symbol) :=
  if leftWidth = 0 || rightWidth = 0 then
    none
  else
    let left := List.replicate leftWidth blank
    let right := List.replicate rightWidth blank
    let initial : MidWord symbol :=
      { left, right, center := blank, state := 0 }
    closeToFixedPoint blank transition leftWidth rightWidth gas
      { leftWords := [left], rightWords := [right], mids := [initial] }

/-- Build and independently verify one n-gram CPS certificate. -/
private def validDecidable [DecidableEq symbol]
    (transition : PTM (Fin 3) symbol) (blank : symbol)
    (leftWidth rightWidth : Nat) (certificate : AbstractState symbol) :
    Decidable (NGramCPS.Valid transition (0 : Fin 3) blank
      leftWidth rightWidth certificate) := by
  unfold NGramCPS.Valid
  infer_instance

def check [DecidableEq symbol] (blank : symbol)
    (transition : PTM (Fin 3) symbol)
    (leftWidth rightWidth gas : Nat) : Bool :=
  match buildCandidate blank transition leftWidth rightWidth gas with
  | none => false
  | some certificate =>
      @decide (NGramCPS.Valid transition (0 : Fin 3) blank
        leftWidth rightWidth certificate)
        (validDecidable transition blank leftWidth rightWidth certificate)

theorem check_sound [DecidableEq symbol] {blank : symbol}
    {transition : PTM (Fin 3) symbol} {leftWidth rightWidth gas : Nat}
    (h : check blank transition leftWidth rightWidth gas = true) :
    exists certificate,
      buildCandidate blank transition leftWidth rightWidth gas = some certificate /\
      NGramCPS.Valid transition (0 : Fin 3) blank
        leftWidth rightWidth certificate := by
  unfold check at h
  cases hBuild : buildCandidate blank transition leftWidth rightWidth gas with
  | none => simp [hBuild] at h
  | some certificate =>
      refine ⟨certificate, rfl, ?_⟩
      have hDecide :
          @decide (NGramCPS.Valid transition (0 : Fin 3) blank
            leftWidth rightWidth certificate)
            (validDecidable transition blank leftWidth rightWidth certificate) =
            true := by
        simpa [hBuild] using h
      exact @of_decide_eq_true _
        (validDecidable transition blank leftWidth rightWidth certificate)
        hDecide

/-! ## Boolean and fixed-history specializations -/

/-- A tape symbol augmented with a bounded history of writes to its cell. -/
structure HistorySymbol where
  bit : Bool
  history : List (Fin 3 × Bool)
  deriving BEq, DecidableEq

def historyTransition (depth : Nat) (table : PTable) :
    PTM (Fin 3) HistorySymbol :=
  fun state symbol => do
    let action <- table state symbol.bit
    pure
      { write :=
          { bit := action.write
            history := ((state, symbol.bit) :: symbol.history).take depth }
        move := action.move
        next := action.next }

def boolCheck (table : PTable) (width gas : Nat) : Bool :=
  check false table.toPTM width width gas

def historyCheck (table : PTable) (depth width gas : Nat) : Bool :=
  check ({ bit := false, history := [] } : HistorySymbol)
    (historyTransition depth table) width width gas

theorem boolCheck_nonhalts {table : PTable} {width gas : Nat}
    (h : boolCheck table width gas = true) :
    table.toPTM.Nonhalts (0 : Fin 3) false := by
  rcases check_sound h with ⟨_certificate, _hBuild, hValid⟩
  exact hValid.nonhalts

theorem history_projects (depth : Nat) (table : PTable) :
    PTM.Projects (historyTransition depth table) table.toPTM
      (fun state => state) HistorySymbol.bit := by
  intro state symbol action hAction
  unfold historyTransition at hAction
  cases hLookup : table state symbol.bit with
  | none => simp [hLookup] at hAction
  | some goAction =>
      have hEq :
          ({ write :=
              { bit := goAction.write
                history := ((state, symbol.bit) :: symbol.history).take depth }
             move := goAction.move
             next := goAction.next } : PAction (Fin 3) HistorySymbol) =
            action := by
        simpa [hLookup] using hAction
      subst action
      simp [PTable.toPTM, hLookup, PAction.map]

theorem historyCheck_nonhalts {table : PTable} {depth width gas : Nat}
    (h : historyCheck table depth width gas = true) :
    table.toPTM.Nonhalts (0 : Fin 3) false := by
  rcases check_sound h with ⟨_certificate, _hBuild, hValid⟩
  have hHistory :
      (historyTransition depth table).Nonhalts (0 : Fin 3)
        ({ bit := false, history := [] } : HistorySymbol) :=
    hValid.nonhalts
  simpa using (history_projects depth table).nonhalts hHistory

/-- The parameter pipeline that covers every leaf in the exhaustive search:
the complete-table fast path, three Boolean passes, then two-write history. -/
def leaf (table : PTable) (_cfg : Config 3) : Bool :=
  tableComplete table ||
  boolCheck table 1 100 ||
  boolCheck table 2 200 ||
  boolCheck table 3 400 ||
  historyCheck table 2 2 1600

theorem leaf_sound : LeafSound leaf := by
  intro table _cfg M hAgree hLeaf steps
  by_cases hComplete : tableComplete table = true
  · exact tableComplete_run_active hComplete hAgree steps
  by_cases hOne : boolCheck table 1 100 = true
  · exact PTable.nonhalts_machine_of_agrees (boolCheck_nonhalts hOne) hAgree steps
  by_cases hTwo : boolCheck table 2 200 = true
  · exact PTable.nonhalts_machine_of_agrees (boolCheck_nonhalts hTwo) hAgree steps
  by_cases hThree : boolCheck table 3 400 = true
  · exact PTable.nonhalts_machine_of_agrees (boolCheck_nonhalts hThree) hAgree steps
  have hHistory : historyCheck table 2 2 1600 = true := by
    simpa [leaf, hComplete, hOne, hTwo, hThree] using hLeaf
  exact PTable.nonhalts_machine_of_agrees
    (historyCheck_nonhalts hHistory) hAgree steps

end NGram
end BB3
end BusyBeaver
end SetTheory
