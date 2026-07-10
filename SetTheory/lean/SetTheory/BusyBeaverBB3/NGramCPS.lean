/-
  BusyBeaverBB3/NGramCPS.lean

  A small, certificate-first formalization of the n-gram CPS nonhalting
  argument.  Certificates are ordinary lists.  `Valid` is therefore a fully
  decidable proposition: it checks the blank seed, word lengths, absence of a
  halting local transition, and closure of every recorded local context.

  The semantics use a zipper whose two one-sided tapes are functions from
  `Nat`, nearest cell first.  This makes the semantic invariant behind n-gram
  CPS particularly transparent: every sliding word beginning at distance at
  least two from the head belongs to the corresponding finite word set.
-/

import SetTheory.BusyBeaverBB3.Partial

namespace SetTheory
namespace BusyBeaver
namespace BB3
namespace NGramCPS

universe u v

namespace PConfig

def consSide (x : Symbol) (side : Nat -> Symbol) : Nat -> Symbol
  | 0 => x
  | n + 1 => side n

def tailSide (side : Nat -> Symbol) : Nat -> Symbol :=
  fun n => side (n + 1)

end PConfig

/-! ## Sliding tape words -/

/-- A finite sliding window in a one-sided tape, nearest symbol first. -/
def window (side : Nat -> Symbol) (start : Nat) : Nat -> List Symbol
  | 0 => []
  | len + 1 => side start :: window side (start + 1) len

@[simp]
theorem window_zero (side : Nat -> Symbol) (start : Nat) :
    window side start 0 = [] := rfl

@[simp]
theorem window_succ (side : Nat -> Symbol) (start len : Nat) :
    window side start (len + 1) =
      side start :: window side (start + 1) len := rfl

@[simp]
theorem length_window (side : Nat -> Symbol) (start len : Nat) :
    (window side start len).length = len := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih => simp [window, ih]

@[simp]
theorem window_const (blank : Symbol) (start len : Nat) :
    window (fun _ => blank) start len = List.replicate len blank := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih => simp [window, ih, List.replicate_succ]

@[simp]
theorem window_tailSide (side : Nat -> Symbol) (start len : Nat) :
    window (PConfig.tailSide side) start len = window side (start + 1) len := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih =>
      simp [window, PConfig.tailSide, ih, Nat.add_assoc]

@[simp]
theorem window_consSide_succ (x : Symbol) (side : Nat -> Symbol)
    (start len : Nat) :
    window (PConfig.consSide x side) (start + 1) len =
      window side start len := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih =>
      simp [window, PConfig.consSide, ih]

theorem take_window (side : Nat -> Symbol) (start len take : Nat) :
    (window side start len).take take = window side start (min take len) := by
  induction len generalizing start take with
  | zero => simp
  | succ len ih =>
      cases take with
      | zero => simp
      | succ take => simp [window, ih]

theorem window_take_pred (side : Nat -> Symbol) (start len : Nat) :
    (window side start len).take (len - 1) = window side start (len - 1) := by
  rw [take_window]
  congr
  omega

theorem window_one_take_pred_eq_tail_window_zero
    (side : Nat -> Symbol) (len : Nat) :
    (window side 1 len).take (len - 1) = (window side 0 len).drop 1 := by
  cases len with
  | zero => rfl
  | succ len =>
      rw [window_take_pred]
      rfl

theorem window_consSide_zero (x : Symbol) (side : Nat -> Symbol)
    {len : Nat} (hLen : 0 < len) :
    window (PConfig.consSide x side) 0 len =
      x :: (window side 0 len).take (len - 1) := by
  cases len with
  | zero => omega
  | succ len =>
      rw [window_take_pred]
      simp only [window_succ, PConfig.consSide]
      rw [window_consSide_succ]
      simp

theorem headD_window_zero (side : Nat -> Symbol) (blank : Symbol)
    {len : Nat} (hLen : 0 < len) :
    (window side 0 len).headD blank = side 0 := by
  cases len with
  | zero => omega
  | succ len => rfl

/-! A computationally decidable finite universal quantifier.  Core Lean's
`List` deliberately has no Prop-valued `Forall` predicate. -/

def All (P : α -> Prop) : List α -> Prop
  | [] => True
  | x :: xs => P x /\ All P xs

def allDecidable (P : α -> Prop) [DecidablePred P] :
    (xs : List α) -> Decidable (All P xs)
  | [] => isTrue trivial
  | x :: xs =>
      match (inferInstance : Decidable (P x)),
          allDecidable P xs with
      | isTrue hx, isTrue hxs => isTrue ⟨hx, hxs⟩
      | isFalse hx, _ => isFalse (fun h => hx h.1)
      | _, isFalse hxs => isFalse (fun h => hxs h.2)

instance [DecidablePred P] : Decidable (All P xs) :=
  allDecidable P xs

theorem All.of_mem {P : α -> Prop} {xs : List α}
    (h : All P xs) {x : α} (hx : x ∈ xs) : P x := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
      rcases h with ⟨hy, hys⟩
      simp only [List.mem_cons] at hx
      rcases hx with hxy | hx
      · exact hxy ▸ hy
      · exact ih hys hx

/-! ## Finite declarative certificates -/

/-- A local configuration: the two immediate words, symbol under the head,
and operational state. -/
structure MidWord (State : Type u) (Symbol : Type v) where
  left : List Symbol
  right : List Symbol
  center : Symbol
  state : State
  deriving DecidableEq, Repr

/-- The finite abstract execution state used as an n-gram certificate. -/
structure Cert (State : Type u) (Symbol : Type v) where
  leftWords : List (List Symbol)
  rightWords : List (List Symbol)
  mids : List (MidWord State Symbol)
  deriving DecidableEq, Repr

def rightSuccessor (action : PAction State Symbol)
    (mw : MidWord State Symbol) (edge : List Symbol) (leftLen : Nat)
    (blank : Symbol) : MidWord State Symbol where
  left := action.write :: mw.left.take (leftLen - 1)
  right := edge
  center := mw.right.headD blank
  state := action.next

def leftSuccessor (action : PAction State Symbol)
    (mw : MidWord State Symbol) (edge : List Symbol) (rightLen : Nat)
    (blank : Symbol) : MidWord State Symbol where
  left := edge
  right := action.write :: mw.right.take (rightLen - 1)
  center := mw.left.headD blank
  state := action.next

/-- Declarative closure of one recorded local context.  `List.Forall` is used
deliberately: unlike an unbounded `forall edge`, this proposition is directly
decidable for finite certificates. -/
def ClosedAt [DecidableEq Symbol] [DecidableEq State]
    (M : PTM State Symbol) (leftLen rightLen : Nat) (blank : Symbol)
    (cert : Cert State Symbol) (mw : MidWord State Symbol) : Prop :=
  match M mw.state mw.center with
  | none => False
  | some action =>
      match action.move with
      | Move.right =>
          mw.left ∈ cert.leftWords /\
          All (fun edge =>
            edge.take (rightLen - 1) = mw.right.drop 1 ->
              rightSuccessor action mw edge leftLen blank ∈ cert.mids)
            cert.rightWords
      | Move.left =>
          mw.right ∈ cert.rightWords /\
          All (fun edge =>
            edge.take (leftLen - 1) = mw.left.drop 1 ->
              leftSuccessor action mw edge rightLen blank ∈ cert.mids)
            cert.leftWords

instance [DecidableEq Symbol] [DecidableEq State]
    {M : PTM State Symbol} {leftLen rightLen : Nat} {blank : Symbol}
    {cert : Cert State Symbol} {mw : MidWord State Symbol} :
    Decidable (ClosedAt M leftLen rightLen blank cert mw) := by
  unfold ClosedAt
  cases hAction : M mw.state mw.center with
  | none =>
      simp only
      exact inferInstance
  | some action =>
      simp only
      cases action.move <;> simp only <;> infer_instance

/-- A completely declarative, finite n-gram CPS certificate. -/
def Valid [DecidableEq Symbol] [DecidableEq State]
    (M : PTM State Symbol) (start : State) (blank : Symbol)
    (leftLen rightLen : Nat) (cert : Cert State Symbol) : Prop :=
  0 < leftLen /\
  0 < rightLen /\
  All (fun word => word.length = leftLen) cert.leftWords /\
  All (fun word => word.length = rightLen) cert.rightWords /\
  All (fun mw =>
    mw.left.length = leftLen /\ mw.right.length = rightLen) cert.mids /\
  List.replicate leftLen blank ∈ cert.leftWords /\
  List.replicate rightLen blank ∈ cert.rightWords /\
  ({ left := List.replicate leftLen blank
     right := List.replicate rightLen blank
     center := blank
     state := start } : MidWord State Symbol) ∈ cert.mids /\
  All (ClosedAt M leftLen rightLen blank cert) cert.mids

/-! ## Semantic invariant -/

def MidWord.Matches (leftLen rightLen : Nat)
    (cfg : PConfig State Symbol) (mw : MidWord State Symbol) : Prop :=
  mw.state = cfg.state /\
  mw.center = cfg.center /\
  mw.left = window cfg.left 0 leftLen /\
  mw.right = window cfg.right 0 rightLen

/-- Every word starting at least one cell beyond the immediate word's start
(i.e. at tape distance at least two) occurs in the recorded set. -/
def FarMatches (words : List (List Symbol)) (side : Nat -> Symbol)
    (len : Nat) : Prop :=
  forall start, 1 <= start -> window side start len ∈ words

def InCert (leftLen rightLen : Nat) (cert : Cert State Symbol)
    (cfg : PConfig State Symbol) : Prop :=
  (exists mw, mw ∈ cert.mids /\ mw.Matches leftLen rightLen cfg) /\
  FarMatches cert.leftWords cfg.left leftLen /\
  FarMatches cert.rightWords cfg.right rightLen

theorem FarMatches.consSide
    {words : List (List Symbol)} {side : Nat -> Symbol} {len : Nat}
    (x : Symbol) (hImmediate : window side 0 len ∈ words)
    (hFar : FarMatches words side len) :
    FarMatches words (PConfig.consSide x side) len := by
  intro start hStart
  cases start with
  | zero => omega
  | succ start =>
      rw [window_consSide_succ]
      cases start with
      | zero => exact hImmediate
      | succ start =>
          exact hFar (start + 1) (by omega)

theorem FarMatches.tailSide
    {words : List (List Symbol)} {side : Nat -> Symbol} {len : Nat}
    (hFar : FarMatches words side len) :
    FarMatches words (PConfig.tailSide side) len := by
  intro start hStart
  rw [window_tailSide]
  exact hFar (start + 1) (by omega)

/-! ## Soundness -/

namespace Valid

theorem initial_inCert [DecidableEq Symbol] [DecidableEq State]
    {M : PTM State Symbol} {start : State} {blank : Symbol}
    {leftLen rightLen : Nat} {cert : Cert State Symbol}
    (hValid : Valid M start blank leftLen rightLen cert) :
    InCert leftLen rightLen cert (PConfig.blank start blank) := by
  rcases hValid with
    ⟨_hLeftPos, _hRightPos, _hLeftLengths, _hRightLengths, _hMidLengths,
      hBlankLeft, hBlankRight, hInitial, _hClosed⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨
      { left := List.replicate leftLen blank
        right := List.replicate rightLen blank
        center := blank
        state := start }, hInitial, ?_⟩
    simp [MidWord.Matches, PConfig.blank, window_const]
  · intro wordStart _hStart
    simpa [PConfig.blank, window_const] using hBlankLeft
  · intro wordStart _hStart
    simpa [PConfig.blank, window_const] using hBlankRight

theorem step [DecidableEq Symbol] [DecidableEq State]
    {M : PTM State Symbol} {start : State} {blank : Symbol}
    {leftLen rightLen : Nat} {cert : Cert State Symbol}
    (hValid : Valid M start blank leftLen rightLen cert)
    {cfg : PConfig State Symbol}
    (hIn : InCert leftLen rightLen cert cfg) :
    exists next,
      M.step? cfg = some next /\ InCert leftLen rightLen cert next := by
  rcases hValid with
    ⟨hLeftPos, hRightPos, _hLeftLengths, _hRightLengths, _hMidLengths,
      _hBlankLeft, _hBlankRight, _hInitial, hClosed⟩
  rcases hIn with ⟨⟨mw, hMw, hMatches⟩, hFarLeft, hFarRight⟩
  rcases hMatches with ⟨hState, hCenter, hLeft, hRight⟩
  have hClose := hClosed.of_mem hMw
  cases hAction : M mw.state mw.center with
  | none =>
      simp [ClosedAt, hAction] at hClose
  | some action =>
      have hLookup : M cfg.state cfg.center = some action := by
        simpa [hState, hCenter] using hAction
      have hStep :
          M.step? cfg = some (PTM.stepAction cfg action) := by
        simp [PTM.step?, hLookup]
      cases hMove : action.move with
      | right =>
          have hCloseRight :
              mw.left ∈ cert.leftWords /\
              All (fun edge =>
                edge.take (rightLen - 1) = mw.right.drop 1 ->
                  rightSuccessor action mw edge leftLen blank ∈ cert.mids)
                cert.rightWords := by
            simpa [ClosedAt, hAction, hMove] using hClose
          let edge := window cfg.right 1 rightLen
          have hEdge : edge ∈ cert.rightWords :=
            hFarRight 1 (by omega)
          have hEdgePrefix :
              edge.take (rightLen - 1) = mw.right.drop 1 := by
            dsimp [edge]
            rw [window_one_take_pred_eq_tail_window_zero, <- hRight]
          have hNextMid :
              rightSuccessor action mw edge leftLen blank ∈ cert.mids :=
            (hCloseRight.2.of_mem hEdge) hEdgePrefix
          have hNextCenter : mw.right.headD blank = cfg.right 0 := by
            rw [hRight]
            exact headD_window_zero cfg.right blank hRightPos
          have hNextLeft :
              (rightSuccessor action mw edge leftLen blank).left =
                window (PTM.stepAction cfg action).left 0 leftLen := by
            rw [show (rightSuccessor action mw edge leftLen blank).left =
                action.write :: mw.left.take (leftLen - 1) by rfl]
            rw [hLeft]
            simp only [PTM.stepAction, hMove]
            change action.write :: (window cfg.left 0 leftLen).take (leftLen - 1) =
              window (PConfig.consSide action.write cfg.left) 0 leftLen
            rw [window_consSide_zero action.write cfg.left hLeftPos]
          have hNextRight :
              (rightSuccessor action mw edge leftLen blank).right =
                window (PTM.stepAction cfg action).right 0 rightLen := by
            dsimp [rightSuccessor, edge, PTM.stepAction]
            rw [hMove]
            exact (window_tailSide cfg.right 0 rightLen).symm
          refine ⟨PTM.stepAction cfg action, hStep, ?_⟩
          refine ⟨⟨rightSuccessor action mw edge leftLen blank, hNextMid, ?_⟩,
            ?_, ?_⟩
          · refine ⟨?_, ?_, hNextLeft, hNextRight⟩
            · simp [rightSuccessor, PTM.stepAction, hMove]
            · simpa [rightSuccessor, PTM.stepAction, hMove] using hNextCenter
          · have hImmediate : window cfg.left 0 leftLen ∈ cert.leftWords := by
              rw [<- hLeft]
              exact hCloseRight.1
            simp only [PTM.stepAction, hMove]
            change FarMatches cert.leftWords
              (PConfig.consSide action.write cfg.left) leftLen
            exact hFarLeft.consSide action.write hImmediate
          · simp only [PTM.stepAction, hMove]
            change FarMatches cert.rightWords
              (PConfig.tailSide cfg.right) rightLen
            exact hFarRight.tailSide
      | left =>
          have hCloseLeft :
              mw.right ∈ cert.rightWords /\
              All (fun edge =>
                edge.take (leftLen - 1) = mw.left.drop 1 ->
                  leftSuccessor action mw edge rightLen blank ∈ cert.mids)
                cert.leftWords := by
            simpa [ClosedAt, hAction, hMove] using hClose
          let edge := window cfg.left 1 leftLen
          have hEdge : edge ∈ cert.leftWords :=
            hFarLeft 1 (by omega)
          have hEdgePrefix :
              edge.take (leftLen - 1) = mw.left.drop 1 := by
            dsimp [edge]
            rw [window_one_take_pred_eq_tail_window_zero, <- hLeft]
          have hNextMid :
              leftSuccessor action mw edge rightLen blank ∈ cert.mids :=
            (hCloseLeft.2.of_mem hEdge) hEdgePrefix
          have hNextCenter : mw.left.headD blank = cfg.left 0 := by
            rw [hLeft]
            exact headD_window_zero cfg.left blank hLeftPos
          have hNextLeft :
              (leftSuccessor action mw edge rightLen blank).left =
                window (PTM.stepAction cfg action).left 0 leftLen := by
            dsimp [leftSuccessor, edge, PTM.stepAction]
            rw [hMove]
            exact (window_tailSide cfg.left 0 leftLen).symm
          have hNextRight :
              (leftSuccessor action mw edge rightLen blank).right =
                window (PTM.stepAction cfg action).right 0 rightLen := by
            rw [show (leftSuccessor action mw edge rightLen blank).right =
                action.write :: mw.right.take (rightLen - 1) by rfl]
            rw [hRight]
            simp only [PTM.stepAction, hMove]
            change action.write :: (window cfg.right 0 rightLen).take (rightLen - 1) =
              window (PConfig.consSide action.write cfg.right) 0 rightLen
            rw [window_consSide_zero action.write cfg.right hRightPos]
          refine ⟨PTM.stepAction cfg action, hStep, ?_⟩
          refine ⟨⟨leftSuccessor action mw edge rightLen blank, hNextMid, ?_⟩,
            ?_, ?_⟩
          · refine ⟨?_, ?_, hNextLeft, hNextRight⟩
            · simp [leftSuccessor, PTM.stepAction, hMove]
            · simpa [leftSuccessor, PTM.stepAction, hMove] using hNextCenter
          · simp only [PTM.stepAction, hMove]
            change FarMatches cert.leftWords
              (PConfig.tailSide cfg.left) leftLen
            exact hFarLeft.tailSide
          · have hImmediate : window cfg.right 0 rightLen ∈ cert.rightWords := by
              rw [<- hRight]
              exact hCloseLeft.1
            simp only [PTM.stepAction, hMove]
            change FarMatches cert.rightWords
              (PConfig.consSide action.write cfg.right) rightLen
            exact hFarRight.consSide action.write hImmediate

theorem run?_exists [DecidableEq Symbol] [DecidableEq State]
    {M : PTM State Symbol} {start : State} {blank : Symbol}
    {leftLen rightLen : Nat} {cert : Cert State Symbol}
    (hValid : Valid M start blank leftLen rightLen cert)
    {cfg : PConfig State Symbol}
    (hIn : InCert leftLen rightLen cert cfg) :
    forall steps, exists result,
      M.run? cfg steps = some result /\
      InCert leftLen rightLen cert result := by
  intro steps
  induction steps with
  | zero => exact ⟨cfg, rfl, hIn⟩
  | succ steps ih =>
      rcases ih with ⟨middle, hRun, hMiddle⟩
      rcases hValid.step hMiddle with ⟨result, hStep, hResult⟩
      refine ⟨result, ?_, hResult⟩
      simp [PTM.run?, hRun, hStep]

/-- A valid finite n-gram CPS certificate proves a genuinely infinite run of
the partial machine from the blank tape. -/
theorem nonhalts [DecidableEq Symbol] [DecidableEq State]
    {M : PTM State Symbol} {start : State} {blank : Symbol}
    {leftLen rightLen : Nat} {cert : Cert State Symbol}
    (hValid : Valid M start blank leftLen rightLen cert) :
    M.Nonhalts start blank := by
  intro steps
  rcases hValid.run?_exists hValid.initial_inCert steps with
    ⟨result, hRun, _hIn⟩
  exact ⟨result, hRun⟩

end Valid

end NGramCPS
end BB3
end BusyBeaver
end SetTheory
