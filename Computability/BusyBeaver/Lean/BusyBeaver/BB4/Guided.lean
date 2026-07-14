/-
  BusyBeaver/BB4/Guided.lean

  A proof-carrying, guided version of the four-state TNF search.  An untrusted
  generator may choose where to branch and which already-proved nonhalting
  method to try, but `verify` checks every choice in the kernel.  In
  particular, a successful hint can close a partial table immediately instead
  of rerunning all earlier failed n-gram passes at the fuel boundary.
-/

import BusyBeaver.BB4.Certificates.Common
import BusyBeaver.BB4.Certificates.R05.A14.Guided.HistoryInvariant
import BusyBeaver.BB4.Certificates.R05.A14.Guided.HistoryInvariantA15A09A03A02A04
import BusyBeaver.BB4.Certificates.R13.C14.Uncovered

set_option maxRecDepth 10000

namespace SetTheory
namespace BusyBeaver
namespace BB4
namespace Guided

open Certificates

/-! ## Independently checked nonhalting hints -/

inductive Hint where
  | complete
  | ngram (value : NGram.Pass)
  | historyCertificate (depth width : Nat)
      (certificate : NGram.AbstractState NGram.HistorySymbol)
  | sporadic
  | r05A14HistoryInvariant
  | r05A14A15Pump
  | c14Uncovered
  deriving DecidableEq, Repr

def Hint.check : Hint -> PTable -> Config 4 -> Bool
  | .complete, table, cfg => completeLeaf table cfg
  | .ngram pass, table, _cfg => pass.check table
  | .historyCertificate depth width certificate, table, _cfg =>
      NGram.historyCertificateCheck table depth width certificate
  | .sporadic, table, cfg => sporadicLeaf table cfg
  | .r05A14HistoryInvariant, table, cfg =>
      Certificates.R05A14HistoryInvariant.leaf table cfg
  | .r05A14A15Pump, table, cfg =>
      Certificates.R05A14HistoryInvariantA15A09A03A02A04.leaf table cfg
  | .c14Uncovered, table, cfg => Certificates.C14Uncovered.leaf table cfg

theorem Hint.check_sound (hint : Hint) :
    LeafSound (fun table cfg => hint.check table cfg) := by
  intro table cfg machine hAgree hCheck steps
  cases hint with
  | complete =>
      exact completeLeaf_sound table cfg machine hAgree
        (by simpa [Hint.check] using hCheck) steps
  | ngram pass =>
      exact PTable.nonhalts_machine_of_agrees
        (NGram.Pass.check_nonhalts (by simpa [Hint.check] using hCheck))
        hAgree steps
  | historyCertificate depth width certificate =>
      exact PTable.nonhalts_machine_of_agrees
        (NGram.historyCertificateCheck_nonhalts
          (by simpa [Hint.check] using hCheck))
        hAgree steps
  | sporadic =>
      exact sporadicLeaf_sound table cfg machine hAgree
        (by simpa [Hint.check] using hCheck) steps
  | r05A14HistoryInvariant =>
      exact Certificates.R05A14HistoryInvariant.leaf_sound table cfg machine hAgree
        (by simpa [Hint.check] using hCheck) steps
  | r05A14A15Pump =>
      exact Certificates.R05A14HistoryInvariantA15A09A03A02A04.leaf_sound
        table cfg machine hAgree (by simpa [Hint.check] using hCheck) steps
  | c14Uncovered =>
      exact Certificates.C14Uncovered.leaf_sound table cfg machine hAgree
        (by simpa [Hint.check] using hCheck) steps

theorem Hint.check_config_irrel (hint : Hint) (table : PTable)
    (left right : Config 4) :
    hint.check table left = hint.check table right := by
  cases hint <;> rfl

/-! ## Certificate trees -/

inductive Certificate where
  | legacy
  | close (hint : Hint)
  | branch (children : GoAction -> Certificate)

namespace Certificate

def complete : Certificate := .close .complete
def bool1 : Certificate := .close (.ngram (.bool 1 100))
def bool2 : Certificate := .close (.ngram (.bool 2 200))
def bool3 : Certificate := .close (.ngram (.bool 3 400))
def history2x2 : Certificate := .close (.ngram (.history 2 2 1600))
def history2x3 : Certificate := .close (.ngram (.history 2 3 1600))
def history4x2 : Certificate := .close (.ngram (.history 4 2 600))
def suppliedHistory (depth width : Nat)
    (certificate : NGram.AbstractState NGram.HistorySymbol) : Certificate :=
  .close (.historyCertificate depth width certificate)
def history4x3 : Certificate := .close (.ngram (.history 4 3 1600))
def history6x2 : Certificate := .close (.ngram (.history 6 2 3200))
def history6x3 : Certificate := .close (.ngram (.history 6 3 3200))
def history8x2 : Certificate := .close (.ngram (.history 8 2 1600))
def history8x3 : Certificate := .close (.ngram (.history 8 3 1600))
def history10x4 : Certificate := .close (.ngram (.history 10 4 10000))
def sporadic : Certificate := .close .sporadic
def r05A14HistoryInvariant : Certificate := .close .r05A14HistoryInvariant
def r05A14A15Pump : Certificate := .close .r05A14A15Pump
def c14Uncovered : Certificate := .close .c14Uncovered

/-- A compact constructor for the sixteen continuing-action children. -/
def children16
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    GoAction -> Certificate := fun action =>
  match action.write, action.move, action.next.val with
  | false, .left, 0 => c00
  | false, .left, 1 => c01
  | false, .left, 2 => c02
  | false, .left, _ => c03
  | false, .right, 0 => c04
  | false, .right, 1 => c05
  | false, .right, 2 => c06
  | false, .right, _ => c07
  | true, .left, 0 => c08
  | true, .left, 1 => c09
  | true, .left, 2 => c10
  | true, .left, _ => c11
  | true, .right, 0 => c12
  | true, .right, 1 => c13
  | true, .right, 2 => c14
  | true, .right, _ => c15

def branch16
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) : Certificate :=
  .branch (children16 c00 c01 c02 c03 c04 c05 c06 c07
    c08 c09 c10 c11 c12 c13 c14 c15)

@[simp] theorem children16_a00
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a00 = c00 := by
  rfl

@[simp] theorem children16_a01
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a01 = c01 := by
  rfl

@[simp] theorem children16_a02
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a02 = c02 := by
  rfl

@[simp] theorem children16_a03
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a03 = c03 := by
  rfl

@[simp] theorem children16_a04
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a04 = c04 := by
  rfl

@[simp] theorem children16_a05
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a05 = c05 := by
  rfl

@[simp] theorem children16_a06
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a06 = c06 := by
  rfl

@[simp] theorem children16_a07
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a07 = c07 := by
  rfl

@[simp] theorem children16_a08
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a08 = c08 := by
  rfl

@[simp] theorem children16_a09
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a09 = c09 := by
  rfl

@[simp] theorem children16_a10
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a10 = c10 := by
  rfl

@[simp] theorem children16_a11
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a11 = c11 := by
  rfl

@[simp] theorem children16_a12
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a12 = c12 := by
  rfl

@[simp] theorem children16_a13
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a13 = c13 := by
  rfl

@[simp] theorem children16_a14
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a14 = c14 := by
  rfl

@[simp] theorem children16_a15
    (c00 c01 c02 c03 c04 c05 c06 c07 : Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Certificate) :
    children16 c00 c01 c02 c03 c04 c05 c06 c07
      c08 c09 c10 c11 c12 c13 c14 c15 a15 = c15 := by
  rfl

/-- The four representatives retained by the root target/direction reduction. -/
def roots4 (c04 c05 c12 c13 : Certificate) : GoAction -> Certificate :=
  fun action =>
    if action = a04 then c04 else
    if action = a05 then c05 else
    if action = a12 then c12 else c13

end Certificate

/-! ## Normalized proof work -/

structure Work where
  fuel : Nat
  used : Nat
  table : PTable
  cfg : Config 4

namespace Work

def normalizeFrom : Nat -> Nat -> PTable -> Config 4 -> Work
  | 0, used, table, cfg => ⟨0, used, table, cfg⟩
  | fuel + 1, used, table, cfg =>
      match cfg.state with
      | none => ⟨fuel + 1, used, table, cfg⟩
      | some state =>
          let bit := Tape.read cfg.tape cfg.head
          match table state bit with
          | none => ⟨fuel + 1, used, table, cfg⟩
          | some action =>
              normalizeFrom fuel used table (stepGo cfg action)

def normalize (work : Work) : Work :=
  normalizeFrom work.fuel work.used work.table work.cfg

def assign (work : Work) (action : GoAction) : Work :=
  match work.fuel, work.cfg.state with
  | fuel + 1, some state =>
      let bit := Tape.read work.cfg.tape work.cfg.head
      ⟨fuel, TNF.grow work.used action,
        work.table.set state bit action, stepGo work.cfg action⟩
  | _, _ => work

def choose (work : Work) (action : GoAction) : Work :=
  (work.assign action).normalize

end Work

/-! ## Executable verifier -/

def verify : Nat -> Nat -> PTable -> Config 4 -> Certificate -> Bool
  | fuel, used, table, cfg, .legacy =>
      TNF.checkFrom leaf fuel used table cfg
  | _fuel, _used, table, cfg, .close hint => hint.check table cfg
  | 0, _used, _table, cfg, .branch _children =>
      match cfg.state with
      | none => decide (cfg.tape.length <= 13)
      | some _ => false
  | fuel + 1, used, table, cfg, .branch children =>
      match cfg.state with
      | none => decide (cfg.tape.length <= 13)
      | some state =>
          let bit := Tape.read cfg.tape cfg.head
          match table state bit with
          | some action =>
              verify fuel used table (stepGo cfg action) (.branch children)
          | none =>
              haltWritesSafe cfg &&
                (TNF.canonicalActions used).all fun action =>
                  verify fuel (TNF.grow used action)
                    (table.set state bit action) (stepGo cfg action)
                    (children action)

namespace Work

def check (work : Work) (certificate : Certificate) : Bool :=
  verify work.fuel work.used work.table work.cfg certificate

theorem check_normalizeFrom (certificate : Certificate) :
    forall fuel used table cfg,
      check ⟨fuel, used, table, cfg⟩ certificate =
        check (normalizeFrom fuel used table cfg) certificate := by
  intro fuel
  induction fuel with
  | zero =>
      intro used table cfg
      rfl
  | succ fuel ih =>
      intro used table cfg
      cases hState : cfg.state with
      | none => simp [normalizeFrom, hState]
      | some state =>
          let bit := Tape.read cfg.tape cfg.head
          cases hLookup : table state bit with
          | none => simp [normalizeFrom, hState, bit, hLookup]
          | some action =>
              cases certificate with
              | legacy =>
                  simpa [check, normalizeFrom, verify, TNF.checkFrom,
                    hState, bit, hLookup]
                    using ih used table (stepGo cfg action)
              | close hint =>
                  calc
                    check ⟨fuel + 1, used, table, cfg⟩ (.close hint) =
                        check ⟨fuel, used, table, stepGo cfg action⟩
                          (.close hint) := by
                      simpa [check, verify] using
                        Hint.check_config_irrel hint table cfg
                          (stepGo cfg action)
                    _ = check
                        (normalizeFrom fuel used table (stepGo cfg action))
                          (.close hint) :=
                      ih used table (stepGo cfg action)
                    _ = check
                        (normalizeFrom (fuel + 1) used table cfg)
                          (.close hint) := by
                      simp [normalizeFrom, hState, bit, hLookup]
              | branch children =>
                  simpa [check, normalizeFrom, verify, hState, bit, hLookup]
                    using ih used table (stepGo cfg action)

theorem check_normalize (work : Work) (certificate : Certificate) :
    work.check certificate = work.normalize.check certificate := by
  cases work
  exact check_normalizeFrom certificate _ _ _ _

theorem check_assign_eq_choose (work : Work) (action : GoAction)
    (certificate : Certificate) :
    (work.assign action).check certificate =
      (work.choose action).check certificate :=
  check_normalize (work.assign action) certificate

end Work

private theorem false_of_close {hint : Hint} {table : PTable}
    {cfg : Config 4} {machine : Machine 4}
    (hCheck : hint.check table cfg = true)
    (hAgree : table.Agrees machine) (hReach : Reachable machine cfg)
    {steps : Nat} (hHalted : (machine.runFrom cfg steps).state = none) :
    False := by
  rcases hReach with ⟨start, hCfg⟩
  have hRun : machine.run (start + steps) = machine.runFrom cfg steps := by
    rw [hCfg, Machine.run_add_eq_runFrom]
  have hGlobalHalted : (machine.run (start + steps)).state = none :=
    (congrArg Config.state hRun).trans hHalted
  exact Hint.check_sound hint table cfg machine hAgree hCheck
    (start + steps) hGlobalHalted

/-- Kernel verification of a guided tree has the same semantic score guarantee
as the exhaustive TNF Boolean, without trusting the generator's hints. -/
theorem verify_sound :
    forall fuel used table cfg certificate machine,
      verify fuel used table cfg certificate = true ->
      TNF.PrefixInvariant used table cfg ->
      table.Agrees machine ->
      Reachable machine cfg ->
      forall steps,
        (machine.runFrom cfg steps).state = none ->
        (machine.runFrom cfg steps).tape.length <= 13 := by
  intro fuel
  induction fuel with
  | zero =>
      intro used table cfg certificate machine hVerify hInv hAgree hReach
        steps hHalted
      cases certificate with
      | legacy =>
          exact TNF.checkFrom_sound leaf_sound 0 used table cfg machine
            hVerify hInv hAgree hReach steps hHalted
      | close hint =>
          exact False.elim
            (false_of_close hVerify hAgree hReach hHalted)
      | branch children =>
          cases hState : cfg.state with
          | none =>
              have hRun := Machine.runFrom_of_halted machine cfg hState steps
              have hBound : cfg.tape.length <= 13 :=
                of_decide_eq_true (by
                  simpa [verify, hState] using hVerify)
              simpa [hRun] using hBound
          | some state => simp [verify, hState] at hVerify
  | succ fuel ih =>
      intro used table cfg certificate machine hVerify hInv hAgree hReach
        steps hHalted
      cases certificate with
      | legacy =>
          exact TNF.checkFrom_sound leaf_sound (fuel + 1) used table cfg
            machine hVerify hInv hAgree hReach steps hHalted
      | close hint =>
          exact False.elim
            (false_of_close hVerify hAgree hReach hHalted)
      | branch children =>
          cases hState : cfg.state with
          | none =>
              have hRun := Machine.runFrom_of_halted machine cfg hState steps
              have hBound : cfg.tape.length <= 13 :=
                of_decide_eq_true (by
                  simpa [verify, hState] using hVerify)
              simpa [hRun] using hBound
          | some state =>
              cases steps with
              | zero => simp [Machine.runFrom, hState] at hHalted
              | succ steps =>
                  let bit := Tape.read cfg.tape cfg.head
                  cases hLookup : table state bit with
                  | some assigned =>
                      have hAction := hAgree state bit assigned hLookup
                      have hStep := stepGo_eq_step machine cfg state assigned
                        hState hAction
                      have hReach' : Reachable machine
                          (stepGo cfg assigned) := by
                        rw [hStep]
                        exact hReach.step
                      have hInv' : TNF.PrefixInvariant used table
                          (stepGo cfg assigned) :=
                        hInv.step_known hLookup
                      have hBranch : verify fuel used table
                          (stepGo cfg assigned) (.branch children) = true := by
                        simpa [verify, hState, bit, hLookup] using hVerify
                      rw [runFrom_succ_start, ← hStep] at hHalted
                      rw [runFrom_succ_start, ← hStep]
                      exact ih used table (stepGo cfg assigned)
                        (.branch children) machine hBranch hInv' hAgree hReach'
                        steps hHalted
                  | none =>
                      have hNode :
                          (haltWritesSafe cfg &&
                            (TNF.canonicalActions used).all fun action =>
                              verify fuel (TNF.grow used action)
                                (table.set state bit action)
                                (stepGo cfg action) (children action)) = true := by
                        simpa [verify, hState, bit, hLookup] using hVerify
                      have hParts := Bool.and_eq_true_iff.mp hNode
                      cases hTransition : machine.transition state bit with
                      | mk write move next =>
                          cases next with
                          | none =>
                              have hStepState :
                                  (machine.step cfg).state = none := by
                                simp [Machine.step, hState, bit, hTransition]
                              rw [runFrom_succ_start]
                              rw [Machine.runFrom_of_halted machine (machine.step cfg)
                                hStepState steps]
                              simpa [Machine.step, hState, bit, hTransition] using
                                haltWritesSafe_sound hParts.1 write
                          | some next =>
                              by_cases hCanonical : next.val <= used
                              · let action : GoAction := { write, move, next }
                                have hAction : action.toAction =
                                    machine.transition state bit := by
                                  simp [action, GoAction.toAction, hTransition]
                                have hMember :
                                    action ∈ TNF.canonicalActions used :=
                                  TNF.mem_canonicalActions action hCanonical
                                have hBranch : verify fuel
                                    (TNF.grow used action)
                                    (table.set state bit action)
                                    (stepGo cfg action) (children action) = true :=
                                  (List.all_eq_true.mp hParts.2) action hMember
                                have hInv' : TNF.PrefixInvariant
                                    (TNF.grow used action)
                                    (table.set state bit action)
                                    (stepGo cfg action) :=
                                  hInv.step_fresh hState
                                have hAgree' :
                                    (table.set state bit action).Agrees machine :=
                                  PTable.set_agrees hAgree hAction
                                have hStep := stepGo_eq_step machine cfg state
                                  action hState hAction
                                have hReach' : Reachable machine
                                    (stepGo cfg action) := by
                                  rw [hStep]
                                  exact hReach.step
                                rw [runFrom_succ_start, ← hStep] at hHalted
                                rw [runFrom_succ_start, ← hStep]
                                exact ih (TNF.grow used action)
                                  (table.set state bit action)
                                  (stepGo cfg action) (children action) machine
                                  hBranch hInv' hAgree' hReach' steps hHalted
                              · have hUsedNext : used < next.val :=
                                  Nat.lt_of_not_ge hCanonical
                                have hUsedFour : used < 4 := by omega
                                let fresh : Fin 4 := ⟨used, hUsedFour⟩
                                let equiv : TNF.Perm :=
                                  TNF.Perm.swap next fresh
                                let renamed : Machine 4 :=
                                  TNF.Rename.machine equiv machine
                                let action : GoAction :=
                                  { write, move, next := fresh }
                                have hFix : TNF.Rename.FixesPrefix used equiv := by
                                  apply TNF.Rename.swap_fixesPrefix
                                  · exact Nat.le_of_lt hUsedNext
                                  · simp [fresh]
                                have hStateFix : equiv state = state :=
                                  hFix state (hInv.state_prefix state hState)
                                have hStateSymm : equiv.symm state = state := by
                                  have hRoundTrip :=
                                    TNF.Perm.symm_apply_apply equiv state
                                  simpa [hStateFix] using hRoundTrip
                                have hAction : action.toAction =
                                    renamed.transition state bit := by
                                  change action.toAction =
                                    TNF.Rename.action equiv
                                      (machine.transition (equiv.symm state) bit)
                                  rw [hStateSymm, hTransition]
                                  simp [action, fresh, equiv, TNF.Rename.action,
                                    GoAction.toAction, TNF.Perm.swap_apply_left]
                                have hMember :
                                    action ∈ TNF.canonicalActions used := by
                                  apply TNF.mem_canonicalActions
                                  simp [action, fresh]
                                have hBranch : verify fuel
                                    (TNF.grow used action)
                                    (table.set state bit action)
                                    (stepGo cfg action) (children action) = true :=
                                  (List.all_eq_true.mp hParts.2) action hMember
                                have hInv' : TNF.PrefixInvariant
                                    (TNF.grow used action)
                                    (table.set state bit action)
                                    (stepGo cfg action) :=
                                  hInv.step_fresh hState
                                have hAgreeRenamed : table.Agrees renamed :=
                                  TNF.agrees_rename_of_prefix hInv hAgree hFix
                                have hAgree' :
                                    (table.set state bit action).Agrees renamed :=
                                  PTable.set_agrees hAgreeRenamed hAction
                                have hReachRenamed : Reachable renamed cfg :=
                                  TNF.reachable_rename_of_prefix hInv hReach hFix
                                have hStep := stepGo_eq_step renamed cfg state
                                  action hState hAction
                                have hReach' : Reachable renamed
                                    (stepGo cfg action) := by
                                  rw [hStep]
                                  exact hReachRenamed.step
                                have hRunRename :
                                    renamed.runFrom cfg (steps + 1) =
                                      TNF.Rename.config equiv
                                        (machine.runFrom cfg (steps + 1)) :=
                                  TNF.runFrom_rename_of_prefix hInv hFix
                                    (steps + 1)
                                have hHaltedRenamed :
                                    (renamed.runFrom cfg (steps + 1)).state =
                                      none := by
                                  rw [hRunRename]
                                  simp [TNF.Rename.config, hHalted]
                                rw [runFrom_succ_start, ← hStep] at hHaltedRenamed
                                have hBound :
                                    (renamed.runFrom (stepGo cfg action)
                                      steps).tape.length <= 13 :=
                                  ih (TNF.grow used action)
                                    (table.set state bit action)
                                    (stepGo cfg action) (children action)
                                    renamed hBranch hInv' hAgree' hReach' steps
                                    hHaltedRenamed
                                have hBoundFull :
                                    (renamed.runFrom cfg
                                      (steps + 1)).tape.length <= 13 := by
                                  rw [runFrom_succ_start, ← hStep]
                                  exact hBound
                                rw [hRunRename] at hBoundFull
                                simpa [TNF.Rename.config] using hBoundFull

/-! ## Root target/direction reduction -/

def verifyRoot (roots : GoAction -> Certificate) : Bool :=
  haltWritesSafe (initial 4) &&
    TNF.rootActions.all fun action =>
      verify 106 (TNF.grow 1 action)
        (PTable.empty.set (0 : Fin 4) false action)
        (stepGo (initial 4) action) (roots action)

theorem score_le_of_root_action {certificate : Certificate}
    {machine : Machine 4} {action : GoAction} {score : Nat}
    (hBranch : verify 106 (TNF.grow 1 action)
      (PTable.empty.set (0 : Fin 4) false action)
      (stepGo (initial 4) action) certificate = true)
    (hAction : action.toAction = machine.transition (0 : Fin 4) false)
    (hHalts : machine.HaltsWithScore score) : score <= 13 := by
  rcases hHalts with ⟨steps, hHalted, hScore⟩
  cases steps with
  | zero => simp [Machine.run, initial, startState] at hHalted
  | succ steps =>
      have hInv : TNF.PrefixInvariant (TNF.grow 1 action)
          (PTable.empty.set (0 : Fin 4) false action)
          (stepGo (initial 4) action) :=
        TNF.rootInvariant.step_fresh TNF.initial_state_A
      have hAgree :
          (PTable.empty.set (0 : Fin 4) false action).Agrees machine :=
        PTable.set_agrees (PTable.empty_agrees machine) hAction
      have hStep := stepGo_eq_step machine (initial 4) (0 : Fin 4)
        action TNF.initial_state_A hAction
      have hReach : Reachable machine (stepGo (initial 4) action) := by
        refine ⟨1, ?_⟩
        simpa [Machine.run] using hStep
      have hRun : machine.run (steps + 1) =
          machine.runFrom (stepGo (initial 4) action) steps := by
        rw [show steps + 1 = 1 + steps by omega,
          Machine.run_add_eq_runFrom]
        simp only [Machine.run]
        rw [← hStep]
      rw [hRun] at hHalted hScore
      have hBound := verify_sound 106 (TNF.grow 1 action)
        (PTable.empty.set (0 : Fin 4) false action)
        (stepGo (initial 4) action) certificate machine hBranch hInv hAgree
        hReach steps hHalted
      exact hScore ▸ hBound

/-- A verified guided root certificate proves the score upper bound for every
four-state machine, using the same state-canonicalization and reflection
argument as `TNF.upperBound_of_checkRoot`. -/
theorem upperBound_of_verifyRoot {roots : GoAction -> Certificate}
    (hCheck : verifyRoot roots = true) {score : Nat} :
    AttainableScore 4 score -> score <= 13 := by
  rintro ⟨machine, hHalts⟩
  have hParts := Bool.and_eq_true_iff.mp hCheck
  cases hTransition : machine.transition (0 : Fin 4) false with
  | mk write move next =>
      cases next with
      | none =>
          exact TNF.score_le_of_root_halt hParts.1 hTransition hHalts
      | some next =>
          rcases TNF.canonicalize_root_target hTransition hHalts with
            ⟨canonical, action, hCanonicalHalts, hAction, hNext⟩
          rcases TNF.orient_root hCanonicalHalts hAction hNext with
            ⟨oriented, orientedAction, hOrientedHalts,
              hOrientedAction, hOrientedNext, hOrientedMove⟩
          have hMember : orientedAction ∈ TNF.rootActions :=
            TNF.mem_rootActions orientedAction hOrientedNext hOrientedMove
          have hBranch : verify 106 (TNF.grow 1 orientedAction)
              (PTable.empty.set (0 : Fin 4) false orientedAction)
              (stepGo (initial 4) orientedAction)
              (roots orientedAction) = true :=
            (List.all_eq_true.mp hParts.2) orientedAction hMember
          exact score_le_of_root_action hBranch hOrientedAction hOrientedHalts

end Guided
end BB4
end BusyBeaver
end SetTheory
