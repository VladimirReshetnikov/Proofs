import BusyBeaver.BB4.Certificates.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

/-- Replay only already-assigned transitions, failing if the run halts or
reaches another fresh table slot before the requested number of steps. -/
def runAssigned? : Nat -> PTable -> Config 4 -> Option (Config 4)
  | 0, _table, cfg => some cfg
  | steps + 1, table, cfg =>
      match cfg.state with
      | none => none
      | some state =>
          let bit := Tape.read cfg.tape cfg.head
          match table state bit with
          | none => none
          | some action => runAssigned? steps table (stepGo cfg action)

theorem checkFrom_eq_zero_of_runAssigned
    (leafFn : PTable -> Config 4 -> Bool) (used : Nat) (table : PTable) :
    forall steps cfg target,
      runAssigned? steps table cfg = some target ->
      TNF.checkFrom leafFn steps used table cfg =
        TNF.checkFrom leafFn 0 used table target := by
  intro steps
  induction steps with
  | zero =>
      intro cfg target hRun
      have hEq : cfg = target := by
        simpa [runAssigned?] using Option.some.inj hRun
      subst target
      rfl
  | succ steps ih =>
      intro cfg target hRun
      cases hState : cfg.state with
      | none =>
          simp [runAssigned?, hState] at hRun
      | some state =>
          let bit := Tape.read cfg.tape cfg.head
          cases hLookup : table state bit with
          | none =>
              simp [runAssigned?, hState, bit, hLookup] at hRun
          | some action =>
              have hTail :
                  runAssigned? steps table (stepGo cfg action) = some target := by
                simpa [runAssigned?, hState, bit, hLookup] using hRun
              simpa [TNF.checkFrom, hState, bit, hLookup] using
                ih (stepGo cfg action) target hTail

end SetTheory.BusyBeaver.BB4.Certificates
