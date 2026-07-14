import BusyBeaver.BB4.Certificates.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

/-- The fresh `C0` transition reached after the `A0=a05, B0=a14` prefix. -/
def thirdBranch_a05_a14 (third : GoAction) : Bool :=
  TNF.checkFrom leaf 104 (TNF.grow 3 third)
    (((PTable.empty.set (0 : Fin 4) false a05).set a05.next false a14).set
      a14.next false third)
    (stepGo (stepGo (stepGo (initial 4) a05) a14) third)

/-- The next transition is fresh immediately for each third action that needs
another shard.  Its scanned bit is computed from the concrete prefix so this
single definition covers both the marked return cell and the blank frontier. -/
def fourthBranch_a05_a14 (third fourth : GoAction) : Bool :=
  let table :=
    ((PTable.empty.set (0 : Fin 4) false a05).set a05.next false a14).set
      a14.next false third
  let cfg := stepGo (stepGo (stepGo (initial 4) a05) a14) third
  let bit := Tape.read cfg.tape cfg.head
  TNF.checkFrom leaf 103 (TNF.grow (TNF.grow 3 third) fourth)
    (table.set third.next bit fourth) (stepGo cfg fourth)

/-! A normalized path interface for selecting deeper proof cuts without
expanding every intermediate fresh node into its own source module. -/

namespace R05A14

structure CertWork where
  fuel : Nat
  used : Nat
  table : PTable
  cfg : Config 4

namespace CertWork

def check (work : CertWork) : Bool :=
  TNF.checkFrom leaf work.fuel work.used work.table work.cfg

def normalizeFrom : Nat -> Nat -> PTable -> Config 4 -> CertWork
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

def normalize (work : CertWork) : CertWork :=
  normalizeFrom work.fuel work.used work.table work.cfg

def assign (work : CertWork) (action : GoAction) : CertWork :=
  match work.fuel, work.cfg.state with
  | fuel + 1, some state =>
      let bit := Tape.read work.cfg.tape work.cfg.head
      ⟨fuel, TNF.grow work.used action,
        work.table.set state bit action, stepGo work.cfg action⟩
  | _, _ => work

def choose (work : CertWork) (action : GoAction) : CertWork :=
  (work.assign action).normalize

def start : CertWork :=
  ⟨105, TNF.grow (TNF.grow 1 a05) a14,
    (PTable.empty.set (0 : Fin 4) false a05).set a05.next false a14,
    stepGo (stepGo (initial 4) a05) a14⟩

def after (choices : List GoAction) : CertWork :=
  choices.foldl choose start

def pathCheck (choices : List GoAction) : Bool :=
  (after choices).check

theorem check_normalizeFrom : forall fuel used table cfg,
    check ⟨fuel, used, table, cfg⟩ =
      check (normalizeFrom fuel used table cfg) := by
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
              simpa [check, normalizeFrom, TNF.checkFrom, hState, bit,
                hLookup] using ih used table (stepGo cfg action)

theorem check_normalize (work : CertWork) :
    work.check = work.normalize.check := by
  cases work
  exact check_normalizeFrom _ _ _ _

theorem check_assign_eq_choose (work : CertWork) (action : GoAction) :
    (work.assign action).check = (work.choose action).check :=
  check_normalize (work.assign action)

theorem assign_check_eq_pathAppend (choices : List GoAction)
    (action : GoAction) :
    ((after choices).assign action).check =
      pathCheck (choices ++ [action]) := by
  rw [check_assign_eq_choose]
  simp [pathCheck, after, List.foldl_append]

def expand (work : CertWork) : Bool :=
  match work.fuel, work.cfg.state with
  | _fuel + 1, some state =>
      let bit := Tape.read work.cfg.tape work.cfg.head
      match work.table state bit with
      | none =>
          haltWritesSafe work.cfg &&
            (TNF.canonicalActions work.used).all fun action =>
              (work.assign action).check
      | some _ => work.check
  | _, _ => work.check

theorem check_eq_expand (work : CertWork) : work.check = work.expand := by
  cases work with
  | mk fuel used table cfg =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases hState : cfg.state with
          | none => simp [expand, hState]
          | some state =>
              let bit := Tape.read cfg.tape cfg.head
              cases hLookup : table state bit with
              | none =>
                  simp [check, expand, assign, TNF.checkFrom, hState, bit,
                    hLookup]
              | some action => simp [expand, hState, bit, hLookup]

theorem pathCheck_eq_expand (choices : List GoAction) :
    pathCheck choices = (after choices).expand :=
  check_eq_expand (after choices)

theorem thirdBranch_eq_pathCheck (third : GoAction) :
    thirdBranch_a05_a14 third = pathCheck [third] := by
  change (start.assign third).check = (start.choose third).check
  exact check_assign_eq_choose start third

end CertWork
end R05A14

end SetTheory.BusyBeaver.BB4.Certificates
