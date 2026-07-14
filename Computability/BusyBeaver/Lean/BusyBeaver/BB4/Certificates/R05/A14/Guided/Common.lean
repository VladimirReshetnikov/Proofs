import BusyBeaver.BB4.Guided
import BusyBeaver.BB4.Certificates.R05.A14.Common

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def ofCertWork (work : Certificates.R05A14.CertWork) : Guided.Work :=
  ⟨work.fuel, work.used, work.table, work.cfg⟩

theorem ofCertWork_normalizeFrom : forall fuel used table cfg,
    ofCertWork
        (Certificates.R05A14.CertWork.normalizeFrom fuel used table cfg) =
      Guided.Work.normalizeFrom fuel used table cfg := by
  intro fuel
  induction fuel with
  | zero =>
      intro used table cfg
      rfl
  | succ fuel ih =>
      intro used table cfg
      cases hState : cfg.state with
      | none => simp [Certificates.R05A14.CertWork.normalizeFrom,
          Guided.Work.normalizeFrom, hState, ofCertWork]
      | some state =>
          let bit := Tape.read cfg.tape cfg.head
          cases hLookup : table state bit with
          | none => simp [Certificates.R05A14.CertWork.normalizeFrom,
              Guided.Work.normalizeFrom, hState, bit, hLookup, ofCertWork]
          | some action =>
              simpa [Certificates.R05A14.CertWork.normalizeFrom,
                Guided.Work.normalizeFrom, hState, bit, hLookup] using
                ih used table (stepGo cfg action)

theorem ofCertWork_assign (work : Certificates.R05A14.CertWork)
    (action : GoAction) :
    ofCertWork (work.assign action) =
      (ofCertWork work).assign action := by
  cases work with
  | mk fuel used table cfg =>
      cases cfg with
      | mk state head tape =>
        cases fuel <;> cases state <;>
        rfl

theorem ofCertWork_normalize (work : Certificates.R05A14.CertWork) :
    ofCertWork work.normalize = (ofCertWork work).normalize := by
  cases work
  exact ofCertWork_normalizeFrom _ _ _ _

theorem ofCertWork_choose (work : Certificates.R05A14.CertWork)
    (action : GoAction) :
    ofCertWork (work.choose action) =
      (ofCertWork work).choose action := by
  rw [Certificates.R05A14.CertWork.choose, Guided.Work.choose,
    ofCertWork_normalize, ofCertWork_assign]

def start : Guided.Work :=
  ofCertWork Certificates.R05A14.CertWork.start

def after (choices : List GoAction) : Guided.Work :=
  ofCertWork (Certificates.R05A14.CertWork.after choices)

def pathCheck (choices : List GoAction) (certificate : Guided.Certificate) :
    Bool :=
  (after choices).check certificate

theorem assign_check_eq_pathAppend (choices : List GoAction)
    (action : GoAction) (certificate : Guided.Certificate) :
    ((after choices).assign action).check certificate =
      pathCheck (choices ++ [action]) certificate := by
  rw [Guided.Work.check_assign_eq_choose]
  unfold after
  rw [← ofCertWork_choose]
  simp [pathCheck, after, Certificates.R05A14.CertWork.after,
    List.foldl_append]

theorem legacy_eq_original (choices : List GoAction) :
    pathCheck choices .legacy =
      Certificates.R05A14.CertWork.pathCheck choices := by
  simp [pathCheck, Guided.Work.check, Guided.verify, after, ofCertWork,
    Certificates.R05A14.CertWork.pathCheck,
    Certificates.R05A14.CertWork.check]

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
