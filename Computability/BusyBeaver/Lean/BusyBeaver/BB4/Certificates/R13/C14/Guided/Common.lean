import BusyBeaver.BB4.Guided
import BusyBeaver.BB4.Certificates.R13.C14.Common

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

/-- Forget the original Boolean certificate wrapper while preserving its
search state exactly. -/
def ofCertWork (work : Certificates.CertWork) : Guided.Work :=
  ⟨work.fuel, work.used, work.table, work.cfg⟩

theorem ofCertWork_normalizeFrom : forall fuel used table cfg,
    ofCertWork (Certificates.CertWork.normalizeFrom fuel used table cfg) =
      Guided.Work.normalizeFrom fuel used table cfg := by
  intro fuel
  induction fuel with
  | zero =>
      intro used table cfg
      rfl
  | succ fuel ih =>
      intro used table cfg
      cases hState : cfg.state with
      | none => simp [Certificates.CertWork.normalizeFrom,
          Guided.Work.normalizeFrom, hState, ofCertWork]
      | some state =>
          let bit := Tape.read cfg.tape cfg.head
          cases hLookup : table state bit with
          | none => simp [Certificates.CertWork.normalizeFrom,
              Guided.Work.normalizeFrom, hState, bit, hLookup, ofCertWork]
          | some action =>
              simpa [Certificates.CertWork.normalizeFrom,
                Guided.Work.normalizeFrom, hState, bit, hLookup] using
                ih used table (stepGo cfg action)

theorem ofCertWork_assign (work : Certificates.CertWork)
    (action : GoAction) :
    ofCertWork (work.assign action) =
      (ofCertWork work).assign action := by
  cases work with
  | mk fuel used table cfg =>
      cases cfg with
      | mk state head tape =>
        cases fuel <;> cases state <;>
        rfl

theorem ofCertWork_normalize (work : Certificates.CertWork) :
    ofCertWork work.normalize = (ofCertWork work).normalize := by
  cases work
  exact ofCertWork_normalizeFrom _ _ _ _

theorem ofCertWork_choose (work : Certificates.CertWork)
    (action : GoAction) :
    ofCertWork (work.choose action) =
      (ofCertWork work).choose action := by
  rw [Certificates.CertWork.choose, Guided.Work.choose,
    ofCertWork_normalize, ofCertWork_assign]

def start : Guided.Work :=
  ofCertWork Certificates.CertWork.start

def after (choices : List GoAction) : Guided.Work :=
  ofCertWork (Certificates.CertWork.after choices)

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
  simp [pathCheck, after, Certificates.CertWork.after,
    List.foldl_append]

theorem legacy_eq_original (choices : List GoAction) :
    pathCheck choices .legacy = Certificates.CertWork.pathCheck choices := by
  simp [pathCheck, Guided.Work.check, Guided.verify, after, ofCertWork,
    Certificates.CertWork.pathCheck, Certificates.CertWork.check]

/-- Assemble the sixteen pointwise child checks without asking the simplifier
to inspect concrete (and potentially very large) certificate definitions. -/
theorem all_children16
    (check : GoAction → Guided.Certificate → Bool)
    (c00 c01 c02 c03 c04 c05 c06 c07 : Guided.Certificate)
    (c08 c09 c10 c11 c12 c13 c14 c15 : Guided.Certificate)
    (h00 : check a00 c00 = true)
    (h01 : check a01 c01 = true)
    (h02 : check a02 c02 = true)
    (h03 : check a03 c03 = true)
    (h04 : check a04 c04 = true)
    (h05 : check a05 c05 = true)
    (h06 : check a06 c06 = true)
    (h07 : check a07 c07 = true)
    (h08 : check a08 c08 = true)
    (h09 : check a09 c09 = true)
    (h10 : check a10 c10 = true)
    (h11 : check a11 c11 = true)
    (h12 : check a12 c12 = true)
    (h13 : check a13 c13 = true)
    (h14 : check a14 c14 = true)
    (h15 : check a15 c15 = true) :
    [a00, a01, a02, a03, a04, a05, a06, a07,
      a08, a09, a10, a11, a12, a13, a14, a15].all
        (fun action => check action
          (Guided.Certificate.children16
            c00 c01 c02 c03 c04 c05 c06 c07
            c08 c09 c10 c11 c12 c13 c14 c15 action)) = true := by
  simp [h00, h01, h02, h03, h04, h05, h06, h07,
    h08, h09, h10, h11, h12, h13, h14, h15]

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
