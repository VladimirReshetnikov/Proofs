import BusyBeaver.BB4.Certificates.R05.A14.Guided.A00
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A01
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A02
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A03
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A04
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A05
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A06
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A07
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A08
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A09
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A10
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A12
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A13
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A14
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A15

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

/-- The complete guided certificate below the fixed `A0=a05, B0=a14`
prefix.  Its sixteen children are independently generated and kernel checked. -/
def certificate : Guided.Certificate :=
  Guided.Certificate.branch16
    certificate_a00 certificate_a01 certificate_a02 certificate_a03
    certificate_a04 certificate_a05 certificate_a06 certificate_a07
    certificate_a08 certificate_a09 certificate_a10 certificate_a11
    certificate_a12 certificate_a13 certificate_a14 certificate_a15

private theorem verified_a04_path :
    pathCheck [a04] certificate_a04 = true := by
  simpa [pathCheck, work_a04] using verified_a04

private theorem verified_a05_path :
    pathCheck [a05] certificate_a05 = true := by
  simpa [pathCheck, work_a05] using verified_a05

private theorem verified_a06_path :
    pathCheck [a06] certificate_a06 = true := by
  simpa [pathCheck, work_a06] using verified_a06

private theorem verified_a12_path :
    pathCheck [a12] certificate_a12 = true := by
  simpa [pathCheck, work_a12] using verified_a12

private theorem verified_a13_path :
    pathCheck [a13] certificate_a13 = true := by
  simpa [pathCheck, work_a13] using verified_a13

private theorem verified_a14_path :
    pathCheck [a14] certificate_a14 = true := by
  simpa [pathCheck, work_a14] using verified_a14

theorem verified : pathCheck [] certificate = true := by
  have child (action : GoAction) (childCertificate : Guided.Certificate)
      (h : pathCheck [action] childCertificate = true) :
      ((after []).assign action).check childCertificate = true := by
    rw [assign_check_eq_pathAppend]
    simpa using h
  have h00 := child a00 certificate_a00 verified_a00
  have h01 := child a01 certificate_a01 verified_a01
  have h02 := child a02 certificate_a02 verified_a02
  have h03 := child a03 certificate_a03 verified_a03
  have h04 := child a04 certificate_a04 verified_a04_path
  have h05 := child a05 certificate_a05 verified_a05_path
  have h06 := child a06 certificate_a06 verified_a06_path
  have h07 := child a07 certificate_a07 verified_a07
  have h08 := child a08 certificate_a08 verified_a08
  have h09 := child a09 certificate_a09 verified_a09
  have h10 := child a10 certificate_a10 verified_a10
  have h11 := child a11 certificate_a11 verified_a11
  have h12 := child a12 certificate_a12 verified_a12_path
  have h13 := child a13 certificate_a13 verified_a13_path
  have h14 := child a14 certificate_a14 verified_a14_path
  have h15 := child a15 certificate_a15 verified_a15
  have hAll :
      (TNF.canonicalActions (after []).used).all
        (fun action =>
          ((after []).assign action).check
            (Guided.Certificate.children16
              certificate_a00 certificate_a01 certificate_a02 certificate_a03
              certificate_a04 certificate_a05 certificate_a06 certificate_a07
              certificate_a08 certificate_a09 certificate_a10 certificate_a11
              certificate_a12 certificate_a13 certificate_a14 certificate_a15
              action)) = true := by
    rw [show (after []).used = 3 by decide,
      Certificates.canonicalActions_three_eq]
    simp [h00, h01, h02, h03, h04, h05, h06, h07,
      h08, h09, h10, h11, h12, h13, h14, h15]
  change
    (haltWritesSafe (after []).cfg &&
      (TNF.canonicalActions (after []).used).all
        (fun action =>
          ((after []).assign action).check
            (Guided.Certificate.children16
              certificate_a00 certificate_a01 certificate_a02 certificate_a03
              certificate_a04 certificate_a05 certificate_a06 certificate_a07
              certificate_a08 certificate_a09 certificate_a10 certificate_a11
              certificate_a12 certificate_a13 certificate_a14 certificate_a15
              action))) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
