import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A01
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A02
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A03
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A04
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A05
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A06
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A07
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A08
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A09
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A10
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A12
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A13
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A14
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A15

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

/-- Guided certificate for the complete subtree below the fixed root choices
`a13` and `a14`. -/
def certificate_c14 : Guided.Certificate :=
  Guided.Certificate.branch16
    certificate_a00
    certificate_a01
    certificate_a02
    certificate_a03
    certificate_a04
    certificate_a05
    certificate_a06
    certificate_a07
    certificate_a08
    certificate_a09
    certificate_a10
    certificate_a11
    certificate_a12
    certificate_a13
    certificate_a14
    certificate_a15

/-- Kernel-checked acceptance of the complete fixed `a13`/`a14` subtree. -/
theorem verified_c14 :
    pathCheck [] certificate_c14 = true := by
  have h00 :
      ((after []).assign a00).check certificate_a00 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a00
  have h01 :
      ((after []).assign a01).check certificate_a01 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a01
  have h02 :
      ((after []).assign a02).check certificate_a02 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a02
  have h03 :
      ((after []).assign a03).check certificate_a03 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a03
  have h04 :
      ((after []).assign a04).check certificate_a04 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a04
  have h05 :
      ((after []).assign a05).check certificate_a05 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a05
  have h06 :
      ((after []).assign a06).check certificate_a06 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a06
  have h07 :
      ((after []).assign a07).check certificate_a07 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a07
  have h08 :
      ((after []).assign a08).check certificate_a08 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a08
  have h09 :
      ((after []).assign a09).check certificate_a09 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a09
  have h10 :
      ((after []).assign a10).check certificate_a10 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a10
  have h11 :
      ((after []).assign a11).check certificate_a11 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a11
  have h12 :
      ((after []).assign a12).check certificate_a12 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a12
  have h13 :
      ((after []).assign a13).check certificate_a13 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a13
  have h14 :
      ((after []).assign a14).check certificate_a14 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a14
  have h15 :
      ((after []).assign a15).check certificate_a15 = true := by
    rw [assign_check_eq_pathAppend]
    exact verified_a15
  have hAll :
      (TNF.canonicalActions (after []).used).all
        (fun action =>
          ((after []).assign action).check
            (Guided.Certificate.children16
              certificate_a00
              certificate_a01
              certificate_a02
              certificate_a03
              certificate_a04
              certificate_a05
              certificate_a06
              certificate_a07
              certificate_a08
              certificate_a09
              certificate_a10
              certificate_a11
              certificate_a12
              certificate_a13
              certificate_a14
              certificate_a15 action)) = true := by
    rw [show (after []).used = 3 by decide,
      Certificates.canonicalActions_three_eq]
    exact all_children16
      (fun action certificate =>
        ((after []).assign action).check certificate)
      certificate_a00
      certificate_a01
      certificate_a02
      certificate_a03
      certificate_a04
      certificate_a05
      certificate_a06
      certificate_a07
      certificate_a08
      certificate_a09
      certificate_a10
      certificate_a11
      certificate_a12
      certificate_a13
      certificate_a14
      certificate_a15
      h00
      h01
      h02
      h03
      h04
      h05
      h06
      h07
      h08
      h09
      h10
      h11
      h12
      h13
      h14
      h15
  change
    (haltWritesSafe (after []).cfg &&
      (TNF.canonicalActions (after []).used).all
        (fun action =>
          ((after []).assign action).check
            (Guided.Certificate.children16
              certificate_a00
              certificate_a01
              certificate_a02
              certificate_a03
              certificate_a04
              certificate_a05
              certificate_a06
              certificate_a07
              certificate_a08
              certificate_a09
              certificate_a10
              certificate_a11
              certificate_a12
              certificate_a13
              certificate_a14
              certificate_a15 action))) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
