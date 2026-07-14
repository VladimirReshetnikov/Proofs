import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A00
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A01
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A02
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A03
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A04
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A05
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A06
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A07
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A08
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A09
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A10
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A11
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A12
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A13
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A14
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A11.A15.A02.A15

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def certificate_a11_a15_a02 : Guided.Certificate :=
  Guided.Certificate.branch16
    certificate_a11_a15_a02_a00
    certificate_a11_a15_a02_a01
    certificate_a11_a15_a02_a02
    certificate_a11_a15_a02_a03
    certificate_a11_a15_a02_a04
    certificate_a11_a15_a02_a05
    certificate_a11_a15_a02_a06
    certificate_a11_a15_a02_a07
    certificate_a11_a15_a02_a08
    certificate_a11_a15_a02_a09
    certificate_a11_a15_a02_a10
    certificate_a11_a15_a02_a11
    certificate_a11_a15_a02_a12
    certificate_a11_a15_a02_a13
    certificate_a11_a15_a02_a14
    certificate_a11_a15_a02_a15

theorem verified_a11_a15_a02 :
    pathCheck [a11, a15, a02] certificate_a11_a15_a02 = true := by
  have hAll :
      (TNF.canonicalActions (after [a11, a15, a02]).used).all
        (fun action =>
          ((after [a11, a15, a02]).assign action).check
            (Guided.Certificate.children16
    certificate_a11_a15_a02_a00
    certificate_a11_a15_a02_a01
    certificate_a11_a15_a02_a02
    certificate_a11_a15_a02_a03
    certificate_a11_a15_a02_a04
    certificate_a11_a15_a02_a05
    certificate_a11_a15_a02_a06
    certificate_a11_a15_a02_a07
    certificate_a11_a15_a02_a08
    certificate_a11_a15_a02_a09
    certificate_a11_a15_a02_a10
    certificate_a11_a15_a02_a11
    certificate_a11_a15_a02_a12
    certificate_a11_a15_a02_a13
    certificate_a11_a15_a02_a14
    certificate_a11_a15_a02_a15 action)) = true := by
    have h00 :
        ((after [a11, a15, a02]).assign a00).check
          certificate_a11_a15_a02_a00 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a00
    have h01 :
        ((after [a11, a15, a02]).assign a01).check
          certificate_a11_a15_a02_a01 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a01
    have h02 :
        ((after [a11, a15, a02]).assign a02).check
          certificate_a11_a15_a02_a02 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a02
    have h03 :
        ((after [a11, a15, a02]).assign a03).check
          certificate_a11_a15_a02_a03 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a03
    have h04 :
        ((after [a11, a15, a02]).assign a04).check
          certificate_a11_a15_a02_a04 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a04
    have h05 :
        ((after [a11, a15, a02]).assign a05).check
          certificate_a11_a15_a02_a05 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a05
    have h06 :
        ((after [a11, a15, a02]).assign a06).check
          certificate_a11_a15_a02_a06 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a06
    have h07 :
        ((after [a11, a15, a02]).assign a07).check
          certificate_a11_a15_a02_a07 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a07
    have h08 :
        ((after [a11, a15, a02]).assign a08).check
          certificate_a11_a15_a02_a08 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a08
    have h09 :
        ((after [a11, a15, a02]).assign a09).check
          certificate_a11_a15_a02_a09 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a09
    have h10 :
        ((after [a11, a15, a02]).assign a10).check
          certificate_a11_a15_a02_a10 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a10
    have h11 :
        ((after [a11, a15, a02]).assign a11).check
          certificate_a11_a15_a02_a11 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a11
    have h12 :
        ((after [a11, a15, a02]).assign a12).check
          certificate_a11_a15_a02_a12 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a12
    have h13 :
        ((after [a11, a15, a02]).assign a13).check
          certificate_a11_a15_a02_a13 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a13
    have h14 :
        ((after [a11, a15, a02]).assign a14).check
          certificate_a11_a15_a02_a14 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a14
    have h15 :
        ((after [a11, a15, a02]).assign a15).check
          certificate_a11_a15_a02_a15 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a11_a15_a02_a15
    rw [show (after [a11, a15, a02]).used = 4 by decide,
      Certificates.canonicalActions_four_eq]
    exact all_children16
      (fun action certificate =>
        ((after [a11, a15, a02]).assign action).check certificate)
      certificate_a11_a15_a02_a00
      certificate_a11_a15_a02_a01
      certificate_a11_a15_a02_a02
      certificate_a11_a15_a02_a03
      certificate_a11_a15_a02_a04
      certificate_a11_a15_a02_a05
      certificate_a11_a15_a02_a06
      certificate_a11_a15_a02_a07
      certificate_a11_a15_a02_a08
      certificate_a11_a15_a02_a09
      certificate_a11_a15_a02_a10
      certificate_a11_a15_a02_a11
      certificate_a11_a15_a02_a12
      certificate_a11_a15_a02_a13
      certificate_a11_a15_a02_a14
      certificate_a11_a15_a02_a15
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
    (haltWritesSafe (after [a11, a15, a02]).cfg &&
      (TNF.canonicalActions (after [a11, a15, a02]).used).all
        (fun action =>
          ((after [a11, a15, a02]).assign action).check
            (Guided.Certificate.children16
    certificate_a11_a15_a02_a00
    certificate_a11_a15_a02_a01
    certificate_a11_a15_a02_a02
    certificate_a11_a15_a02_a03
    certificate_a11_a15_a02_a04
    certificate_a11_a15_a02_a05
    certificate_a11_a15_a02_a06
    certificate_a11_a15_a02_a07
    certificate_a11_a15_a02_a08
    certificate_a11_a15_a02_a09
    certificate_a11_a15_a02_a10
    certificate_a11_a15_a02_a11
    certificate_a11_a15_a02_a12
    certificate_a11_a15_a02_a13
    certificate_a11_a15_a02_a14
    certificate_a11_a15_a02_a15 action))) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
