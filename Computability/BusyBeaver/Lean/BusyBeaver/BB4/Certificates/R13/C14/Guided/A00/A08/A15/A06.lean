import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A00
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A01
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A02
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A03
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A04
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A05
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A06
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A07
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A08
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A09
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A10
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A11
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A12
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A13
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A14
import BusyBeaver.BB4.Certificates.R13.C14.Guided.A00.A08.A15.A06.A15

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def certificate_a00_a08_a15_a06 : Guided.Certificate :=
  Guided.Certificate.branch16
    certificate_a00_a08_a15_a06_a00
    certificate_a00_a08_a15_a06_a01
    certificate_a00_a08_a15_a06_a02
    certificate_a00_a08_a15_a06_a03
    certificate_a00_a08_a15_a06_a04
    certificate_a00_a08_a15_a06_a05
    certificate_a00_a08_a15_a06_a06
    certificate_a00_a08_a15_a06_a07
    certificate_a00_a08_a15_a06_a08
    certificate_a00_a08_a15_a06_a09
    certificate_a00_a08_a15_a06_a10
    certificate_a00_a08_a15_a06_a11
    certificate_a00_a08_a15_a06_a12
    certificate_a00_a08_a15_a06_a13
    certificate_a00_a08_a15_a06_a14
    certificate_a00_a08_a15_a06_a15

theorem verified_a00_a08_a15_a06 :
    pathCheck [a00, a08, a15, a06] certificate_a00_a08_a15_a06 = true := by
  have hAll :
      (TNF.canonicalActions (after [a00, a08, a15, a06]).used).all
        (fun action =>
          ((after [a00, a08, a15, a06]).assign action).check
            (Guided.Certificate.children16
    certificate_a00_a08_a15_a06_a00
    certificate_a00_a08_a15_a06_a01
    certificate_a00_a08_a15_a06_a02
    certificate_a00_a08_a15_a06_a03
    certificate_a00_a08_a15_a06_a04
    certificate_a00_a08_a15_a06_a05
    certificate_a00_a08_a15_a06_a06
    certificate_a00_a08_a15_a06_a07
    certificate_a00_a08_a15_a06_a08
    certificate_a00_a08_a15_a06_a09
    certificate_a00_a08_a15_a06_a10
    certificate_a00_a08_a15_a06_a11
    certificate_a00_a08_a15_a06_a12
    certificate_a00_a08_a15_a06_a13
    certificate_a00_a08_a15_a06_a14
    certificate_a00_a08_a15_a06_a15 action)) = true := by
    have h00 :
        ((after [a00, a08, a15, a06]).assign a00).check
          certificate_a00_a08_a15_a06_a00 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a00
    have h01 :
        ((after [a00, a08, a15, a06]).assign a01).check
          certificate_a00_a08_a15_a06_a01 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a01
    have h02 :
        ((after [a00, a08, a15, a06]).assign a02).check
          certificate_a00_a08_a15_a06_a02 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a02
    have h03 :
        ((after [a00, a08, a15, a06]).assign a03).check
          certificate_a00_a08_a15_a06_a03 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a03
    have h04 :
        ((after [a00, a08, a15, a06]).assign a04).check
          certificate_a00_a08_a15_a06_a04 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a04
    have h05 :
        ((after [a00, a08, a15, a06]).assign a05).check
          certificate_a00_a08_a15_a06_a05 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a05
    have h06 :
        ((after [a00, a08, a15, a06]).assign a06).check
          certificate_a00_a08_a15_a06_a06 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a06
    have h07 :
        ((after [a00, a08, a15, a06]).assign a07).check
          certificate_a00_a08_a15_a06_a07 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a07
    have h08 :
        ((after [a00, a08, a15, a06]).assign a08).check
          certificate_a00_a08_a15_a06_a08 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a08
    have h09 :
        ((after [a00, a08, a15, a06]).assign a09).check
          certificate_a00_a08_a15_a06_a09 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a09
    have h10 :
        ((after [a00, a08, a15, a06]).assign a10).check
          certificate_a00_a08_a15_a06_a10 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a10
    have h11 :
        ((after [a00, a08, a15, a06]).assign a11).check
          certificate_a00_a08_a15_a06_a11 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a11
    have h12 :
        ((after [a00, a08, a15, a06]).assign a12).check
          certificate_a00_a08_a15_a06_a12 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a12
    have h13 :
        ((after [a00, a08, a15, a06]).assign a13).check
          certificate_a00_a08_a15_a06_a13 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a13
    have h14 :
        ((after [a00, a08, a15, a06]).assign a14).check
          certificate_a00_a08_a15_a06_a14 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a14
    have h15 :
        ((after [a00, a08, a15, a06]).assign a15).check
          certificate_a00_a08_a15_a06_a15 = true := by
      rw [assign_check_eq_pathAppend]
      exact verified_a00_a08_a15_a06_a15
    rw [show (after [a00, a08, a15, a06]).used = 4 by decide,
      Certificates.canonicalActions_four_eq]
    exact all_children16
      (fun action certificate =>
        ((after [a00, a08, a15, a06]).assign action).check certificate)
      certificate_a00_a08_a15_a06_a00
      certificate_a00_a08_a15_a06_a01
      certificate_a00_a08_a15_a06_a02
      certificate_a00_a08_a15_a06_a03
      certificate_a00_a08_a15_a06_a04
      certificate_a00_a08_a15_a06_a05
      certificate_a00_a08_a15_a06_a06
      certificate_a00_a08_a15_a06_a07
      certificate_a00_a08_a15_a06_a08
      certificate_a00_a08_a15_a06_a09
      certificate_a00_a08_a15_a06_a10
      certificate_a00_a08_a15_a06_a11
      certificate_a00_a08_a15_a06_a12
      certificate_a00_a08_a15_a06_a13
      certificate_a00_a08_a15_a06_a14
      certificate_a00_a08_a15_a06_a15
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
    (haltWritesSafe (after [a00, a08, a15, a06]).cfg &&
      (TNF.canonicalActions (after [a00, a08, a15, a06]).used).all
        (fun action =>
          ((after [a00, a08, a15, a06]).assign action).check
            (Guided.Certificate.children16
    certificate_a00_a08_a15_a06_a00
    certificate_a00_a08_a15_a06_a01
    certificate_a00_a08_a15_a06_a02
    certificate_a00_a08_a15_a06_a03
    certificate_a00_a08_a15_a06_a04
    certificate_a00_a08_a15_a06_a05
    certificate_a00_a08_a15_a06_a06
    certificate_a00_a08_a15_a06_a07
    certificate_a00_a08_a15_a06_a08
    certificate_a00_a08_a15_a06_a09
    certificate_a00_a08_a15_a06_a10
    certificate_a00_a08_a15_a06_a11
    certificate_a00_a08_a15_a06_a12
    certificate_a00_a08_a15_a06_a13
    certificate_a00_a08_a15_a06_a14
    certificate_a00_a08_a15_a06_a15 action))) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
