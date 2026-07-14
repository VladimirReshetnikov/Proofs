import BusyBeaver.BB4.Certificates.R13.C14.A15.A00
import BusyBeaver.BB4.Certificates.R13.C14.A15.A01
import BusyBeaver.BB4.Certificates.R13.C14.A15.A02
import BusyBeaver.BB4.Certificates.R13.C14.A15.A03
import BusyBeaver.BB4.Certificates.R13.C14.A15.A04
import BusyBeaver.BB4.Certificates.R13.C14.A15.A05
import BusyBeaver.BB4.Certificates.R13.C14.A15.A06
import BusyBeaver.BB4.Certificates.R13.C14.A15.A07
import BusyBeaver.BB4.Certificates.R13.C14.A15.A08
import BusyBeaver.BB4.Certificates.R13.C14.A15.A09
import BusyBeaver.BB4.Certificates.R13.C14.A15.A10
import BusyBeaver.BB4.Certificates.R13.C14.A15.A11
import BusyBeaver.BB4.Certificates.R13.C14.A15.A12
import BusyBeaver.BB4.Certificates.R13.C14.A15.A13
import BusyBeaver.BB4.Certificates.R13.C14.A15.A14
import BusyBeaver.BB4.Certificates.R13.C14.A15.A15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem pathCheck_a15 : CertWork.pathCheck [a15] = true := by
  have hAll :
      (TNF.canonicalActions (CertWork.after [a15]).used).all
        (fun action => ((CertWork.after [a15]).assign action).check) = true := by
    have h00 : ((CertWork.after [a15]).assign a00).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a00
    have h01 : ((CertWork.after [a15]).assign a01).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a01
    have h02 : ((CertWork.after [a15]).assign a02).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a02
    have h03 : ((CertWork.after [a15]).assign a03).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a03
    have h04 : ((CertWork.after [a15]).assign a04).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a04
    have h05 : ((CertWork.after [a15]).assign a05).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a05
    have h06 : ((CertWork.after [a15]).assign a06).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a06
    have h07 : ((CertWork.after [a15]).assign a07).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a07
    have h08 : ((CertWork.after [a15]).assign a08).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a08
    have h09 : ((CertWork.after [a15]).assign a09).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a09
    have h10 : ((CertWork.after [a15]).assign a10).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a10
    have h11 : ((CertWork.after [a15]).assign a11).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a11
    have h12 : ((CertWork.after [a15]).assign a12).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a12
    have h13 : ((CertWork.after [a15]).assign a13).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a13
    have h14 : ((CertWork.after [a15]).assign a14).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a14
    have h15 : ((CertWork.after [a15]).assign a15).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a15_a15
    rw [show (CertWork.after [a15]).used = 4 by decide, canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      h00, h01, h02, h03, h04, h05, h06, h07,
      h08, h09, h10, h11, h12, h13, h14, h15]
    simp
  rw [CertWork.pathCheck_eq_expand]
  change
    (haltWritesSafe (CertWork.after [a15]).cfg &&
      (TNF.canonicalActions (CertWork.after [a15]).used).all
        (fun action => ((CertWork.after [a15]).assign action).check)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
