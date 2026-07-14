import BusyBeaver.BB4.Certificates.R13.C14.A00.A01.A03
import BusyBeaver.BB4.Certificates.R13.C14.A00.A01.A07
import BusyBeaver.BB4.Certificates.R13.C14.A00.A01.A09
import BusyBeaver.BB4.Certificates.R13.C14.A00.A01.A10
import BusyBeaver.BB4.Certificates.R13.C14.A00.A01.A11
import BusyBeaver.BB4.Certificates.R13.C14.A00.A01.A15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem pathCheck_a00_a01_a00 : CertWork.pathCheck [a00, a01, a00] = true := by
  decide

theorem pathCheck_a00_a01_a01 : CertWork.pathCheck [a00, a01, a01] = true := by
  decide

theorem pathCheck_a00_a01_a02 : CertWork.pathCheck [a00, a01, a02] = true := by
  decide

theorem pathCheck_a00_a01_a04 : CertWork.pathCheck [a00, a01, a04] = true := by
  decide

theorem pathCheck_a00_a01_a05 : CertWork.pathCheck [a00, a01, a05] = true := by
  decide

theorem pathCheck_a00_a01_a06 : CertWork.pathCheck [a00, a01, a06] = true := by
  decide

theorem pathCheck_a00_a01_a08 : CertWork.pathCheck [a00, a01, a08] = true := by
  decide

theorem pathCheck_a00_a01_a12 : CertWork.pathCheck [a00, a01, a12] = true := by
  decide

theorem pathCheck_a00_a01_a13 : CertWork.pathCheck [a00, a01, a13] = true := by
  decide

theorem pathCheck_a00_a01_a14 : CertWork.pathCheck [a00, a01, a14] = true := by
  decide

theorem pathCheck_a00_a01 : CertWork.pathCheck [a00, a01] = true := by
  have hAll :
      (TNF.canonicalActions (CertWork.after [a00, a01]).used).all
        (fun action => ((CertWork.after [a00, a01]).assign action).check) = true := by
    have h00 : ((CertWork.after [a00, a01]).assign a00).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a00
    have h01 : ((CertWork.after [a00, a01]).assign a01).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a01
    have h02 : ((CertWork.after [a00, a01]).assign a02).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a02
    have h03 : ((CertWork.after [a00, a01]).assign a03).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a03
    have h04 : ((CertWork.after [a00, a01]).assign a04).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a04
    have h05 : ((CertWork.after [a00, a01]).assign a05).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a05
    have h06 : ((CertWork.after [a00, a01]).assign a06).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a06
    have h07 : ((CertWork.after [a00, a01]).assign a07).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a07
    have h08 : ((CertWork.after [a00, a01]).assign a08).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a08
    have h09 : ((CertWork.after [a00, a01]).assign a09).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a09
    have h10 : ((CertWork.after [a00, a01]).assign a10).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a10
    have h11 : ((CertWork.after [a00, a01]).assign a11).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a11
    have h12 : ((CertWork.after [a00, a01]).assign a12).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a12
    have h13 : ((CertWork.after [a00, a01]).assign a13).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a13
    have h14 : ((CertWork.after [a00, a01]).assign a14).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a14
    have h15 : ((CertWork.after [a00, a01]).assign a15).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_a00_a01_a15
    rw [show (CertWork.after [a00, a01]).used = 3 by decide, canonicalActions_three_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      h00, h01, h02, h03, h04, h05, h06, h07,
      h08, h09, h10, h11, h12, h13, h14, h15]
    simp
  rw [CertWork.pathCheck_eq_expand]
  change
    (haltWritesSafe (CertWork.after [a00, a01]).cfg &&
      (TNF.canonicalActions (CertWork.after [a00, a01]).used).all
        (fun action => ((CertWork.after [a00, a01]).assign action).check)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
