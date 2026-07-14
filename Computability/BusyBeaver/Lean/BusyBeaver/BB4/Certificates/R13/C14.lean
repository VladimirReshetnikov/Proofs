import BusyBeaver.BB4.Certificates.R13.C14.A00
import BusyBeaver.BB4.Certificates.R13.C14.A01
import BusyBeaver.BB4.Certificates.R13.C14.A02
import BusyBeaver.BB4.Certificates.R13.C14.A03
import BusyBeaver.BB4.Certificates.R13.C14.A04
import BusyBeaver.BB4.Certificates.R13.C14.A05
import BusyBeaver.BB4.Certificates.R13.C14.A06
import BusyBeaver.BB4.Certificates.R13.C14.A07
import BusyBeaver.BB4.Certificates.R13.C14.A08
import BusyBeaver.BB4.Certificates.R13.C14.A09
import BusyBeaver.BB4.Certificates.R13.C14.A10
import BusyBeaver.BB4.Certificates.R13.C14.A11
import BusyBeaver.BB4.Certificates.R13.C14.A12
import BusyBeaver.BB4.Certificates.R13.C14.A13
import BusyBeaver.BB4.Certificates.R13.C14.A14
import BusyBeaver.BB4.Certificates.R13.C14.A15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem secondBranch_a13_a14 : secondBranch a13 a14 = true := by
  have h00 : thirdBranch_a13_a14 a00 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a00
  have h01 : thirdBranch_a13_a14 a01 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a01
  have h02 : thirdBranch_a13_a14 a02 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a02
  have h03 : thirdBranch_a13_a14 a03 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a03
  have h04 : thirdBranch_a13_a14 a04 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a04
  have h05 : thirdBranch_a13_a14 a05 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a05
  have h06 : thirdBranch_a13_a14 a06 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a06
  have h07 : thirdBranch_a13_a14 a07 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a07
  have h08 : thirdBranch_a13_a14 a08 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a08
  have h09 : thirdBranch_a13_a14 a09 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a09
  have h10 : thirdBranch_a13_a14 a10 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a10
  have h11 : thirdBranch_a13_a14 a11 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a11
  have h12 : thirdBranch_a13_a14 a12 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a12
  have h13 : thirdBranch_a13_a14 a13 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a13
  have h14 : thirdBranch_a13_a14 a14 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a14
  have h15 : thirdBranch_a13_a14 a15 = true := by
    rw [CertWork.thirdBranch_eq_pathCheck]
    exact pathCheck_a15
  have hAll :
      (TNF.canonicalActions 3).all thirdBranch_a13_a14 = true := by
    rw [canonicalActions_three_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      h00, h01, h02, h03, h04, h05, h06, h07,
      h08, h09, h10, h11, h12, h13, h14, h15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 4) a13) a14) &&
      (TNF.canonicalActions 3).all thirdBranch_a13_a14) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
