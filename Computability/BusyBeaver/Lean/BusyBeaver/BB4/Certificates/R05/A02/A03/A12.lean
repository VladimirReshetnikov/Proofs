import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A00
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A01
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A02
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A03
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A04
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A05
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A06
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A07
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A09
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A11
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A12
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A13
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A14
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem fourthBranchA02A03_a12 : fourthBranchA02A03 a12 = true := by
  have hAll : (TNF.canonicalActions 4).all fifthBranchA02A03A12 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fifthBranchA02A03A12_a00,
      fifthBranchA02A03A12_a01,
      fifthBranchA02A03A12_a02,
      fifthBranchA02A03A12_a03,
      fifthBranchA02A03A12_a04,
      fifthBranchA02A03A12_a05,
      fifthBranchA02A03A12_a06,
      fifthBranchA02A03A12_a07,
      fifthBranchA02A03A12_a08,
      fifthBranchA02A03A12_a09,
      fifthBranchA02A03A12_a10,
      fifthBranchA02A03A12_a11,
      fifthBranchA02A03A12_a12,
      fifthBranchA02A03A12_a13,
      fifthBranchA02A03A12_a14,
      fifthBranchA02A03A12_a15]
    simp
  change
    (haltWritesSafe beforeFifthA02A03A12 &&
      (TNF.canonicalActions 4).all fifthBranchA02A03A12) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
