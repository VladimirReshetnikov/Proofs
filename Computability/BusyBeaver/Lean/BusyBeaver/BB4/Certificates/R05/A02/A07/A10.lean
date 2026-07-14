import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A00
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A01
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A02
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A03
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A04
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A05
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A06
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A07
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A08
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A09
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A10
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A11
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A12
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A13
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A14
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem fourthBranchA02A07_a10 : fourthBranchA02A07 a10 = true := by
  have hAll : (TNF.canonicalActions 4).all fifthBranchA02A07A10 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fifthBranchA02A07A10_a00,
      fifthBranchA02A07A10_a01,
      fifthBranchA02A07A10_a02,
      fifthBranchA02A07A10_a03,
      fifthBranchA02A07A10_a04,
      fifthBranchA02A07A10_a05,
      fifthBranchA02A07A10_a06,
      fifthBranchA02A07A10_a07,
      fifthBranchA02A07A10_a08,
      fifthBranchA02A07A10_a09,
      fifthBranchA02A07A10_a10,
      fifthBranchA02A07A10_a11,
      fifthBranchA02A07A10_a12,
      fifthBranchA02A07A10_a13,
      fifthBranchA02A07A10_a14,
      fifthBranchA02A07A10_a15]
    simp
  change
    (haltWritesSafe beforeFifthA02A07A10 &&
      (TNF.canonicalActions 4).all fifthBranchA02A07A10) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
