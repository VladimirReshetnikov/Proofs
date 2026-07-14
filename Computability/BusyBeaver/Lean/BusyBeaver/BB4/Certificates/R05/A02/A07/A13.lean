import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A00
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A01
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A02
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A03
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A04
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A05
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A06
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A07
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A08
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A09
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A11
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A12
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A13
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A14
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem fourthBranchA02A07_a13 : fourthBranchA02A07 a13 = true := by
  have hAll : (TNF.canonicalActions 4).all fifthBranchA02A07A13 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fifthBranchA02A07A13_a00,
      fifthBranchA02A07A13_a01,
      fifthBranchA02A07A13_a02,
      fifthBranchA02A07A13_a03,
      fifthBranchA02A07A13_a04,
      fifthBranchA02A07A13_a05,
      fifthBranchA02A07A13_a06,
      fifthBranchA02A07A13_a07,
      fifthBranchA02A07A13_a08,
      fifthBranchA02A07A13_a09,
      fifthBranchA02A07A13_a10,
      fifthBranchA02A07A13_a11,
      fifthBranchA02A07A13_a12,
      fifthBranchA02A07A13_a13,
      fifthBranchA02A07A13_a14,
      fifthBranchA02A07A13_a15]
    simp
  change
    (haltWritesSafe beforeFifthA02A07A13 &&
      (TNF.canonicalActions 4).all fifthBranchA02A07A13) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
