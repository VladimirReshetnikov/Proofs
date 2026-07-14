import BusyBeaver.BB4.Certificates.R05.A02.A13.A00
import BusyBeaver.BB4.Certificates.R05.A02.A13.A01
import BusyBeaver.BB4.Certificates.R05.A02.A13.A02
import BusyBeaver.BB4.Certificates.R05.A02.A13.A03
import BusyBeaver.BB4.Certificates.R05.A02.A13.A04
import BusyBeaver.BB4.Certificates.R05.A02.A13.A05
import BusyBeaver.BB4.Certificates.R05.A02.A13.A06
import BusyBeaver.BB4.Certificates.R05.A02.A13.A07
import BusyBeaver.BB4.Certificates.R05.A02.A13.A08
import BusyBeaver.BB4.Certificates.R05.A02.A13.A09
import BusyBeaver.BB4.Certificates.R05.A02.A13.A10
import BusyBeaver.BB4.Certificates.R05.A02.A13.A11
import BusyBeaver.BB4.Certificates.R05.A02.A13.A12
import BusyBeaver.BB4.Certificates.R05.A02.A13.A13
import BusyBeaver.BB4.Certificates.R05.A02.A13.A14
import BusyBeaver.BB4.Certificates.R05.A02.A13.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem thirdBranchA02_a13 : thirdBranchA02 a13 = true := by
  have hAll : (TNF.canonicalActions 3).all fourthBranchA02A13 = true := by
    rw [canonicalActions_three_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranchA02A13_a00,
      fourthBranchA02A13_a01,
      fourthBranchA02A13_a02,
      fourthBranchA02A13_a03,
      fourthBranchA02A13_a04,
      fourthBranchA02A13_a05,
      fourthBranchA02A13_a06,
      fourthBranchA02A13_a07,
      fourthBranchA02A13_a08,
      fourthBranchA02A13_a09,
      fourthBranchA02A13_a10,
      fourthBranchA02A13_a11,
      fourthBranchA02A13_a12,
      fourthBranchA02A13_a13,
      fourthBranchA02A13_a14,
      fourthBranchA02A13_a15]
    simp
  change
    (haltWritesSafe beforeFourthA02A13 &&
      (TNF.canonicalActions 3).all fourthBranchA02A13) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
