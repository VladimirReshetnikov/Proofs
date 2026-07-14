import BusyBeaver.BB4.Certificates.R05.A02.A15.A00
import BusyBeaver.BB4.Certificates.R05.A02.A15.A01
import BusyBeaver.BB4.Certificates.R05.A02.A15.A02
import BusyBeaver.BB4.Certificates.R05.A02.A15.A03
import BusyBeaver.BB4.Certificates.R05.A02.A15.A04
import BusyBeaver.BB4.Certificates.R05.A02.A15.A05
import BusyBeaver.BB4.Certificates.R05.A02.A15.A06
import BusyBeaver.BB4.Certificates.R05.A02.A15.A07
import BusyBeaver.BB4.Certificates.R05.A02.A15.A08
import BusyBeaver.BB4.Certificates.R05.A02.A15.A09
import BusyBeaver.BB4.Certificates.R05.A02.A15.A10
import BusyBeaver.BB4.Certificates.R05.A02.A15.A11
import BusyBeaver.BB4.Certificates.R05.A02.A15.A12
import BusyBeaver.BB4.Certificates.R05.A02.A15.A13
import BusyBeaver.BB4.Certificates.R05.A02.A15.A14
import BusyBeaver.BB4.Certificates.R05.A02.A15.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem thirdBranchA02_a15 : thirdBranchA02 a15 = true := by
  have hAll : (TNF.canonicalActions 4).all fourthBranchA02A15 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranchA02A15_a00,
      fourthBranchA02A15_a01,
      fourthBranchA02A15_a02,
      fourthBranchA02A15_a03,
      fourthBranchA02A15_a04,
      fourthBranchA02A15_a05,
      fourthBranchA02A15_a06,
      fourthBranchA02A15_a07,
      fourthBranchA02A15_a08,
      fourthBranchA02A15_a09,
      fourthBranchA02A15_a10,
      fourthBranchA02A15_a11,
      fourthBranchA02A15_a12,
      fourthBranchA02A15_a13,
      fourthBranchA02A15_a14,
      fourthBranchA02A15_a15]
    simp
  change
    (haltWritesSafe beforeFourthA02A15 &&
      (TNF.canonicalActions 4).all fourthBranchA02A15) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
