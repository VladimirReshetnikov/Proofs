import BusyBeaver.BB4.Certificates.R05.A02.A11.A00
import BusyBeaver.BB4.Certificates.R05.A02.A11.A01
import BusyBeaver.BB4.Certificates.R05.A02.A11.A02
import BusyBeaver.BB4.Certificates.R05.A02.A11.A03
import BusyBeaver.BB4.Certificates.R05.A02.A11.A04
import BusyBeaver.BB4.Certificates.R05.A02.A11.A05
import BusyBeaver.BB4.Certificates.R05.A02.A11.A06
import BusyBeaver.BB4.Certificates.R05.A02.A11.A07
import BusyBeaver.BB4.Certificates.R05.A02.A11.A08
import BusyBeaver.BB4.Certificates.R05.A02.A11.A09
import BusyBeaver.BB4.Certificates.R05.A02.A11.A10
import BusyBeaver.BB4.Certificates.R05.A02.A11.A11
import BusyBeaver.BB4.Certificates.R05.A02.A11.A12
import BusyBeaver.BB4.Certificates.R05.A02.A11.A13
import BusyBeaver.BB4.Certificates.R05.A02.A11.A14
import BusyBeaver.BB4.Certificates.R05.A02.A11.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem thirdBranchA02_a11 : thirdBranchA02 a11 = true := by
  have hAll : (TNF.canonicalActions 4).all fourthBranchA02A11 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranchA02A11_a00,
      fourthBranchA02A11_a01,
      fourthBranchA02A11_a02,
      fourthBranchA02A11_a03,
      fourthBranchA02A11_a04,
      fourthBranchA02A11_a05,
      fourthBranchA02A11_a06,
      fourthBranchA02A11_a07,
      fourthBranchA02A11_a08,
      fourthBranchA02A11_a09,
      fourthBranchA02A11_a10,
      fourthBranchA02A11_a11,
      fourthBranchA02A11_a12,
      fourthBranchA02A11_a13,
      fourthBranchA02A11_a14,
      fourthBranchA02A11_a15]
    simp
  change
    (haltWritesSafe beforeFourthA02A11 &&
      (TNF.canonicalActions 4).all fourthBranchA02A11) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
