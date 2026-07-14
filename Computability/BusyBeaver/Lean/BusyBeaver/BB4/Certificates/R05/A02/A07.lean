import BusyBeaver.BB4.Certificates.R05.A02.A07.A00
import BusyBeaver.BB4.Certificates.R05.A02.A07.A01
import BusyBeaver.BB4.Certificates.R05.A02.A07.A02
import BusyBeaver.BB4.Certificates.R05.A02.A07.A03
import BusyBeaver.BB4.Certificates.R05.A02.A07.A04
import BusyBeaver.BB4.Certificates.R05.A02.A07.A05
import BusyBeaver.BB4.Certificates.R05.A02.A07.A06
import BusyBeaver.BB4.Certificates.R05.A02.A07.A07
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08
import BusyBeaver.BB4.Certificates.R05.A02.A07.A09
import BusyBeaver.BB4.Certificates.R05.A02.A07.A10
import BusyBeaver.BB4.Certificates.R05.A02.A07.A11
import BusyBeaver.BB4.Certificates.R05.A02.A07.A12
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13
import BusyBeaver.BB4.Certificates.R05.A02.A07.A14
import BusyBeaver.BB4.Certificates.R05.A02.A07.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem thirdBranchA02_a07 : thirdBranchA02 a07 = true := by
  have hAll : (TNF.canonicalActions 4).all fourthBranchA02A07 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranchA02A07_a00,
      fourthBranchA02A07_a01,
      fourthBranchA02A07_a02,
      fourthBranchA02A07_a03,
      fourthBranchA02A07_a04,
      fourthBranchA02A07_a05,
      fourthBranchA02A07_a06,
      fourthBranchA02A07_a07,
      fourthBranchA02A07_a08,
      fourthBranchA02A07_a09,
      fourthBranchA02A07_a10,
      fourthBranchA02A07_a11,
      fourthBranchA02A07_a12,
      fourthBranchA02A07_a13,
      fourthBranchA02A07_a14,
      fourthBranchA02A07_a15]
    simp
  change
    (haltWritesSafe beforeFourthA02A07 &&
      (TNF.canonicalActions 4).all fourthBranchA02A07) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
