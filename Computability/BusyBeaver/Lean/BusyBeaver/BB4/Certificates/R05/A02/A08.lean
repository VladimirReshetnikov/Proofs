import BusyBeaver.BB4.Certificates.R05.A02.A08.A00
import BusyBeaver.BB4.Certificates.R05.A02.A08.A01
import BusyBeaver.BB4.Certificates.R05.A02.A08.A02
import BusyBeaver.BB4.Certificates.R05.A02.A08.A03
import BusyBeaver.BB4.Certificates.R05.A02.A08.A04
import BusyBeaver.BB4.Certificates.R05.A02.A08.A05
import BusyBeaver.BB4.Certificates.R05.A02.A08.A06
import BusyBeaver.BB4.Certificates.R05.A02.A08.A07
import BusyBeaver.BB4.Certificates.R05.A02.A08.A08
import BusyBeaver.BB4.Certificates.R05.A02.A08.A09
import BusyBeaver.BB4.Certificates.R05.A02.A08.A10
import BusyBeaver.BB4.Certificates.R05.A02.A08.A11
import BusyBeaver.BB4.Certificates.R05.A02.A08.A12
import BusyBeaver.BB4.Certificates.R05.A02.A08.A13
import BusyBeaver.BB4.Certificates.R05.A02.A08.A14
import BusyBeaver.BB4.Certificates.R05.A02.A08.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem thirdBranchA02_a08 : thirdBranchA02 a08 = true := by
  have hAll : (TNF.canonicalActions 3).all fourthBranchA02A08 = true := by
    rw [canonicalActions_three_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranchA02A08_a00,
      fourthBranchA02A08_a01,
      fourthBranchA02A08_a02,
      fourthBranchA02A08_a03,
      fourthBranchA02A08_a04,
      fourthBranchA02A08_a05,
      fourthBranchA02A08_a06,
      fourthBranchA02A08_a07,
      fourthBranchA02A08_a08,
      fourthBranchA02A08_a09,
      fourthBranchA02A08_a10,
      fourthBranchA02A08_a11,
      fourthBranchA02A08_a12,
      fourthBranchA02A08_a13,
      fourthBranchA02A08_a14,
      fourthBranchA02A08_a15]
    simp
  change
    (haltWritesSafe beforeFourthA02A08 &&
      (TNF.canonicalActions 3).all fourthBranchA02A08) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
