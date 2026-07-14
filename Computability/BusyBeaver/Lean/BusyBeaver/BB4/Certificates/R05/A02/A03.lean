import BusyBeaver.BB4.Certificates.R05.A02.A03.A00
import BusyBeaver.BB4.Certificates.R05.A02.A03.A01
import BusyBeaver.BB4.Certificates.R05.A02.A03.A02
import BusyBeaver.BB4.Certificates.R05.A02.A03.A03
import BusyBeaver.BB4.Certificates.R05.A02.A03.A04
import BusyBeaver.BB4.Certificates.R05.A02.A03.A05
import BusyBeaver.BB4.Certificates.R05.A02.A03.A06
import BusyBeaver.BB4.Certificates.R05.A02.A03.A07
import BusyBeaver.BB4.Certificates.R05.A02.A03.A08
import BusyBeaver.BB4.Certificates.R05.A02.A03.A09
import BusyBeaver.BB4.Certificates.R05.A02.A03.A10
import BusyBeaver.BB4.Certificates.R05.A02.A03.A11
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14
import BusyBeaver.BB4.Certificates.R05.A02.A03.A15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem thirdBranchA02_a03 : thirdBranchA02 a03 = true := by
  have hAll : (TNF.canonicalActions 4).all fourthBranchA02A03 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranchA02A03_a00, fourthBranchA02A03_a01,
      fourthBranchA02A03_a02, fourthBranchA02A03_a03,
      fourthBranchA02A03_a04, fourthBranchA02A03_a05,
      fourthBranchA02A03_a06, fourthBranchA02A03_a07,
      fourthBranchA02A03_a08, fourthBranchA02A03_a09,
      fourthBranchA02A03_a10, fourthBranchA02A03_a11,
      fourthBranchA02A03_a12, fourthBranchA02A03_a13,
      fourthBranchA02A03_a14, fourthBranchA02A03_a15]
    simp
  change
    (haltWritesSafe
        (stepGo (stepGo (stepGo (initial 4) a05) a02) a03) &&
      (TNF.canonicalActions 4).all fourthBranchA02A03) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
