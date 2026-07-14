import BusyBeaver.BB4.Certificates.R05.A14.A01.A00
import BusyBeaver.BB4.Certificates.R05.A14.A01.A01
import BusyBeaver.BB4.Certificates.R05.A14.A01.A02
import BusyBeaver.BB4.Certificates.R05.A14.A01.A03
import BusyBeaver.BB4.Certificates.R05.A14.A01.A04
import BusyBeaver.BB4.Certificates.R05.A14.A01.A05
import BusyBeaver.BB4.Certificates.R05.A14.A01.A06
import BusyBeaver.BB4.Certificates.R05.A14.A01.A07
import BusyBeaver.BB4.Certificates.R05.A14.A01.A08
import BusyBeaver.BB4.Certificates.R05.A14.A01.A09
import BusyBeaver.BB4.Certificates.R05.A14.A01.A10
import BusyBeaver.BB4.Certificates.R05.A14.A01.A11
import BusyBeaver.BB4.Certificates.R05.A14.A01.A12
import BusyBeaver.BB4.Certificates.R05.A14.A01.A13
import BusyBeaver.BB4.Certificates.R05.A14.A01.A14
import BusyBeaver.BB4.Certificates.R05.A14.A01.A15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem thirdBranch_a05_a14_a01 : thirdBranch_a05_a14 a01 = true := by
  have hAll : (TNF.canonicalActions 3).all
      (fourthBranch_a05_a14 a01) = true := by
    rw [canonicalActions_three_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranch_a05_a14_a01_a00, fourthBranch_a05_a14_a01_a01, fourthBranch_a05_a14_a01_a02, fourthBranch_a05_a14_a01_a03,\n      fourthBranch_a05_a14_a01_a04, fourthBranch_a05_a14_a01_a05, fourthBranch_a05_a14_a01_a06, fourthBranch_a05_a14_a01_a07,\n      fourthBranch_a05_a14_a01_a08, fourthBranch_a05_a14_a01_a09, fourthBranch_a05_a14_a01_a10, fourthBranch_a05_a14_a01_a11,\n      fourthBranch_a05_a14_a01_a12, fourthBranch_a05_a14_a01_a13, fourthBranch_a05_a14_a01_a14, fourthBranch_a05_a14_a01_a15]
    simp
  change
    (haltWritesSafe
        (stepGo (stepGo (stepGo (initial 4) a05) a14) a01) &&
      (TNF.canonicalActions 3).all (fourthBranch_a05_a14 a01)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
