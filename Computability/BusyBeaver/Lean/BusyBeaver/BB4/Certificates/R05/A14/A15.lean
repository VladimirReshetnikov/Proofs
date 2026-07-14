import BusyBeaver.BB4.Certificates.R05.A14.A15.A00
import BusyBeaver.BB4.Certificates.R05.A14.A15.A01
import BusyBeaver.BB4.Certificates.R05.A14.A15.A02
import BusyBeaver.BB4.Certificates.R05.A14.A15.A03
import BusyBeaver.BB4.Certificates.R05.A14.A15.A04
import BusyBeaver.BB4.Certificates.R05.A14.A15.A05
import BusyBeaver.BB4.Certificates.R05.A14.A15.A06
import BusyBeaver.BB4.Certificates.R05.A14.A15.A07
import BusyBeaver.BB4.Certificates.R05.A14.A15.A08
import BusyBeaver.BB4.Certificates.R05.A14.A15.A09
import BusyBeaver.BB4.Certificates.R05.A14.A15.A10
import BusyBeaver.BB4.Certificates.R05.A14.A15.A11
import BusyBeaver.BB4.Certificates.R05.A14.A15.A12
import BusyBeaver.BB4.Certificates.R05.A14.A15.A13
import BusyBeaver.BB4.Certificates.R05.A14.A15.A14
import BusyBeaver.BB4.Certificates.R05.A14.A15.A15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem thirdBranch_a05_a14_a15 : thirdBranch_a05_a14 a15 = true := by
  have hAll : (TNF.canonicalActions 4).all
      (fourthBranch_a05_a14 a15) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranch_a05_a14_a15_a00, fourthBranch_a05_a14_a15_a01, fourthBranch_a05_a14_a15_a02, fourthBranch_a05_a14_a15_a03,\n      fourthBranch_a05_a14_a15_a04, fourthBranch_a05_a14_a15_a05, fourthBranch_a05_a14_a15_a06, fourthBranch_a05_a14_a15_a07,\n      fourthBranch_a05_a14_a15_a08, fourthBranch_a05_a14_a15_a09, fourthBranch_a05_a14_a15_a10, fourthBranch_a05_a14_a15_a11,\n      fourthBranch_a05_a14_a15_a12, fourthBranch_a05_a14_a15_a13, fourthBranch_a05_a14_a15_a14, fourthBranch_a05_a14_a15_a15]
    simp
  change
    (haltWritesSafe
        (stepGo (stepGo (stepGo (initial 4) a05) a14) a15) &&
      (TNF.canonicalActions 4).all (fourthBranch_a05_a14 a15)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
