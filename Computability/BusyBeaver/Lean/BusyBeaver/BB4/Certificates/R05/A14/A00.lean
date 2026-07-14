import BusyBeaver.BB4.Certificates.R05.A14.A00.A00
import BusyBeaver.BB4.Certificates.R05.A14.A00.A01
import BusyBeaver.BB4.Certificates.R05.A14.A00.A02
import BusyBeaver.BB4.Certificates.R05.A14.A00.A03
import BusyBeaver.BB4.Certificates.R05.A14.A00.A04
import BusyBeaver.BB4.Certificates.R05.A14.A00.A05
import BusyBeaver.BB4.Certificates.R05.A14.A00.A06
import BusyBeaver.BB4.Certificates.R05.A14.A00.A07
import BusyBeaver.BB4.Certificates.R05.A14.A00.A08
import BusyBeaver.BB4.Certificates.R05.A14.A00.A09
import BusyBeaver.BB4.Certificates.R05.A14.A00.A10
import BusyBeaver.BB4.Certificates.R05.A14.A00.A11
import BusyBeaver.BB4.Certificates.R05.A14.A00.A12
import BusyBeaver.BB4.Certificates.R05.A14.A00.A13
import BusyBeaver.BB4.Certificates.R05.A14.A00.A14
import BusyBeaver.BB4.Certificates.R05.A14.A00.A15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem thirdBranch_a05_a14_a00 : thirdBranch_a05_a14 a00 = true := by
  have hAll : (TNF.canonicalActions 3).all
      (fourthBranch_a05_a14 a00) = true := by
    rw [canonicalActions_three_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranch_a05_a14_a00_a00, fourthBranch_a05_a14_a00_a01, fourthBranch_a05_a14_a00_a02, fourthBranch_a05_a14_a00_a03,\n      fourthBranch_a05_a14_a00_a04, fourthBranch_a05_a14_a00_a05, fourthBranch_a05_a14_a00_a06, fourthBranch_a05_a14_a00_a07,\n      fourthBranch_a05_a14_a00_a08, fourthBranch_a05_a14_a00_a09, fourthBranch_a05_a14_a00_a10, fourthBranch_a05_a14_a00_a11,\n      fourthBranch_a05_a14_a00_a12, fourthBranch_a05_a14_a00_a13, fourthBranch_a05_a14_a00_a14, fourthBranch_a05_a14_a00_a15]
    simp
  change
    (haltWritesSafe
        (stepGo (stepGo (stepGo (initial 4) a05) a14) a00) &&
      (TNF.canonicalActions 3).all (fourthBranch_a05_a14 a00)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
