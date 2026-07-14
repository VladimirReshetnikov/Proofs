import BusyBeaver.BB4.Certificates.R05.A02.A00
import BusyBeaver.BB4.Certificates.R05.A02.A01
import BusyBeaver.BB4.Certificates.R05.A02.A02
import BusyBeaver.BB4.Certificates.R05.A02.A03
import BusyBeaver.BB4.Certificates.R05.A02.A04
import BusyBeaver.BB4.Certificates.R05.A02.A05
import BusyBeaver.BB4.Certificates.R05.A02.A06
import BusyBeaver.BB4.Certificates.R05.A02.A07
import BusyBeaver.BB4.Certificates.R05.A02.A08
import BusyBeaver.BB4.Certificates.R05.A02.A09
import BusyBeaver.BB4.Certificates.R05.A02.A10
import BusyBeaver.BB4.Certificates.R05.A02.A11
import BusyBeaver.BB4.Certificates.R05.A02.A12
import BusyBeaver.BB4.Certificates.R05.A02.A13
import BusyBeaver.BB4.Certificates.R05.A02.A14
import BusyBeaver.BB4.Certificates.R05.A02.A15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem secondBranch_a05_a02 : secondBranch a05 a02 = true := by
  have hAll : (TNF.canonicalActions 3).all thirdBranchA02 = true := by
    rw [canonicalActions_three_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      thirdBranchA02_a00, thirdBranchA02_a01, thirdBranchA02_a02,
      thirdBranchA02_a03, thirdBranchA02_a04, thirdBranchA02_a05,
      thirdBranchA02_a06, thirdBranchA02_a07, thirdBranchA02_a08,
      thirdBranchA02_a09, thirdBranchA02_a10, thirdBranchA02_a11,
      thirdBranchA02_a12, thirdBranchA02_a13, thirdBranchA02_a14,
      thirdBranchA02_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 4) a05) a02) &&
      (TNF.canonicalActions 3).all thirdBranchA02) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
