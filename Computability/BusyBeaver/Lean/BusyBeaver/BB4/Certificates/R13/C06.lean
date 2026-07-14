import BusyBeaver.BB4.Certificates.R13.C06.C00
import BusyBeaver.BB4.Certificates.R13.C06.C01
import BusyBeaver.BB4.Certificates.R13.C06.C02
import BusyBeaver.BB4.Certificates.R13.C06.C03
import BusyBeaver.BB4.Certificates.R13.C06.C04
import BusyBeaver.BB4.Certificates.R13.C06.C05
import BusyBeaver.BB4.Certificates.R13.C06.C06
import BusyBeaver.BB4.Certificates.R13.C06.C07
import BusyBeaver.BB4.Certificates.R13.C06.C08
import BusyBeaver.BB4.Certificates.R13.C06.C09
import BusyBeaver.BB4.Certificates.R13.C06.C10
import BusyBeaver.BB4.Certificates.R13.C06.C11
import BusyBeaver.BB4.Certificates.R13.C06.C12
import BusyBeaver.BB4.Certificates.R13.C06.C13
import BusyBeaver.BB4.Certificates.R13.C06.C14
import BusyBeaver.BB4.Certificates.R13.C06.C15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem secondBranch_a13_a06 : secondBranch a13 a06 = true := by
  have hAll : (TNF.canonicalActions 3).all (thirdBranch_a13_a06) = true := by
    rw [canonicalActions_three_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, thirdBranch_a13_a06_a00, thirdBranch_a13_a06_a01, thirdBranch_a13_a06_a02, thirdBranch_a13_a06_a03, thirdBranch_a13_a06_a04, thirdBranch_a13_a06_a05, thirdBranch_a13_a06_a06, thirdBranch_a13_a06_a07, thirdBranch_a13_a06_a08, thirdBranch_a13_a06_a09, thirdBranch_a13_a06_a10, thirdBranch_a13_a06_a11, thirdBranch_a13_a06_a12, thirdBranch_a13_a06_a13, thirdBranch_a13_a06_a14, thirdBranch_a13_a06_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 4) a13) a06) &&
      (TNF.canonicalActions 3).all (thirdBranch_a13_a06)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
