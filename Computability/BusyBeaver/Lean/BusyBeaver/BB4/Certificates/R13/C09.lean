import BusyBeaver.BB4.Certificates.R13.C09.C00
import BusyBeaver.BB4.Certificates.R13.C09.C01
import BusyBeaver.BB4.Certificates.R13.C09.C02
import BusyBeaver.BB4.Certificates.R13.C09.C04
import BusyBeaver.BB4.Certificates.R13.C09.C05
import BusyBeaver.BB4.Certificates.R13.C09.C06
import BusyBeaver.BB4.Certificates.R13.C09.C08
import BusyBeaver.BB4.Certificates.R13.C09.C09
import BusyBeaver.BB4.Certificates.R13.C09.C10
import BusyBeaver.BB4.Certificates.R13.C09.C12
import BusyBeaver.BB4.Certificates.R13.C09.C13
import BusyBeaver.BB4.Certificates.R13.C09.C14

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem secondBranch_a13_a09 : secondBranch a13 a09 = true := by
  have hAll : (TNF.canonicalActions 2).all (thirdBranch_a13_a09) = true := by
    rw [canonicalActions_two_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, thirdBranch_a13_a09_a00, thirdBranch_a13_a09_a01, thirdBranch_a13_a09_a02, thirdBranch_a13_a09_a04, thirdBranch_a13_a09_a05, thirdBranch_a13_a09_a06, thirdBranch_a13_a09_a08, thirdBranch_a13_a09_a09, thirdBranch_a13_a09_a10, thirdBranch_a13_a09_a12, thirdBranch_a13_a09_a13, thirdBranch_a13_a09_a14]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 4) a13) a09) &&
      (TNF.canonicalActions 2).all (thirdBranch_a13_a09)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
