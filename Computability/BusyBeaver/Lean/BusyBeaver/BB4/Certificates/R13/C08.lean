import BusyBeaver.BB4.Certificates.R13.C08.C00
import BusyBeaver.BB4.Certificates.R13.C08.C01
import BusyBeaver.BB4.Certificates.R13.C08.C02
import BusyBeaver.BB4.Certificates.R13.C08.C04
import BusyBeaver.BB4.Certificates.R13.C08.C05
import BusyBeaver.BB4.Certificates.R13.C08.C06
import BusyBeaver.BB4.Certificates.R13.C08.C08
import BusyBeaver.BB4.Certificates.R13.C08.C09
import BusyBeaver.BB4.Certificates.R13.C08.C10
import BusyBeaver.BB4.Certificates.R13.C08.C12
import BusyBeaver.BB4.Certificates.R13.C08.C13
import BusyBeaver.BB4.Certificates.R13.C08.C14

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem secondBranch_a13_a08 : secondBranch a13 a08 = true := by
  have hAll : (TNF.canonicalActions 2).all (thirdBranch_a13_a08) = true := by
    rw [canonicalActions_two_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, thirdBranch_a13_a08_a00, thirdBranch_a13_a08_a01, thirdBranch_a13_a08_a02, thirdBranch_a13_a08_a04, thirdBranch_a13_a08_a05, thirdBranch_a13_a08_a06, thirdBranch_a13_a08_a08, thirdBranch_a13_a08_a09, thirdBranch_a13_a08_a10, thirdBranch_a13_a08_a12, thirdBranch_a13_a08_a13, thirdBranch_a13_a08_a14]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 4) a13) a08) &&
      (TNF.canonicalActions 2).all (thirdBranch_a13_a08)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
