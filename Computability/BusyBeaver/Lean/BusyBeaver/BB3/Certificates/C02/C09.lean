import BusyBeaver.BB3.Certificates.C02.C09.C00
import BusyBeaver.BB3.Certificates.C02.C09.C01
import BusyBeaver.BB3.Certificates.C02.C09.C02
import BusyBeaver.BB3.Certificates.C02.C09.C03
import BusyBeaver.BB3.Certificates.C02.C09.C04
import BusyBeaver.BB3.Certificates.C02.C09.C05
import BusyBeaver.BB3.Certificates.C02.C09.C06
import BusyBeaver.BB3.Certificates.C02.C09.C07
import BusyBeaver.BB3.Certificates.C02.C09.C08
import BusyBeaver.BB3.Certificates.C02.C09.C09
import BusyBeaver.BB3.Certificates.C02.C09.C10
import BusyBeaver.BB3.Certificates.C02.C09.C11

namespace SetTheory.BusyBeaver.BB3.Certificates


theorem secondBranch_a02_a09 : secondBranch a02 a09 = true := by
  have hAll : actionList.all (reboundBranch a02 a09) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, reboundBranch_a02_a09_a00, reboundBranch_a02_a09_a01, reboundBranch_a02_a09_a02, reboundBranch_a02_a09_a03, reboundBranch_a02_a09_a04, reboundBranch_a02_a09_a05, reboundBranch_a02_a09_a06, reboundBranch_a02_a09_a07, reboundBranch_a02_a09_a08, reboundBranch_a02_a09_a09, reboundBranch_a02_a09_a10, reboundBranch_a02_a09_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (initial 3) a02) a09) a02) &&
      actionList.all (reboundBranch a02 a09)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
