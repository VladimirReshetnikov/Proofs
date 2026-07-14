import BusyBeaver.BB3.Certificates.C07.C09.C00
import BusyBeaver.BB3.Certificates.C07.C09.C01
import BusyBeaver.BB3.Certificates.C07.C09.C02
import BusyBeaver.BB3.Certificates.C07.C09.C03
import BusyBeaver.BB3.Certificates.C07.C09.C04
import BusyBeaver.BB3.Certificates.C07.C09.C05
import BusyBeaver.BB3.Certificates.C07.C09.C06
import BusyBeaver.BB3.Certificates.C07.C09.C07
import BusyBeaver.BB3.Certificates.C07.C09.C08
import BusyBeaver.BB3.Certificates.C07.C09.C09
import BusyBeaver.BB3.Certificates.C07.C09.C10
import BusyBeaver.BB3.Certificates.C07.C09.C11

namespace SetTheory.BusyBeaver.BB3.Certificates


theorem secondBranch_a07_a09 : secondBranch a07 a09 = true := by
  have hAll : actionList.all (thirdMarkedBranch a07 a09) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, thirdMarkedBranch_a07_a09_a00, thirdMarkedBranch_a07_a09_a01, thirdMarkedBranch_a07_a09_a02, thirdMarkedBranch_a07_a09_a03, thirdMarkedBranch_a07_a09_a04, thirdMarkedBranch_a07_a09_a05, thirdMarkedBranch_a07_a09_a06, thirdMarkedBranch_a07_a09_a07, thirdMarkedBranch_a07_a09_a08, thirdMarkedBranch_a07_a09_a09, thirdMarkedBranch_a07_a09_a10, thirdMarkedBranch_a07_a09_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a07) a09) &&
      actionList.all (thirdMarkedBranch a07 a09)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
