import BusyBeaver.BB3.Certificates.C10.C06.C00
import BusyBeaver.BB3.Certificates.C10.C06.C01
import BusyBeaver.BB3.Certificates.C10.C06.C02
import BusyBeaver.BB3.Certificates.C10.C06.C03
import BusyBeaver.BB3.Certificates.C10.C06.C04
import BusyBeaver.BB3.Certificates.C10.C06.C05
import BusyBeaver.BB3.Certificates.C10.C06.C06
import BusyBeaver.BB3.Certificates.C10.C06.C07
import BusyBeaver.BB3.Certificates.C10.C06.C08
import BusyBeaver.BB3.Certificates.C10.C06.C09
import BusyBeaver.BB3.Certificates.C10.C06.C10
import BusyBeaver.BB3.Certificates.C10.C06.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem secondBranch_a10_a06 : secondBranch a10 a06 = true := by
  have hAll : actionList.all (thirdMarkedBranch a10 a06) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      thirdMarkedBranch_a10_a06_a00, thirdMarkedBranch_a10_a06_a01, thirdMarkedBranch_a10_a06_a02, thirdMarkedBranch_a10_a06_a03, thirdMarkedBranch_a10_a06_a04, thirdMarkedBranch_a10_a06_a05, thirdMarkedBranch_a10_a06_a06, thirdMarkedBranch_a10_a06_a07, thirdMarkedBranch_a10_a06_a08, thirdMarkedBranch_a10_a06_a09, thirdMarkedBranch_a10_a06_a10, thirdMarkedBranch_a10_a06_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a10) a06) &&
      actionList.all (thirdMarkedBranch a10 a06)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
