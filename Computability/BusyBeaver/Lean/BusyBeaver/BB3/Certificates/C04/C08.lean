import BusyBeaver.BB3.Certificates.C04.C08.C00
import BusyBeaver.BB3.Certificates.C04.C08.C01
import BusyBeaver.BB3.Certificates.C04.C08.C02
import BusyBeaver.BB3.Certificates.C04.C08.C03
import BusyBeaver.BB3.Certificates.C04.C08.C04
import BusyBeaver.BB3.Certificates.C04.C08.C05
import BusyBeaver.BB3.Certificates.C04.C08.C06
import BusyBeaver.BB3.Certificates.C04.C08.C07
import BusyBeaver.BB3.Certificates.C04.C08.C08
import BusyBeaver.BB3.Certificates.C04.C08.C09
import BusyBeaver.BB3.Certificates.C04.C08.C10
import BusyBeaver.BB3.Certificates.C04.C08.C11

namespace SetTheory.BusyBeaver.BB3.Certificates


theorem secondBranch_a04_a08 : secondBranch a04 a08 = true := by
  have hAll : actionList.all (thirdFreshBranch a04 a08) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, thirdFreshBranch_a04_a08_a00, thirdFreshBranch_a04_a08_a01, thirdFreshBranch_a04_a08_a02, thirdFreshBranch_a04_a08_a03, thirdFreshBranch_a04_a08_a04, thirdFreshBranch_a04_a08_a05, thirdFreshBranch_a04_a08_a06, thirdFreshBranch_a04_a08_a07, thirdFreshBranch_a04_a08_a08, thirdFreshBranch_a04_a08_a09, thirdFreshBranch_a04_a08_a10, thirdFreshBranch_a04_a08_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a04) a08) &&
      actionList.all (thirdFreshBranch a04 a08)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
