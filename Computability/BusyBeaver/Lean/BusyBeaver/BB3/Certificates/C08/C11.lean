import BusyBeaver.BB3.Certificates.C08.C11.C00
import BusyBeaver.BB3.Certificates.C08.C11.C01
import BusyBeaver.BB3.Certificates.C08.C11.C02
import BusyBeaver.BB3.Certificates.C08.C11.C03
import BusyBeaver.BB3.Certificates.C08.C11.C04
import BusyBeaver.BB3.Certificates.C08.C11.C05
import BusyBeaver.BB3.Certificates.C08.C11.C06
import BusyBeaver.BB3.Certificates.C08.C11.C07
import BusyBeaver.BB3.Certificates.C08.C11.C08
import BusyBeaver.BB3.Certificates.C08.C11.C09
import BusyBeaver.BB3.Certificates.C08.C11.C10
import BusyBeaver.BB3.Certificates.C08.C11.C11

namespace SetTheory.BusyBeaver.BB3.Certificates


theorem secondBranch_a08_a11 : secondBranch a08 a11 = true := by
  have hAll : actionList.all (thirdMarkedBranch a08 a11) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, thirdMarkedBranch_a08_a11_a00, thirdMarkedBranch_a08_a11_a01, thirdMarkedBranch_a08_a11_a02, thirdMarkedBranch_a08_a11_a03, thirdMarkedBranch_a08_a11_a04, thirdMarkedBranch_a08_a11_a05, thirdMarkedBranch_a08_a11_a06, thirdMarkedBranch_a08_a11_a07, thirdMarkedBranch_a08_a11_a08, thirdMarkedBranch_a08_a11_a09, thirdMarkedBranch_a08_a11_a10, thirdMarkedBranch_a08_a11_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a08) a11) &&
      actionList.all (thirdMarkedBranch a08 a11)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
