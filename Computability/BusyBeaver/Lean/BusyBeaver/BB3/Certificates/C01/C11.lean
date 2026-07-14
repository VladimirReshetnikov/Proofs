import BusyBeaver.BB3.Certificates.C01.C11.C00
import BusyBeaver.BB3.Certificates.C01.C11.C01
import BusyBeaver.BB3.Certificates.C01.C11.C02
import BusyBeaver.BB3.Certificates.C01.C11.C03
import BusyBeaver.BB3.Certificates.C01.C11.C04
import BusyBeaver.BB3.Certificates.C01.C11.C05
import BusyBeaver.BB3.Certificates.C01.C11.C06
import BusyBeaver.BB3.Certificates.C01.C11.C07
import BusyBeaver.BB3.Certificates.C01.C11.C08
import BusyBeaver.BB3.Certificates.C01.C11.C09
import BusyBeaver.BB3.Certificates.C01.C11.C10
import BusyBeaver.BB3.Certificates.C01.C11.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem secondBranch_a01_a11 : secondBranch a01 a11 = true := by
  have hAll : actionList.all (thirdFreshBranch a01 a11) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, thirdFreshBranch_a01_a11_a00, thirdFreshBranch_a01_a11_a01, thirdFreshBranch_a01_a11_a02, thirdFreshBranch_a01_a11_a03, thirdFreshBranch_a01_a11_a04, thirdFreshBranch_a01_a11_a05, thirdFreshBranch_a01_a11_a06, thirdFreshBranch_a01_a11_a07, thirdFreshBranch_a01_a11_a08, thirdFreshBranch_a01_a11_a09, thirdFreshBranch_a01_a11_a10, thirdFreshBranch_a01_a11_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a01) a11) &&
      actionList.all (thirdFreshBranch a01 a11)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
