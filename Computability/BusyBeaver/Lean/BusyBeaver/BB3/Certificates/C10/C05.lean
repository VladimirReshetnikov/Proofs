import BusyBeaver.BB3.Certificates.C10.C05.C00
import BusyBeaver.BB3.Certificates.C10.C05.C01
import BusyBeaver.BB3.Certificates.C10.C05.C02
import BusyBeaver.BB3.Certificates.C10.C05.C03
import BusyBeaver.BB3.Certificates.C10.C05.C04
import BusyBeaver.BB3.Certificates.C10.C05.C05
import BusyBeaver.BB3.Certificates.C10.C05.C06
import BusyBeaver.BB3.Certificates.C10.C05.C07
import BusyBeaver.BB3.Certificates.C10.C05.C08
import BusyBeaver.BB3.Certificates.C10.C05.C09
import BusyBeaver.BB3.Certificates.C10.C05.C10
import BusyBeaver.BB3.Certificates.C10.C05.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem secondBranch_a10_a05 : secondBranch a10 a05 = true := by
  have hAll : actionList.all (thirdFreshBranch a10 a05) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      thirdFreshBranch_a10_a05_a00, thirdFreshBranch_a10_a05_a01, thirdFreshBranch_a10_a05_a02, thirdFreshBranch_a10_a05_a03, thirdFreshBranch_a10_a05_a04, thirdFreshBranch_a10_a05_a05, thirdFreshBranch_a10_a05_a06, thirdFreshBranch_a10_a05_a07, thirdFreshBranch_a10_a05_a08, thirdFreshBranch_a10_a05_a09, thirdFreshBranch_a10_a05_a10, thirdFreshBranch_a10_a05_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a10) a05) &&
      actionList.all (thirdFreshBranch a10 a05)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
