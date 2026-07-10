import SetTheory.BusyBeaverBB3.Certificates.C08.C01.C00
import SetTheory.BusyBeaverBB3.Certificates.C08.C01.C01
import SetTheory.BusyBeaverBB3.Certificates.C08.C01.C02
import SetTheory.BusyBeaverBB3.Certificates.C08.C01.C03
import SetTheory.BusyBeaverBB3.Certificates.C08.C01.C04
import SetTheory.BusyBeaverBB3.Certificates.C08.C01.C05
import SetTheory.BusyBeaverBB3.Certificates.C08.C01.C06
import SetTheory.BusyBeaverBB3.Certificates.C08.C01.C07
import SetTheory.BusyBeaverBB3.Certificates.C08.C01.C08
import SetTheory.BusyBeaverBB3.Certificates.C08.C01.C09
import SetTheory.BusyBeaverBB3.Certificates.C08.C01.C10
import SetTheory.BusyBeaverBB3.Certificates.C08.C01.C11

namespace SetTheory.BusyBeaver.BB3.Certificates


theorem secondBranch_a08_a01 : secondBranch a08 a01 = true := by
  have hAll : actionList.all (thirdFreshBranch a08 a01) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, thirdFreshBranch_a08_a01_a00, thirdFreshBranch_a08_a01_a01, thirdFreshBranch_a08_a01_a02, thirdFreshBranch_a08_a01_a03, thirdFreshBranch_a08_a01_a04, thirdFreshBranch_a08_a01_a05, thirdFreshBranch_a08_a01_a06, thirdFreshBranch_a08_a01_a07, thirdFreshBranch_a08_a01_a08, thirdFreshBranch_a08_a01_a09, thirdFreshBranch_a08_a01_a10, thirdFreshBranch_a08_a01_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a08) a01) &&
      actionList.all (thirdFreshBranch a08 a01)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
