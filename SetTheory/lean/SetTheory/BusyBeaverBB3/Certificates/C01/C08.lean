import SetTheory.BusyBeaverBB3.Certificates.C01.C08.C00
import SetTheory.BusyBeaverBB3.Certificates.C01.C08.C01
import SetTheory.BusyBeaverBB3.Certificates.C01.C08.C02
import SetTheory.BusyBeaverBB3.Certificates.C01.C08.C03
import SetTheory.BusyBeaverBB3.Certificates.C01.C08.C04
import SetTheory.BusyBeaverBB3.Certificates.C01.C08.C05
import SetTheory.BusyBeaverBB3.Certificates.C01.C08.C06
import SetTheory.BusyBeaverBB3.Certificates.C01.C08.C07
import SetTheory.BusyBeaverBB3.Certificates.C01.C08.C08
import SetTheory.BusyBeaverBB3.Certificates.C01.C08.C09
import SetTheory.BusyBeaverBB3.Certificates.C01.C08.C10
import SetTheory.BusyBeaverBB3.Certificates.C01.C08.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem secondBranch_a01_a08 : secondBranch a01 a08 = true := by
  have hAll : actionList.all (thirdFreshBranch a01 a08) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, thirdFreshBranch_a01_a08_a00, thirdFreshBranch_a01_a08_a01, thirdFreshBranch_a01_a08_a02, thirdFreshBranch_a01_a08_a03, thirdFreshBranch_a01_a08_a04, thirdFreshBranch_a01_a08_a05, thirdFreshBranch_a01_a08_a06, thirdFreshBranch_a01_a08_a07, thirdFreshBranch_a01_a08_a08, thirdFreshBranch_a01_a08_a09, thirdFreshBranch_a01_a08_a10, thirdFreshBranch_a01_a08_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a01) a08) &&
      actionList.all (thirdFreshBranch a01 a08)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
