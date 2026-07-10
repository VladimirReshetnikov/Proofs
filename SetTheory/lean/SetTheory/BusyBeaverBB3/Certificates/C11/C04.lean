import SetTheory.BusyBeaverBB3.Certificates.C11.C04.C03
import SetTheory.BusyBeaverBB3.Certificates.C11.C04.C04
import SetTheory.BusyBeaverBB3.Certificates.C11.C04.C05
import SetTheory.BusyBeaverBB3.Certificates.C11.C04.C00
import SetTheory.BusyBeaverBB3.Certificates.C11.C04.C01
import SetTheory.BusyBeaverBB3.Certificates.C11.C04.C02
import SetTheory.BusyBeaverBB3.Certificates.C11.C04.C09
import SetTheory.BusyBeaverBB3.Certificates.C11.C04.C10
import SetTheory.BusyBeaverBB3.Certificates.C11.C04.C11
import SetTheory.BusyBeaverBB3.Certificates.C11.C04.C06
import SetTheory.BusyBeaverBB3.Certificates.C11.C04.C07
import SetTheory.BusyBeaverBB3.Certificates.C11.C04.C08

namespace SetTheory.BusyBeaver.BB3.Certificates


theorem secondBranch_a11_a04 : secondBranch a11 a04 = true := by
  have hAll : actionList.all (thirdFreshBranch a11 a04) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, thirdFreshBranch_a11_a04_a03, thirdFreshBranch_a11_a04_a04, thirdFreshBranch_a11_a04_a05, thirdFreshBranch_a11_a04_a00, thirdFreshBranch_a11_a04_a01, thirdFreshBranch_a11_a04_a02, thirdFreshBranch_a11_a04_a09, thirdFreshBranch_a11_a04_a10, thirdFreshBranch_a11_a04_a11, thirdFreshBranch_a11_a04_a06, thirdFreshBranch_a11_a04_a07, thirdFreshBranch_a11_a04_a08]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a11) a04) &&
      actionList.all (thirdFreshBranch a11 a04)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates

