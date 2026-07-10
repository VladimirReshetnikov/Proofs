import SetTheory.BusyBeaverBB3.Certificates.C11.C10.C03
import SetTheory.BusyBeaverBB3.Certificates.C11.C10.C04
import SetTheory.BusyBeaverBB3.Certificates.C11.C10.C05
import SetTheory.BusyBeaverBB3.Certificates.C11.C10.C00
import SetTheory.BusyBeaverBB3.Certificates.C11.C10.C01
import SetTheory.BusyBeaverBB3.Certificates.C11.C10.C02
import SetTheory.BusyBeaverBB3.Certificates.C11.C10.C09
import SetTheory.BusyBeaverBB3.Certificates.C11.C10.C10
import SetTheory.BusyBeaverBB3.Certificates.C11.C10.C11
import SetTheory.BusyBeaverBB3.Certificates.C11.C10.C06
import SetTheory.BusyBeaverBB3.Certificates.C11.C10.C07
import SetTheory.BusyBeaverBB3.Certificates.C11.C10.C08

namespace SetTheory.BusyBeaver.BB3.Certificates


theorem secondBranch_a11_a10 : secondBranch a11 a10 = true := by
  have hAll : actionList.all (thirdFreshBranch a11 a10) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, thirdFreshBranch_a11_a10_a03, thirdFreshBranch_a11_a10_a04, thirdFreshBranch_a11_a10_a05, thirdFreshBranch_a11_a10_a00, thirdFreshBranch_a11_a10_a01, thirdFreshBranch_a11_a10_a02, thirdFreshBranch_a11_a10_a09, thirdFreshBranch_a11_a10_a10, thirdFreshBranch_a11_a10_a11, thirdFreshBranch_a11_a10_a06, thirdFreshBranch_a11_a10_a07, thirdFreshBranch_a11_a10_a08]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a11) a10) &&
      actionList.all (thirdFreshBranch a11 a10)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates

