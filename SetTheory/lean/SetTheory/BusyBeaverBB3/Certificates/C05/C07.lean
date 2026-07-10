import SetTheory.BusyBeaverBB3.Certificates.C05.C07.C00
import SetTheory.BusyBeaverBB3.Certificates.C05.C07.C01
import SetTheory.BusyBeaverBB3.Certificates.C05.C07.C02
import SetTheory.BusyBeaverBB3.Certificates.C05.C07.C03
import SetTheory.BusyBeaverBB3.Certificates.C05.C07.C04
import SetTheory.BusyBeaverBB3.Certificates.C05.C07.C05
import SetTheory.BusyBeaverBB3.Certificates.C05.C07.C06
import SetTheory.BusyBeaverBB3.Certificates.C05.C07.C07
import SetTheory.BusyBeaverBB3.Certificates.C05.C07.C08
import SetTheory.BusyBeaverBB3.Certificates.C05.C07.C09
import SetTheory.BusyBeaverBB3.Certificates.C05.C07.C10
import SetTheory.BusyBeaverBB3.Certificates.C05.C07.C11

namespace SetTheory.BusyBeaver.BB3.Certificates


theorem secondBranch_a05_a07 : secondBranch a05 a07 = true := by
  have hAll : actionList.all (thirdFreshBranch a05 a07) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, thirdFreshBranch_a05_a07_a00, thirdFreshBranch_a05_a07_a01, thirdFreshBranch_a05_a07_a02, thirdFreshBranch_a05_a07_a03, thirdFreshBranch_a05_a07_a04, thirdFreshBranch_a05_a07_a05, thirdFreshBranch_a05_a07_a06, thirdFreshBranch_a05_a07_a07, thirdFreshBranch_a05_a07_a08, thirdFreshBranch_a05_a07_a09, thirdFreshBranch_a05_a07_a10, thirdFreshBranch_a05_a07_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a05) a07) &&
      actionList.all (thirdFreshBranch a05 a07)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
