import SetTheory.BusyBeaverBB3.Certificates.C04.C06.C00
import SetTheory.BusyBeaverBB3.Certificates.C04.C06.C01
import SetTheory.BusyBeaverBB3.Certificates.C04.C06.C02
import SetTheory.BusyBeaverBB3.Certificates.C04.C06.C03
import SetTheory.BusyBeaverBB3.Certificates.C04.C06.C04
import SetTheory.BusyBeaverBB3.Certificates.C04.C06.C05
import SetTheory.BusyBeaverBB3.Certificates.C04.C06.C06
import SetTheory.BusyBeaverBB3.Certificates.C04.C06.C07
import SetTheory.BusyBeaverBB3.Certificates.C04.C06.C08
import SetTheory.BusyBeaverBB3.Certificates.C04.C06.C09
import SetTheory.BusyBeaverBB3.Certificates.C04.C06.C10
import SetTheory.BusyBeaverBB3.Certificates.C04.C06.C11

namespace SetTheory.BusyBeaver.BB3.Certificates


theorem secondBranch_a04_a06 : secondBranch a04 a06 = true := by
  have hAll : actionList.all (reboundBranch a04 a06) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, reboundBranch_a04_a06_a00, reboundBranch_a04_a06_a01, reboundBranch_a04_a06_a02, reboundBranch_a04_a06_a03, reboundBranch_a04_a06_a04, reboundBranch_a04_a06_a05, reboundBranch_a04_a06_a06, reboundBranch_a04_a06_a07, reboundBranch_a04_a06_a08, reboundBranch_a04_a06_a09, reboundBranch_a04_a06_a10, reboundBranch_a04_a06_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (initial 3) a04) a06) a04) &&
      actionList.all (reboundBranch a04 a06)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
