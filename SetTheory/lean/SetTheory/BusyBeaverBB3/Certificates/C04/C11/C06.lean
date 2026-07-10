import SetTheory.BusyBeaverBB3.Certificates.C04.C11.C06.C00
import SetTheory.BusyBeaverBB3.Certificates.C04.C11.C06.C01
import SetTheory.BusyBeaverBB3.Certificates.C04.C11.C06.C02
import SetTheory.BusyBeaverBB3.Certificates.C04.C11.C06.C03
import SetTheory.BusyBeaverBB3.Certificates.C04.C11.C06.C04
import SetTheory.BusyBeaverBB3.Certificates.C04.C11.C06.C05
import SetTheory.BusyBeaverBB3.Certificates.C04.C11.C06.C06
import SetTheory.BusyBeaverBB3.Certificates.C04.C11.C06.C07
import SetTheory.BusyBeaverBB3.Certificates.C04.C11.C06.C08
import SetTheory.BusyBeaverBB3.Certificates.C04.C11.C06.C09
import SetTheory.BusyBeaverBB3.Certificates.C04.C11.C06.C10
import SetTheory.BusyBeaverBB3.Certificates.C04.C11.C06.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem thirdFreshBranch_a04_a11_a06 :
    thirdFreshBranch a04 a11 a06 = true := by
  have hAll : actionList.all fourthBranch_a04_a11_a06 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fourthBranch_a04_a11_a06_a00, fourthBranch_a04_a11_a06_a01, fourthBranch_a04_a11_a06_a02, fourthBranch_a04_a11_a06_a03, fourthBranch_a04_a11_a06_a04, fourthBranch_a04_a11_a06_a05, fourthBranch_a04_a11_a06_a06, fourthBranch_a04_a11_a06_a07, fourthBranch_a04_a11_a06_a08, fourthBranch_a04_a11_a06_a09, fourthBranch_a04_a11_a06_a10, fourthBranch_a04_a11_a06_a11]
    simp
  change
    (haltWritesSafe
      (stepGo (stepGo (stepGo (initial 3) a04) a11) a06) &&
      actionList.all fourthBranch_a04_a11_a06) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
