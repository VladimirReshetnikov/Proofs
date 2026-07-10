import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C03
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C04
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C05
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C00
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C01
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C02
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C09
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C10
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C11
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C06
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C07
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C08

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem thirdMarkedBranch_a11_a07_a06 :
    thirdMarkedBranch a11 a07 a06 = true := by
  have hAll : actionList.all fourthBranch_a11_a07_a06 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fourthBranch_a11_a07_a06_a03, fourthBranch_a11_a07_a06_a04, fourthBranch_a11_a07_a06_a05, fourthBranch_a11_a07_a06_a00, fourthBranch_a11_a07_a06_a01, fourthBranch_a11_a07_a06_a02, fourthBranch_a11_a07_a06_a09, fourthBranch_a11_a07_a06_a10, fourthBranch_a11_a07_a06_a11, fourthBranch_a11_a07_a06_a06, fourthBranch_a11_a07_a06_a07, fourthBranch_a11_a07_a06_a08]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (initial 3) a11) a07) a06) a11) &&
      actionList.all fourthBranch_a11_a07_a06) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates

