import SetTheory.BusyBeaverBB3.Certificates.C07.C05.C09.C00
import SetTheory.BusyBeaverBB3.Certificates.C07.C05.C09.C01
import SetTheory.BusyBeaverBB3.Certificates.C07.C05.C09.C02
import SetTheory.BusyBeaverBB3.Certificates.C07.C05.C09.C03
import SetTheory.BusyBeaverBB3.Certificates.C07.C05.C09.C04
import SetTheory.BusyBeaverBB3.Certificates.C07.C05.C09.C05
import SetTheory.BusyBeaverBB3.Certificates.C07.C05.C09.C06
import SetTheory.BusyBeaverBB3.Certificates.C07.C05.C09.C07
import SetTheory.BusyBeaverBB3.Certificates.C07.C05.C09.C08
import SetTheory.BusyBeaverBB3.Certificates.C07.C05.C09.C09
import SetTheory.BusyBeaverBB3.Certificates.C07.C05.C09.C10
import SetTheory.BusyBeaverBB3.Certificates.C07.C05.C09.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem thirdMarkedBranch_a07_a05_a09 :
    thirdMarkedBranch a07 a05 a09 = true := by
  have hAll : actionList.all fourthBranch_a07_a05_a09 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fourthBranch_a07_a05_a09_a00, fourthBranch_a07_a05_a09_a01, fourthBranch_a07_a05_a09_a02, fourthBranch_a07_a05_a09_a03, fourthBranch_a07_a05_a09_a04, fourthBranch_a07_a05_a09_a05, fourthBranch_a07_a05_a09_a06, fourthBranch_a07_a05_a09_a07, fourthBranch_a07_a05_a09_a08, fourthBranch_a07_a05_a09_a09, fourthBranch_a07_a05_a09_a10, fourthBranch_a07_a05_a09_a11]
    simp
  change
    (haltWritesSafe
      (stepGo
        (stepGo (stepGo (stepGo (initial 3) a07) a05) a09) a07) &&
      actionList.all fourthBranch_a07_a05_a09) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
