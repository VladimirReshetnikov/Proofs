import SetTheory.BusyBeaverBB3.Certificates.C08.C09.C10.C00
import SetTheory.BusyBeaverBB3.Certificates.C08.C09.C10.C01
import SetTheory.BusyBeaverBB3.Certificates.C08.C09.C10.C02
import SetTheory.BusyBeaverBB3.Certificates.C08.C09.C10.C03
import SetTheory.BusyBeaverBB3.Certificates.C08.C09.C10.C04
import SetTheory.BusyBeaverBB3.Certificates.C08.C09.C10.C05
import SetTheory.BusyBeaverBB3.Certificates.C08.C09.C10.C06
import SetTheory.BusyBeaverBB3.Certificates.C08.C09.C10.C07
import SetTheory.BusyBeaverBB3.Certificates.C08.C09.C10.C08
import SetTheory.BusyBeaverBB3.Certificates.C08.C09.C10.C09
import SetTheory.BusyBeaverBB3.Certificates.C08.C09.C10.C10
import SetTheory.BusyBeaverBB3.Certificates.C08.C09.C10.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem thirdMarkedBranch_a08_a09_a10 :
    thirdMarkedBranch a08 a09 a10 = true := by
  have hAll : actionList.all fourthBranch_a08_a09_a10 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fourthBranch_a08_a09_a10_a00, fourthBranch_a08_a09_a10_a01, fourthBranch_a08_a09_a10_a02, fourthBranch_a08_a09_a10_a03, fourthBranch_a08_a09_a10_a04, fourthBranch_a08_a09_a10_a05, fourthBranch_a08_a09_a10_a06, fourthBranch_a08_a09_a10_a07, fourthBranch_a08_a09_a10_a08, fourthBranch_a08_a09_a10_a09, fourthBranch_a08_a09_a10_a10, fourthBranch_a08_a09_a10_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (initial 3) a08) a09) a10) &&
      actionList.all fourthBranch_a08_a09_a10) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
