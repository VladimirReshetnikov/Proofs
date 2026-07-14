import BusyBeaver.BB3.Certificates.C07.C09.C11.C00
import BusyBeaver.BB3.Certificates.C07.C09.C11.C01
import BusyBeaver.BB3.Certificates.C07.C09.C11.C02
import BusyBeaver.BB3.Certificates.C07.C09.C11.C03
import BusyBeaver.BB3.Certificates.C07.C09.C11.C04
import BusyBeaver.BB3.Certificates.C07.C09.C11.C05
import BusyBeaver.BB3.Certificates.C07.C09.C11.C06
import BusyBeaver.BB3.Certificates.C07.C09.C11.C07
import BusyBeaver.BB3.Certificates.C07.C09.C11.C08
import BusyBeaver.BB3.Certificates.C07.C09.C11.C09
import BusyBeaver.BB3.Certificates.C07.C09.C11.C10
import BusyBeaver.BB3.Certificates.C07.C09.C11.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem thirdMarkedBranch_a07_a09_a11 :
    thirdMarkedBranch a07 a09 a11 = true := by
  have hAll : actionList.all fourthBranch_a07_a09_a11 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fourthBranch_a07_a09_a11_a00, fourthBranch_a07_a09_a11_a01, fourthBranch_a07_a09_a11_a02, fourthBranch_a07_a09_a11_a03, fourthBranch_a07_a09_a11_a04, fourthBranch_a07_a09_a11_a05, fourthBranch_a07_a09_a11_a06, fourthBranch_a07_a09_a11_a07, fourthBranch_a07_a09_a11_a08, fourthBranch_a07_a09_a11_a09, fourthBranch_a07_a09_a11_a10, fourthBranch_a07_a09_a11_a11]
    simp
  change
    (haltWritesSafe
      (stepGo (stepGo (stepGo (initial 3) a07) a09) a11) &&
      actionList.all fourthBranch_a07_a09_a11) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
