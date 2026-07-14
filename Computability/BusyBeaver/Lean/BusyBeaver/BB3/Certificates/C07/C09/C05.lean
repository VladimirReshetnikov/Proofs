import BusyBeaver.BB3.Certificates.C07.C09.C05.C00
import BusyBeaver.BB3.Certificates.C07.C09.C05.C01
import BusyBeaver.BB3.Certificates.C07.C09.C05.C02
import BusyBeaver.BB3.Certificates.C07.C09.C05.C03
import BusyBeaver.BB3.Certificates.C07.C09.C05.C04
import BusyBeaver.BB3.Certificates.C07.C09.C05.C05
import BusyBeaver.BB3.Certificates.C07.C09.C05.C06
import BusyBeaver.BB3.Certificates.C07.C09.C05.C07
import BusyBeaver.BB3.Certificates.C07.C09.C05.C08
import BusyBeaver.BB3.Certificates.C07.C09.C05.C09
import BusyBeaver.BB3.Certificates.C07.C09.C05.C10
import BusyBeaver.BB3.Certificates.C07.C09.C05.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem thirdMarkedBranch_a07_a09_a05 :
    thirdMarkedBranch a07 a09 a05 = true := by
  have hAll : actionList.all fourthBranch_a07_a09_a05 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fourthBranch_a07_a09_a05_a00, fourthBranch_a07_a09_a05_a01, fourthBranch_a07_a09_a05_a02, fourthBranch_a07_a09_a05_a03, fourthBranch_a07_a09_a05_a04, fourthBranch_a07_a09_a05_a05, fourthBranch_a07_a09_a05_a06, fourthBranch_a07_a09_a05_a07, fourthBranch_a07_a09_a05_a08, fourthBranch_a07_a09_a05_a09, fourthBranch_a07_a09_a05_a10, fourthBranch_a07_a09_a05_a11]
    simp
  change
    (haltWritesSafe
      (stepGo (stepGo (stepGo (initial 3) a07) a09) a05) &&
      actionList.all fourthBranch_a07_a09_a05) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
