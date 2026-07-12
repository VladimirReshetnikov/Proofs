import BusyBeaver.BB3.Certificates.C07.C11.C09.Common
import BusyBeaver.BB3.Certificates.C07.C11.C09.C01.C00
import BusyBeaver.BB3.Certificates.C07.C11.C09.C01.C01
import BusyBeaver.BB3.Certificates.C07.C11.C09.C01.C02
import BusyBeaver.BB3.Certificates.C07.C11.C09.C01.C03
import BusyBeaver.BB3.Certificates.C07.C11.C09.C01.C04
import BusyBeaver.BB3.Certificates.C07.C11.C09.C01.C05
import BusyBeaver.BB3.Certificates.C07.C11.C09.C01.C06
import BusyBeaver.BB3.Certificates.C07.C11.C09.C01.C07
import BusyBeaver.BB3.Certificates.C07.C11.C09.C01.C08
import BusyBeaver.BB3.Certificates.C07.C11.C09.C01.C09
import BusyBeaver.BB3.Certificates.C07.C11.C09.C01.C10
import BusyBeaver.BB3.Certificates.C07.C11.C09.C01.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem fourthBranch_a07_a11_a09_a01 :
    fourthBranch_a07_a11_a09 a01 = true := by
  have hAll : actionList.all fifthBranch_a07_a11_a09_a01 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fifthBranch_a07_a11_a09_a01_a00, fifthBranch_a07_a11_a09_a01_a01, fifthBranch_a07_a11_a09_a01_a02, fifthBranch_a07_a11_a09_a01_a03, fifthBranch_a07_a11_a09_a01_a04, fifthBranch_a07_a11_a09_a01_a05, fifthBranch_a07_a11_a09_a01_a06, fifthBranch_a07_a11_a09_a01_a07, fifthBranch_a07_a11_a09_a01_a08, fifthBranch_a07_a11_a09_a01_a09, fifthBranch_a07_a11_a09_a01_a10, fifthBranch_a07_a11_a09_a01_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 3) a07) a11) a09) a07) a01) a01) a11) &&
      actionList.all fifthBranch_a07_a11_a09_a01) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
