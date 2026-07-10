import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C01.Common
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C01.C09.C03
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C01.C09.C04
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C01.C09.C05
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C01.C09.C00
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C01.C09.C01
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C01.C09.C02
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C01.C09.C09
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C01.C09.C10
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C01.C09.C11
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C01.C09.C06
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C01.C09.C07
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C01.C09.C08

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem fourthBranch_a11_a07_a01_a09 :
    fourthBranch_a11_a07_a01 a09 = true := by
  have hAll : actionList.all fifthBranch_a11_a07_a01_a09 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fifthBranch_a11_a07_a01_a09_a03, fifthBranch_a11_a07_a01_a09_a04, fifthBranch_a11_a07_a01_a09_a05, fifthBranch_a11_a07_a01_a09_a00, fifthBranch_a11_a07_a01_a09_a01, fifthBranch_a11_a07_a01_a09_a02, fifthBranch_a11_a07_a01_a09_a09, fifthBranch_a11_a07_a01_a09_a10, fifthBranch_a11_a07_a01_a09_a11, fifthBranch_a11_a07_a01_a09_a06, fifthBranch_a11_a07_a01_a09_a07, fifthBranch_a11_a07_a01_a09_a08]
    simp
  change
    (haltWritesSafe
      (stepGo
        (stepGo
          (stepGo
            (stepGo (stepGo (initial 3) a11) a07)
            a01)
          a09)
        a11) &&
      actionList.all fifthBranch_a11_a07_a01_a09) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates

