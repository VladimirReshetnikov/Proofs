import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.Common
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C05.C03
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C05.C04
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C05.C05
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C05.C00
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C05.C01
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C05.C02
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C05.C09
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C05.C10
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C05.C11
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C05.C06
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C05.C07
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C06.C05.C08

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem fourthBranch_a11_a07_a06_a05 :
    fourthBranch_a11_a07_a06 a05 = true := by
  have hAll : actionList.all fifthBranch_a11_a07_a06_a05 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fifthBranch_a11_a07_a06_a05_a03, fifthBranch_a11_a07_a06_a05_a04, fifthBranch_a11_a07_a06_a05_a05, fifthBranch_a11_a07_a06_a05_a00, fifthBranch_a11_a07_a06_a05_a01, fifthBranch_a11_a07_a06_a05_a02, fifthBranch_a11_a07_a06_a05_a09, fifthBranch_a11_a07_a06_a05_a10, fifthBranch_a11_a07_a06_a05_a11, fifthBranch_a11_a07_a06_a05_a06, fifthBranch_a11_a07_a06_a05_a07, fifthBranch_a11_a07_a06_a05_a08]
    simp
  change
    (haltWritesSafe
      (stepGo
        (stepGo
          (stepGo
            (stepGo
              (stepGo
                (stepGo
                  (stepGo (initial 3) a11)
                  a07)
                a06)
              a11)
            a05)
          a05)
        a07) &&
      actionList.all fifthBranch_a11_a07_a06_a05) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates

