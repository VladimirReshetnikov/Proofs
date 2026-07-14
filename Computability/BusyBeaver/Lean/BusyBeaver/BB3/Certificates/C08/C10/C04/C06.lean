import BusyBeaver.BB3.Certificates.C08.C10.C04.Common
import BusyBeaver.BB3.Certificates.C08.C10.C04.C06.C00
import BusyBeaver.BB3.Certificates.C08.C10.C04.C06.C01
import BusyBeaver.BB3.Certificates.C08.C10.C04.C06.C02
import BusyBeaver.BB3.Certificates.C08.C10.C04.C06.C03
import BusyBeaver.BB3.Certificates.C08.C10.C04.C06.C04
import BusyBeaver.BB3.Certificates.C08.C10.C04.C06.C05
import BusyBeaver.BB3.Certificates.C08.C10.C04.C06.C06
import BusyBeaver.BB3.Certificates.C08.C10.C04.C06.C07
import BusyBeaver.BB3.Certificates.C08.C10.C04.C06.C08
import BusyBeaver.BB3.Certificates.C08.C10.C04.C06.C09
import BusyBeaver.BB3.Certificates.C08.C10.C04.C06.C10
import BusyBeaver.BB3.Certificates.C08.C10.C04.C06.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem fourthBranch_a08_a10_a04_a06 :
    fourthBranch_a08_a10_a04 a06 = true := by
  have hAll : actionList.all fifthBranch_a08_a10_a04_a06 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fifthBranch_a08_a10_a04_a06_a00, fifthBranch_a08_a10_a04_a06_a01, fifthBranch_a08_a10_a04_a06_a02, fifthBranch_a08_a10_a04_a06_a03, fifthBranch_a08_a10_a04_a06_a04, fifthBranch_a08_a10_a04_a06_a05, fifthBranch_a08_a10_a04_a06_a06, fifthBranch_a08_a10_a04_a06_a07, fifthBranch_a08_a10_a04_a06_a08, fifthBranch_a08_a10_a04_a06_a09, fifthBranch_a08_a10_a04_a06_a10, fifthBranch_a08_a10_a04_a06_a11]
    simp
  change
    (haltWritesSafe
      (stepGo
        (stepGo
          (stepGo
            (stepGo (stepGo (initial 3) a08) a10)
            a04)
          a06)
        a08) &&
      actionList.all fifthBranch_a08_a10_a04_a06) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
