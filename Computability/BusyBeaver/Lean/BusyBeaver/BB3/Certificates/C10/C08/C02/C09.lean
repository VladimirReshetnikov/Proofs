import BusyBeaver.BB3.Certificates.C10.C08.C02.Common
import BusyBeaver.BB3.Certificates.C10.C08.C02.C09.C00
import BusyBeaver.BB3.Certificates.C10.C08.C02.C09.C01
import BusyBeaver.BB3.Certificates.C10.C08.C02.C09.C02
import BusyBeaver.BB3.Certificates.C10.C08.C02.C09.C03
import BusyBeaver.BB3.Certificates.C10.C08.C02.C09.C04
import BusyBeaver.BB3.Certificates.C10.C08.C02.C09.C05
import BusyBeaver.BB3.Certificates.C10.C08.C02.C09.C06
import BusyBeaver.BB3.Certificates.C10.C08.C02.C09.C07
import BusyBeaver.BB3.Certificates.C10.C08.C02.C09.C08
import BusyBeaver.BB3.Certificates.C10.C08.C02.C09.C09
import BusyBeaver.BB3.Certificates.C10.C08.C02.C09.C10
import BusyBeaver.BB3.Certificates.C10.C08.C02.C09.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem fourthBranch_a10_a08_a02_a09 :
    fourthBranch_a10_a08_a02 a09 = true := by
  have hAll : actionList.all fifthBranch_a10_a08_a02_a09 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fifthBranch_a10_a08_a02_a09_a00, fifthBranch_a10_a08_a02_a09_a01, fifthBranch_a10_a08_a02_a09_a02, fifthBranch_a10_a08_a02_a09_a03, fifthBranch_a10_a08_a02_a09_a04, fifthBranch_a10_a08_a02_a09_a05, fifthBranch_a10_a08_a02_a09_a06, fifthBranch_a10_a08_a02_a09_a07, fifthBranch_a10_a08_a02_a09_a08, fifthBranch_a10_a08_a02_a09_a09, fifthBranch_a10_a08_a02_a09_a10, fifthBranch_a10_a08_a02_a09_a11]
    simp
  change
    (haltWritesSafe
      (stepGo
        (stepGo
          (stepGo
            (stepGo (stepGo (initial 3) a10) a08)
            a02)
          a09)
        a10) &&
      actionList.all fifthBranch_a10_a08_a02_a09) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
