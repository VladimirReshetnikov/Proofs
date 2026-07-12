import BusyBeaver.BB3.Certificates.C08.C10.C09.Common
import BusyBeaver.BB3.Certificates.C08.C10.C09.C02.C00
import BusyBeaver.BB3.Certificates.C08.C10.C09.C02.C01
import BusyBeaver.BB3.Certificates.C08.C10.C09.C02.C02
import BusyBeaver.BB3.Certificates.C08.C10.C09.C02.C03
import BusyBeaver.BB3.Certificates.C08.C10.C09.C02.C04
import BusyBeaver.BB3.Certificates.C08.C10.C09.C02.C05
import BusyBeaver.BB3.Certificates.C08.C10.C09.C02.C06
import BusyBeaver.BB3.Certificates.C08.C10.C09.C02.C07
import BusyBeaver.BB3.Certificates.C08.C10.C09.C02.C08
import BusyBeaver.BB3.Certificates.C08.C10.C09.C02.C09
import BusyBeaver.BB3.Certificates.C08.C10.C09.C02.C10
import BusyBeaver.BB3.Certificates.C08.C10.C09.C02.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem fourthBranch_a08_a10_a09_a02 :
    fourthBranch_a08_a10_a09 a02 = true := by
  have hAll : actionList.all fifthBranch_a08_a10_a09_a02 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fifthBranch_a08_a10_a09_a02_a00, fifthBranch_a08_a10_a09_a02_a01, fifthBranch_a08_a10_a09_a02_a02, fifthBranch_a08_a10_a09_a02_a03, fifthBranch_a08_a10_a09_a02_a04, fifthBranch_a08_a10_a09_a02_a05, fifthBranch_a08_a10_a09_a02_a06, fifthBranch_a08_a10_a09_a02_a07, fifthBranch_a08_a10_a09_a02_a08, fifthBranch_a08_a10_a09_a02_a09, fifthBranch_a08_a10_a09_a02_a10, fifthBranch_a08_a10_a09_a02_a11]
    simp
  change
    (haltWritesSafe
      (stepGo
        (stepGo
          (stepGo
            (stepGo
              (stepGo
                (stepGo
                  (stepGo (initial 3) a08)
                  a10)
                a09)
              a08)
            a02)
          a02)
        a10) &&
      actionList.all fifthBranch_a08_a10_a09_a02) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
