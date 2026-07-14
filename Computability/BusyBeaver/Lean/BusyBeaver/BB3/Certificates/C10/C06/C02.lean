import BusyBeaver.BB3.Certificates.C10.C06.C02.C00
import BusyBeaver.BB3.Certificates.C10.C06.C02.C01
import BusyBeaver.BB3.Certificates.C10.C06.C02.C02
import BusyBeaver.BB3.Certificates.C10.C06.C02.C03
import BusyBeaver.BB3.Certificates.C10.C06.C02.C04
import BusyBeaver.BB3.Certificates.C10.C06.C02.C05
import BusyBeaver.BB3.Certificates.C10.C06.C02.C06
import BusyBeaver.BB3.Certificates.C10.C06.C02.C07
import BusyBeaver.BB3.Certificates.C10.C06.C02.C08
import BusyBeaver.BB3.Certificates.C10.C06.C02.C09
import BusyBeaver.BB3.Certificates.C10.C06.C02.C10
import BusyBeaver.BB3.Certificates.C10.C06.C02.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem thirdMarkedBranch_a10_a06_a02 :
    thirdMarkedBranch a10 a06 a02 = true := by
  have hAll : actionList.all fourthBranch_a10_a06_a02 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranch_a10_a06_a02_a00, fourthBranch_a10_a06_a02_a01, fourthBranch_a10_a06_a02_a02, fourthBranch_a10_a06_a02_a03, fourthBranch_a10_a06_a02_a04, fourthBranch_a10_a06_a02_a05, fourthBranch_a10_a06_a02_a06, fourthBranch_a10_a06_a02_a07, fourthBranch_a10_a06_a02_a08, fourthBranch_a10_a06_a02_a09, fourthBranch_a10_a06_a02_a10, fourthBranch_a10_a06_a02_a11]
    simp
  change
    (haltWritesSafe
      (stepGo
        (stepGo (stepGo (initial 3) a10) a06)
        a02) &&
      actionList.all fourthBranch_a10_a06_a02) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
