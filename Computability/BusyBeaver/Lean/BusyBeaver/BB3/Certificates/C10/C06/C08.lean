import BusyBeaver.BB3.Certificates.C10.C06.C08.C00
import BusyBeaver.BB3.Certificates.C10.C06.C08.C01
import BusyBeaver.BB3.Certificates.C10.C06.C08.C02
import BusyBeaver.BB3.Certificates.C10.C06.C08.C03
import BusyBeaver.BB3.Certificates.C10.C06.C08.C04
import BusyBeaver.BB3.Certificates.C10.C06.C08.C05
import BusyBeaver.BB3.Certificates.C10.C06.C08.C06
import BusyBeaver.BB3.Certificates.C10.C06.C08.C07
import BusyBeaver.BB3.Certificates.C10.C06.C08.C08
import BusyBeaver.BB3.Certificates.C10.C06.C08.C09
import BusyBeaver.BB3.Certificates.C10.C06.C08.C10
import BusyBeaver.BB3.Certificates.C10.C06.C08.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem thirdMarkedBranch_a10_a06_a08 :
    thirdMarkedBranch a10 a06 a08 = true := by
  have hAll : actionList.all fourthBranch_a10_a06_a08 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranch_a10_a06_a08_a00, fourthBranch_a10_a06_a08_a01, fourthBranch_a10_a06_a08_a02, fourthBranch_a10_a06_a08_a03, fourthBranch_a10_a06_a08_a04, fourthBranch_a10_a06_a08_a05, fourthBranch_a10_a06_a08_a06, fourthBranch_a10_a06_a08_a07, fourthBranch_a10_a06_a08_a08, fourthBranch_a10_a06_a08_a09, fourthBranch_a10_a06_a08_a10, fourthBranch_a10_a06_a08_a11]
    simp
  change
    (haltWritesSafe
      (stepGo (stepGo (stepGo (initial 3) a10) a06) a08) &&
      actionList.all fourthBranch_a10_a06_a08) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
