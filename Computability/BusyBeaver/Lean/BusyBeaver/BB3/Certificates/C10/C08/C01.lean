import BusyBeaver.BB3.Certificates.C10.C08.C01.C00
import BusyBeaver.BB3.Certificates.C10.C08.C01.C01
import BusyBeaver.BB3.Certificates.C10.C08.C01.C02
import BusyBeaver.BB3.Certificates.C10.C08.C01.C03
import BusyBeaver.BB3.Certificates.C10.C08.C01.C04
import BusyBeaver.BB3.Certificates.C10.C08.C01.C05
import BusyBeaver.BB3.Certificates.C10.C08.C01.C06
import BusyBeaver.BB3.Certificates.C10.C08.C01.C07
import BusyBeaver.BB3.Certificates.C10.C08.C01.C08
import BusyBeaver.BB3.Certificates.C10.C08.C01.C09
import BusyBeaver.BB3.Certificates.C10.C08.C01.C10
import BusyBeaver.BB3.Certificates.C10.C08.C01.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem thirdMarkedBranch_a10_a08_a01 :
    thirdMarkedBranch a10 a08 a01 = true := by
  have hAll : actionList.all fourthBranch_a10_a08_a01 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranch_a10_a08_a01_a00, fourthBranch_a10_a08_a01_a01, fourthBranch_a10_a08_a01_a02, fourthBranch_a10_a08_a01_a03, fourthBranch_a10_a08_a01_a04, fourthBranch_a10_a08_a01_a05, fourthBranch_a10_a08_a01_a06, fourthBranch_a10_a08_a01_a07, fourthBranch_a10_a08_a01_a08, fourthBranch_a10_a08_a01_a09, fourthBranch_a10_a08_a01_a10, fourthBranch_a10_a08_a01_a11]
    simp
  change
    (haltWritesSafe
      (stepGo
        (stepGo
          (stepGo (stepGo (initial 3) a10) a08)
          a01)
        a08) &&
      actionList.all fourthBranch_a10_a08_a01) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
