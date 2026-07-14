import BusyBeaver.BB3.Certificates.C10.C00
import BusyBeaver.BB3.Certificates.C10.C01
import BusyBeaver.BB3.Certificates.C10.C02
import BusyBeaver.BB3.Certificates.C10.C03
import BusyBeaver.BB3.Certificates.C10.C04
import BusyBeaver.BB3.Certificates.C10.C05
import BusyBeaver.BB3.Certificates.C10.C06
import BusyBeaver.BB3.Certificates.C10.C07
import BusyBeaver.BB3.Certificates.C10.C08
import BusyBeaver.BB3.Certificates.C10.C09
import BusyBeaver.BB3.Certificates.C10.C10
import BusyBeaver.BB3.Certificates.C10.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem firstBranch_a10 : firstBranch a10 = true := by
  have hAll : actionList.all (secondBranch a10) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      secondBranch_a10_a00, secondBranch_a10_a01, secondBranch_a10_a02,
      secondBranch_a10_a03, secondBranch_a10_a04, secondBranch_a10_a05,
      secondBranch_a10_a06, secondBranch_a10_a07, secondBranch_a10_a08,
      secondBranch_a10_a09, secondBranch_a10_a10, secondBranch_a10_a11]
    simp
  change
    (haltWritesSafe (stepGo (initial 3) a10) &&
      actionList.all (secondBranch a10)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
