import BusyBeaver.BB3.Certificates.C04.C00
import BusyBeaver.BB3.Certificates.C04.C01
import BusyBeaver.BB3.Certificates.C04.C02
import BusyBeaver.BB3.Certificates.C04.C03
import BusyBeaver.BB3.Certificates.C04.C04
import BusyBeaver.BB3.Certificates.C04.C05
import BusyBeaver.BB3.Certificates.C04.C06
import BusyBeaver.BB3.Certificates.C04.C07
import BusyBeaver.BB3.Certificates.C04.C08
import BusyBeaver.BB3.Certificates.C04.C09
import BusyBeaver.BB3.Certificates.C04.C10
import BusyBeaver.BB3.Certificates.C04.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem firstBranch_a04 : firstBranch a04 = true := by
  have hAll : actionList.all (secondBranch a04) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, secondBranch_a04_a00, secondBranch_a04_a01, secondBranch_a04_a02, secondBranch_a04_a03, secondBranch_a04_a04, secondBranch_a04_a05, secondBranch_a04_a06, secondBranch_a04_a07, secondBranch_a04_a08, secondBranch_a04_a09, secondBranch_a04_a10, secondBranch_a04_a11]
    simp
  change
    (haltWritesSafe (stepGo (initial 3) a04) &&
      actionList.all (secondBranch a04)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
