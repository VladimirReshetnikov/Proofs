import BusyBeaver.BB3.Certificates.C08.C00
import BusyBeaver.BB3.Certificates.C08.C01
import BusyBeaver.BB3.Certificates.C08.C02
import BusyBeaver.BB3.Certificates.C08.C03
import BusyBeaver.BB3.Certificates.C08.C04
import BusyBeaver.BB3.Certificates.C08.C05
import BusyBeaver.BB3.Certificates.C08.C06
import BusyBeaver.BB3.Certificates.C08.C07
import BusyBeaver.BB3.Certificates.C08.C08
import BusyBeaver.BB3.Certificates.C08.C09
import BusyBeaver.BB3.Certificates.C08.C10
import BusyBeaver.BB3.Certificates.C08.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem firstBranch_a08 : firstBranch a08 = true := by
  have hAll : actionList.all (secondBranch a08) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      secondBranch_a08_a00, secondBranch_a08_a01, secondBranch_a08_a02,
      secondBranch_a08_a03, secondBranch_a08_a04, secondBranch_a08_a05,
      secondBranch_a08_a06, secondBranch_a08_a07, secondBranch_a08_a08,
      secondBranch_a08_a09, secondBranch_a08_a10, secondBranch_a08_a11]
    simp
  change
    (haltWritesSafe (stepGo (initial 3) a08) &&
      actionList.all (secondBranch a08)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
