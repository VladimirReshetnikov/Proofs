import BusyBeaver.BB3.Certificates.C07.C00
import BusyBeaver.BB3.Certificates.C07.C01
import BusyBeaver.BB3.Certificates.C07.C02
import BusyBeaver.BB3.Certificates.C07.C03
import BusyBeaver.BB3.Certificates.C07.C04
import BusyBeaver.BB3.Certificates.C07.C05
import BusyBeaver.BB3.Certificates.C07.C06
import BusyBeaver.BB3.Certificates.C07.C07
import BusyBeaver.BB3.Certificates.C07.C08
import BusyBeaver.BB3.Certificates.C07.C09
import BusyBeaver.BB3.Certificates.C07.C10
import BusyBeaver.BB3.Certificates.C07.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem firstBranch_a07 : firstBranch a07 = true := by
  have hAll : actionList.all (secondBranch a07) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, secondBranch_a07_a00, secondBranch_a07_a01, secondBranch_a07_a02, secondBranch_a07_a03, secondBranch_a07_a04, secondBranch_a07_a05, secondBranch_a07_a06, secondBranch_a07_a07, secondBranch_a07_a08, secondBranch_a07_a09, secondBranch_a07_a10, secondBranch_a07_a11]
    simp
  change
    (haltWritesSafe (stepGo (initial 3) a07) &&
      actionList.all (secondBranch a07)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
