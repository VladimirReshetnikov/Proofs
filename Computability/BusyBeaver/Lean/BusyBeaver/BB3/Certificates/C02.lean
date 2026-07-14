import BusyBeaver.BB3.Certificates.C02.C00
import BusyBeaver.BB3.Certificates.C02.C01
import BusyBeaver.BB3.Certificates.C02.C02
import BusyBeaver.BB3.Certificates.C02.C03
import BusyBeaver.BB3.Certificates.C02.C04
import BusyBeaver.BB3.Certificates.C02.C05
import BusyBeaver.BB3.Certificates.C02.C06
import BusyBeaver.BB3.Certificates.C02.C07
import BusyBeaver.BB3.Certificates.C02.C08
import BusyBeaver.BB3.Certificates.C02.C09
import BusyBeaver.BB3.Certificates.C02.C10
import BusyBeaver.BB3.Certificates.C02.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem firstBranch_a02 : firstBranch a02 = true := by
  have hAll : actionList.all (secondBranch a02) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, secondBranch_a02_a00, secondBranch_a02_a01, secondBranch_a02_a02, secondBranch_a02_a03, secondBranch_a02_a04, secondBranch_a02_a05, secondBranch_a02_a06, secondBranch_a02_a07, secondBranch_a02_a08, secondBranch_a02_a09, secondBranch_a02_a10, secondBranch_a02_a11]
    simp
  change
    (haltWritesSafe (stepGo (initial 3) a02) &&
      actionList.all (secondBranch a02)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
