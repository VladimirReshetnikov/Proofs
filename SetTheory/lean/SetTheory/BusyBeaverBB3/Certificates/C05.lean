import SetTheory.BusyBeaverBB3.Certificates.C05.C00
import SetTheory.BusyBeaverBB3.Certificates.C05.C01
import SetTheory.BusyBeaverBB3.Certificates.C05.C02
import SetTheory.BusyBeaverBB3.Certificates.C05.C03
import SetTheory.BusyBeaverBB3.Certificates.C05.C04
import SetTheory.BusyBeaverBB3.Certificates.C05.C05
import SetTheory.BusyBeaverBB3.Certificates.C05.C06
import SetTheory.BusyBeaverBB3.Certificates.C05.C07
import SetTheory.BusyBeaverBB3.Certificates.C05.C08
import SetTheory.BusyBeaverBB3.Certificates.C05.C09
import SetTheory.BusyBeaverBB3.Certificates.C05.C10
import SetTheory.BusyBeaverBB3.Certificates.C05.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem firstBranch_a05 : firstBranch a05 = true := by
  have hAll : actionList.all (secondBranch a05) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, secondBranch_a05_a00, secondBranch_a05_a01, secondBranch_a05_a02, secondBranch_a05_a03, secondBranch_a05_a04, secondBranch_a05_a05, secondBranch_a05_a06, secondBranch_a05_a07, secondBranch_a05_a08, secondBranch_a05_a09, secondBranch_a05_a10, secondBranch_a05_a11]
    simp
  change
    (haltWritesSafe (stepGo (initial 3) a05) &&
      actionList.all (secondBranch a05)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
