import SetTheory.BusyBeaverBB3.Certificates.C11.C03
import SetTheory.BusyBeaverBB3.Certificates.C11.C04
import SetTheory.BusyBeaverBB3.Certificates.C11.C05
import SetTheory.BusyBeaverBB3.Certificates.C11.C00
import SetTheory.BusyBeaverBB3.Certificates.C11.C01
import SetTheory.BusyBeaverBB3.Certificates.C11.C02
import SetTheory.BusyBeaverBB3.Certificates.C11.C09
import SetTheory.BusyBeaverBB3.Certificates.C11.C10
import SetTheory.BusyBeaverBB3.Certificates.C11.C11
import SetTheory.BusyBeaverBB3.Certificates.C11.C06
import SetTheory.BusyBeaverBB3.Certificates.C11.C07
import SetTheory.BusyBeaverBB3.Certificates.C11.C08

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem firstBranch_a11 : firstBranch a11 = true := by
  have hAll : actionList.all (secondBranch a11) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      secondBranch_a11_a03, secondBranch_a11_a04, secondBranch_a11_a05,
      secondBranch_a11_a00, secondBranch_a11_a01, secondBranch_a11_a02,
      secondBranch_a11_a09, secondBranch_a11_a10, secondBranch_a11_a11,
      secondBranch_a11_a06, secondBranch_a11_a07, secondBranch_a11_a08]
    simp
  change
    (haltWritesSafe (stepGo (initial 3) a11) &&
      actionList.all (secondBranch a11)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates

