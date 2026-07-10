import SetTheory.BusyBeaverBB3.Certificates.C11.C06.C03
import SetTheory.BusyBeaverBB3.Certificates.C11.C06.C04
import SetTheory.BusyBeaverBB3.Certificates.C11.C06.C05
import SetTheory.BusyBeaverBB3.Certificates.C11.C06.C00
import SetTheory.BusyBeaverBB3.Certificates.C11.C06.C01
import SetTheory.BusyBeaverBB3.Certificates.C11.C06.C02
import SetTheory.BusyBeaverBB3.Certificates.C11.C06.C09
import SetTheory.BusyBeaverBB3.Certificates.C11.C06.C10
import SetTheory.BusyBeaverBB3.Certificates.C11.C06.C11
import SetTheory.BusyBeaverBB3.Certificates.C11.C06.C06
import SetTheory.BusyBeaverBB3.Certificates.C11.C06.C07
import SetTheory.BusyBeaverBB3.Certificates.C11.C06.C08

namespace SetTheory.BusyBeaver.BB3.Certificates


theorem secondBranch_a11_a06 : secondBranch a11 a06 = true := by
  have hAll : actionList.all (thirdMarkedBranch a11 a06) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, thirdMarkedBranch_a11_a06_a03, thirdMarkedBranch_a11_a06_a04, thirdMarkedBranch_a11_a06_a05, thirdMarkedBranch_a11_a06_a00, thirdMarkedBranch_a11_a06_a01, thirdMarkedBranch_a11_a06_a02, thirdMarkedBranch_a11_a06_a09, thirdMarkedBranch_a11_a06_a10, thirdMarkedBranch_a11_a06_a11, thirdMarkedBranch_a11_a06_a06, thirdMarkedBranch_a11_a06_a07, thirdMarkedBranch_a11_a06_a08]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a11) a06) &&
      actionList.all (thirdMarkedBranch a11 a06)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates

