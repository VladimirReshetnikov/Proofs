import SetTheory.BusyBeaverBB3.Certificates.C10.C02.C00
import SetTheory.BusyBeaverBB3.Certificates.C10.C02.C01
import SetTheory.BusyBeaverBB3.Certificates.C10.C02.C02
import SetTheory.BusyBeaverBB3.Certificates.C10.C02.C03
import SetTheory.BusyBeaverBB3.Certificates.C10.C02.C04
import SetTheory.BusyBeaverBB3.Certificates.C10.C02.C05
import SetTheory.BusyBeaverBB3.Certificates.C10.C02.C06
import SetTheory.BusyBeaverBB3.Certificates.C10.C02.C07
import SetTheory.BusyBeaverBB3.Certificates.C10.C02.C08
import SetTheory.BusyBeaverBB3.Certificates.C10.C02.C09
import SetTheory.BusyBeaverBB3.Certificates.C10.C02.C10
import SetTheory.BusyBeaverBB3.Certificates.C10.C02.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem secondBranch_a10_a02 : secondBranch a10 a02 = true := by
  have hAll : actionList.all (thirdMarkedBranch a10 a02) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      thirdMarkedBranch_a10_a02_a00, thirdMarkedBranch_a10_a02_a01, thirdMarkedBranch_a10_a02_a02, thirdMarkedBranch_a10_a02_a03, thirdMarkedBranch_a10_a02_a04, thirdMarkedBranch_a10_a02_a05, thirdMarkedBranch_a10_a02_a06, thirdMarkedBranch_a10_a02_a07, thirdMarkedBranch_a10_a02_a08, thirdMarkedBranch_a10_a02_a09, thirdMarkedBranch_a10_a02_a10, thirdMarkedBranch_a10_a02_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a10) a02) &&
      actionList.all (thirdMarkedBranch a10 a02)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
