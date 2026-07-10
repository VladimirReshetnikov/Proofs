import SetTheory.BusyBeaverBB3.Certificates.C10.C08.C00
import SetTheory.BusyBeaverBB3.Certificates.C10.C08.C01
import SetTheory.BusyBeaverBB3.Certificates.C10.C08.C02
import SetTheory.BusyBeaverBB3.Certificates.C10.C08.C03
import SetTheory.BusyBeaverBB3.Certificates.C10.C08.C04
import SetTheory.BusyBeaverBB3.Certificates.C10.C08.C05
import SetTheory.BusyBeaverBB3.Certificates.C10.C08.C06
import SetTheory.BusyBeaverBB3.Certificates.C10.C08.C07
import SetTheory.BusyBeaverBB3.Certificates.C10.C08.C08
import SetTheory.BusyBeaverBB3.Certificates.C10.C08.C09
import SetTheory.BusyBeaverBB3.Certificates.C10.C08.C10
import SetTheory.BusyBeaverBB3.Certificates.C10.C08.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem secondBranch_a10_a08 : secondBranch a10 a08 = true := by
  have hAll : actionList.all (thirdMarkedBranch a10 a08) = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      thirdMarkedBranch_a10_a08_a00, thirdMarkedBranch_a10_a08_a01, thirdMarkedBranch_a10_a08_a02, thirdMarkedBranch_a10_a08_a03, thirdMarkedBranch_a10_a08_a04, thirdMarkedBranch_a10_a08_a05, thirdMarkedBranch_a10_a08_a06, thirdMarkedBranch_a10_a08_a07, thirdMarkedBranch_a10_a08_a08, thirdMarkedBranch_a10_a08_a09, thirdMarkedBranch_a10_a08_a10, thirdMarkedBranch_a10_a08_a11]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 3) a10) a08) &&
      actionList.all (thirdMarkedBranch a10 a08)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
