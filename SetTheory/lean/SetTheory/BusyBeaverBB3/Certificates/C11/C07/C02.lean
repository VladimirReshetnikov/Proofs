import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C02.C00
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C02.C01
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C02.C02
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C02.C03
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C02.C04
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C02.C05
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C02.C06
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C02.C07
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C02.C08
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C02.C09
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C02.C10
import SetTheory.BusyBeaverBB3.Certificates.C11.C07.C02.C11

namespace SetTheory.BusyBeaver.BB3.Certificates

theorem thirdMarkedBranch_a11_a07_a02 :
    thirdMarkedBranch a11 a07 a02 = true := by
  have hAll : actionList.all fourthBranch_a11_a07_a02 = true := by
    rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranch_a11_a07_a02_a00, fourthBranch_a11_a07_a02_a01, fourthBranch_a11_a07_a02_a02, fourthBranch_a11_a07_a02_a03, fourthBranch_a11_a07_a02_a04, fourthBranch_a11_a07_a02_a05, fourthBranch_a11_a07_a02_a06, fourthBranch_a11_a07_a02_a07, fourthBranch_a11_a07_a02_a08, fourthBranch_a11_a07_a02_a09, fourthBranch_a11_a07_a02_a10, fourthBranch_a11_a07_a02_a11]
    simp
  change
    (haltWritesSafe
      (stepGo (stepGo (stepGo (stepGo (initial 3) a11) a07) a02) a07) &&
      actionList.all fourthBranch_a11_a07_a02) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB3.Certificates
