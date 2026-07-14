import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C00
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C01
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C02
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C03
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C04
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C05
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C06
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C07
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C08
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C09
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C10
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C11
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C12
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C13
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C14
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C07.C15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem sixthBranch_a13_a01_a02_a11_a12_a07 :
    sixthBranch_a13_a01_a02_a11_a12 a07 = true := by
  have hAll : (TNF.canonicalActions 4).all (seventhBranch_a13_a01_a02_a11_a12_a07) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, seventhBranch_a13_a01_a02_a11_a12_a07_a00, seventhBranch_a13_a01_a02_a11_a12_a07_a01, seventhBranch_a13_a01_a02_a11_a12_a07_a02, seventhBranch_a13_a01_a02_a11_a12_a07_a03, seventhBranch_a13_a01_a02_a11_a12_a07_a04, seventhBranch_a13_a01_a02_a11_a12_a07_a05, seventhBranch_a13_a01_a02_a11_a12_a07_a06, seventhBranch_a13_a01_a02_a11_a12_a07_a07, seventhBranch_a13_a01_a02_a11_a12_a07_a08, seventhBranch_a13_a01_a02_a11_a12_a07_a09, seventhBranch_a13_a01_a02_a11_a12_a07_a10, seventhBranch_a13_a01_a02_a11_a12_a07_a11, seventhBranch_a13_a01_a02_a11_a12_a07_a12, seventhBranch_a13_a01_a02_a11_a12_a07_a13, seventhBranch_a13_a01_a02_a11_a12_a07_a14, seventhBranch_a13_a01_a02_a11_a12_a07_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) a11) a12) a07) a12) a13) a01) a02) &&
      (TNF.canonicalActions 4).all (seventhBranch_a13_a01_a02_a11_a12_a07)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
