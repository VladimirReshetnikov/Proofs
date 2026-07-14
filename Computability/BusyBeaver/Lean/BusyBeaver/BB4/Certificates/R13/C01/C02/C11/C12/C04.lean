import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C00
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C01
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C02
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C03
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C04
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C05
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C06
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C07
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C08
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C09
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C10
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C11
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C12
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C13
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C14
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C04.C15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem sixthBranch_a13_a01_a02_a11_a12_a04 :
    sixthBranch_a13_a01_a02_a11_a12 a04 = true := by
  have hAll : (TNF.canonicalActions 4).all (seventhBranch_a13_a01_a02_a11_a12_a04) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, seventhBranch_a13_a01_a02_a11_a12_a04_a00, seventhBranch_a13_a01_a02_a11_a12_a04_a01, seventhBranch_a13_a01_a02_a11_a12_a04_a02, seventhBranch_a13_a01_a02_a11_a12_a04_a03, seventhBranch_a13_a01_a02_a11_a12_a04_a04, seventhBranch_a13_a01_a02_a11_a12_a04_a05, seventhBranch_a13_a01_a02_a11_a12_a04_a06, seventhBranch_a13_a01_a02_a11_a12_a04_a07, seventhBranch_a13_a01_a02_a11_a12_a04_a08, seventhBranch_a13_a01_a02_a11_a12_a04_a09, seventhBranch_a13_a01_a02_a11_a12_a04_a10, seventhBranch_a13_a01_a02_a11_a12_a04_a11, seventhBranch_a13_a01_a02_a11_a12_a04_a12, seventhBranch_a13_a01_a02_a11_a12_a04_a13, seventhBranch_a13_a01_a02_a11_a12_a04_a14, seventhBranch_a13_a01_a02_a11_a12_a04_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) a11) a12) a04) a13) a01) a02) a11) &&
      (TNF.canonicalActions 4).all (seventhBranch_a13_a01_a02_a11_a12_a04)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
