import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C00
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C01
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C02
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C03
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C04
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C05
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C06
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C07
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C08
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C09
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C10
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C11
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C12
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C13
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C14
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.C15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem fifthBranch_a13_a01_a02_a11_a04 :
    fifthBranch_a13_a01_a02_a11 a04 = true := by
  have hAll : (TNF.canonicalActions 4).all (sixthBranch_a13_a01_a02_a11_a04) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, sixthBranch_a13_a01_a02_a11_a04_a00, sixthBranch_a13_a01_a02_a11_a04_a01, sixthBranch_a13_a01_a02_a11_a04_a02, sixthBranch_a13_a01_a02_a11_a04_a03, sixthBranch_a13_a01_a02_a11_a04_a04, sixthBranch_a13_a01_a02_a11_a04_a05, sixthBranch_a13_a01_a02_a11_a04_a06, sixthBranch_a13_a01_a02_a11_a04_a07, sixthBranch_a13_a01_a02_a11_a04_a08, sixthBranch_a13_a01_a02_a11_a04_a09, sixthBranch_a13_a01_a02_a11_a04_a10, sixthBranch_a13_a01_a02_a11_a04_a11, sixthBranch_a13_a01_a02_a11_a04_a12, sixthBranch_a13_a01_a02_a11_a04_a13, sixthBranch_a13_a01_a02_a11_a04_a14, sixthBranch_a13_a01_a02_a11_a04_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) a11) a04) &&
      (TNF.canonicalActions 4).all (sixthBranch_a13_a01_a02_a11_a04)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
