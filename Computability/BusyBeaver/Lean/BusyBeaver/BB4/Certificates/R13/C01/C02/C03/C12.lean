import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C00
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C01
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C02
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C03
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C04
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C05
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C06
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C07
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C08
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C09
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C10
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C11
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C12
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C13
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C14
import BusyBeaver.BB4.Certificates.R13.C01.C02.C03.C12.C15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem fifthBranch_a13_a01_a02_a03_a12 :
    fifthBranch_a13_a01_a02_a03 a12 = true := by
  have hAll : (TNF.canonicalActions 4).all (sixthBranch_a13_a01_a02_a03_a12) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, sixthBranch_a13_a01_a02_a03_a12_a00, sixthBranch_a13_a01_a02_a03_a12_a01, sixthBranch_a13_a01_a02_a03_a12_a02, sixthBranch_a13_a01_a02_a03_a12_a03, sixthBranch_a13_a01_a02_a03_a12_a04, sixthBranch_a13_a01_a02_a03_a12_a05, sixthBranch_a13_a01_a02_a03_a12_a06, sixthBranch_a13_a01_a02_a03_a12_a07, sixthBranch_a13_a01_a02_a03_a12_a08, sixthBranch_a13_a01_a02_a03_a12_a09, sixthBranch_a13_a01_a02_a03_a12_a10, sixthBranch_a13_a01_a02_a03_a12_a11, sixthBranch_a13_a01_a02_a03_a12_a12, sixthBranch_a13_a01_a02_a03_a12_a13, sixthBranch_a13_a01_a02_a03_a12_a14, sixthBranch_a13_a01_a02_a03_a12_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) a03) a12) a13) a01) a02) &&
      (TNF.canonicalActions 4).all (sixthBranch_a13_a01_a02_a03_a12)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
