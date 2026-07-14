import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C00
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C01
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C02
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C03
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C04
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C05
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C06
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C07
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C08
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C09
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C10
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C11
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C12
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C13
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C14
import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.C09.C15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem sixthBranch_a13_a01_a02_a15_a12_a09 :
    sixthBranch_a13_a01_a02_a15_a12 a09 = true := by
  have hAll : (TNF.canonicalActions 4).all (seventhBranch_a13_a01_a02_a15_a12_a09) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, seventhBranch_a13_a01_a02_a15_a12_a09_a00, seventhBranch_a13_a01_a02_a15_a12_a09_a01, seventhBranch_a13_a01_a02_a15_a12_a09_a02, seventhBranch_a13_a01_a02_a15_a12_a09_a03, seventhBranch_a13_a01_a02_a15_a12_a09_a04, seventhBranch_a13_a01_a02_a15_a12_a09_a05, seventhBranch_a13_a01_a02_a15_a12_a09_a06, seventhBranch_a13_a01_a02_a15_a12_a09_a07, seventhBranch_a13_a01_a02_a15_a12_a09_a08, seventhBranch_a13_a01_a02_a15_a12_a09_a09, seventhBranch_a13_a01_a02_a15_a12_a09_a10, seventhBranch_a13_a01_a02_a15_a12_a09_a11, seventhBranch_a13_a01_a02_a15_a12_a09_a12, seventhBranch_a13_a01_a02_a15_a12_a09_a13, seventhBranch_a13_a01_a02_a15_a12_a09_a14, seventhBranch_a13_a01_a02_a15_a12_a09_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) a15) a12) a13) a01) a02) a09) a02) a15) a12) &&
      (TNF.canonicalActions 4).all (seventhBranch_a13_a01_a02_a15_a12_a09)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
