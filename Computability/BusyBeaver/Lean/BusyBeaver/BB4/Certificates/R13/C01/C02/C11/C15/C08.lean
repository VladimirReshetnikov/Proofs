import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C00
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C01
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C02
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C03
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C04
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C05
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C06
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C07
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C08
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C09
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C10
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C11
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C12
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C13
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C14
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C15.C08.C15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem sixthBranch_a13_a01_a02_a11_a15_a08 :
    sixthBranch_a13_a01_a02_a11_a15 a08 = true := by
  have hAll : (TNF.canonicalActions 4).all (seventhBranch_a13_a01_a02_a11_a15_a08) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, seventhBranch_a13_a01_a02_a11_a15_a08_a00, seventhBranch_a13_a01_a02_a11_a15_a08_a01, seventhBranch_a13_a01_a02_a11_a15_a08_a02, seventhBranch_a13_a01_a02_a11_a15_a08_a03, seventhBranch_a13_a01_a02_a11_a15_a08_a04, seventhBranch_a13_a01_a02_a11_a15_a08_a05, seventhBranch_a13_a01_a02_a11_a15_a08_a06, seventhBranch_a13_a01_a02_a11_a15_a08_a07, seventhBranch_a13_a01_a02_a11_a15_a08_a08, seventhBranch_a13_a01_a02_a11_a15_a08_a09, seventhBranch_a13_a01_a02_a11_a15_a08_a10, seventhBranch_a13_a01_a02_a11_a15_a08_a11, seventhBranch_a13_a01_a02_a11_a15_a08_a12, seventhBranch_a13_a01_a02_a11_a15_a08_a13, seventhBranch_a13_a01_a02_a11_a15_a08_a14, seventhBranch_a13_a01_a02_a11_a15_a08_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) a11) a15) a08) &&
      (TNF.canonicalActions 4).all (seventhBranch_a13_a01_a02_a11_a15_a08)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
