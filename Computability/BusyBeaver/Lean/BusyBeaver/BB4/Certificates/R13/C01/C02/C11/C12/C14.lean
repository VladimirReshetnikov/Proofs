import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C00
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C01
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C02
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C03
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C04
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C05
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C06
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C07
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C08
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C09
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C10
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C11
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C12
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C13
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C14
import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C12.C14.C15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem sixthBranch_a13_a01_a02_a11_a12_a14 :
    sixthBranch_a13_a01_a02_a11_a12 a14 = true := by
  have hAll : (TNF.canonicalActions 4).all (seventhBranch_a13_a01_a02_a11_a12_a14) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, seventhBranch_a13_a01_a02_a11_a12_a14_a00, seventhBranch_a13_a01_a02_a11_a12_a14_a01, seventhBranch_a13_a01_a02_a11_a12_a14_a02, seventhBranch_a13_a01_a02_a11_a12_a14_a03, seventhBranch_a13_a01_a02_a11_a12_a14_a04, seventhBranch_a13_a01_a02_a11_a12_a14_a05, seventhBranch_a13_a01_a02_a11_a12_a14_a06, seventhBranch_a13_a01_a02_a11_a12_a14_a07, seventhBranch_a13_a01_a02_a11_a12_a14_a08, seventhBranch_a13_a01_a02_a11_a12_a14_a09, seventhBranch_a13_a01_a02_a11_a12_a14_a10, seventhBranch_a13_a01_a02_a11_a12_a14_a11, seventhBranch_a13_a01_a02_a11_a12_a14_a12, seventhBranch_a13_a01_a02_a11_a12_a14_a13, seventhBranch_a13_a01_a02_a11_a12_a14_a14, seventhBranch_a13_a01_a02_a11_a12_a14_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) a11) a12) a14) a11) &&
      (TNF.canonicalActions 4).all (seventhBranch_a13_a01_a02_a11_a12_a14)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
