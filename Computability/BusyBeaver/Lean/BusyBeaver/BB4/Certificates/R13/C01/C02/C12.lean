import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C00
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C01
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C02
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C03
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C04
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C05
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C06
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C07
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C08
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C09
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C10
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C11
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C12
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C13
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C14
import BusyBeaver.BB4.Certificates.R13.C01.C02.C12.C15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem fourthBranch_a13_a01_a02_a12 :
    fourthBranch_a13_a01_a02 a12 = true := by
  have hAll : (TNF.canonicalActions 3).all (fifthBranch_a13_a01_a02_a12) = true := by
    rw [canonicalActions_three_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fifthBranch_a13_a01_a02_a12_a00, fifthBranch_a13_a01_a02_a12_a01, fifthBranch_a13_a01_a02_a12_a02, fifthBranch_a13_a01_a02_a12_a03, fifthBranch_a13_a01_a02_a12_a04, fifthBranch_a13_a01_a02_a12_a05, fifthBranch_a13_a01_a02_a12_a06, fifthBranch_a13_a01_a02_a12_a07, fifthBranch_a13_a01_a02_a12_a08, fifthBranch_a13_a01_a02_a12_a09, fifthBranch_a13_a01_a02_a12_a10, fifthBranch_a13_a01_a02_a12_a11, fifthBranch_a13_a01_a02_a12_a12, fifthBranch_a13_a01_a02_a12_a13, fifthBranch_a13_a01_a02_a12_a14, fifthBranch_a13_a01_a02_a12_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) a12) a13) a01) a02) &&
      (TNF.canonicalActions 3).all (fifthBranch_a13_a01_a02_a12)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
