import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C00
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C01
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C02
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C03
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C04
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C05
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C06
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C07
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C08
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C09
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C10
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C11
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C12
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C13
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C14
import BusyBeaver.BB4.Certificates.R13.C01.C08.C02.C15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem fourthBranch_a13_a01_a08_a02 :
    fourthBranch_a13_a01_a08 a02 = true := by
  have hAll : (TNF.canonicalActions 3).all (fifthBranch_a13_a01_a08_a02) = true := by
    rw [canonicalActions_three_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fifthBranch_a13_a01_a08_a02_a00, fifthBranch_a13_a01_a08_a02_a01, fifthBranch_a13_a01_a08_a02_a02, fifthBranch_a13_a01_a08_a02_a03, fifthBranch_a13_a01_a08_a02_a04, fifthBranch_a13_a01_a08_a02_a05, fifthBranch_a13_a01_a08_a02_a06, fifthBranch_a13_a01_a08_a02_a07, fifthBranch_a13_a01_a08_a02_a08, fifthBranch_a13_a01_a08_a02_a09, fifthBranch_a13_a01_a08_a02_a10, fifthBranch_a13_a01_a08_a02_a11, fifthBranch_a13_a01_a08_a02_a12, fifthBranch_a13_a01_a08_a02_a13, fifthBranch_a13_a01_a08_a02_a14, fifthBranch_a13_a01_a08_a02_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a08) a13) a08) a02) &&
      (TNF.canonicalActions 3).all (fifthBranch_a13_a01_a08_a02)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
