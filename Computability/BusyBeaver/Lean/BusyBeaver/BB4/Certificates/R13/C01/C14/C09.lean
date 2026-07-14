import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C00
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C01
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C02
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C03
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C04
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C05
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C06
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C07
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C08
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C09
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C10
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C11
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C12
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C13
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C14
import BusyBeaver.BB4.Certificates.R13.C01.C14.C09.C15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem fourthBranch_a13_a01_a14_a09 :
    fourthBranch_a13_a01_a14 a09 = true := by
  have hAll : (TNF.canonicalActions 3).all (fifthBranch_a13_a01_a14_a09) = true := by
    rw [canonicalActions_three_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fifthBranch_a13_a01_a14_a09_a00, fifthBranch_a13_a01_a14_a09_a01, fifthBranch_a13_a01_a14_a09_a02, fifthBranch_a13_a01_a14_a09_a03, fifthBranch_a13_a01_a14_a09_a04, fifthBranch_a13_a01_a14_a09_a05, fifthBranch_a13_a01_a14_a09_a06, fifthBranch_a13_a01_a14_a09_a07, fifthBranch_a13_a01_a14_a09_a08, fifthBranch_a13_a01_a14_a09_a09, fifthBranch_a13_a01_a14_a09_a10, fifthBranch_a13_a01_a14_a09_a11, fifthBranch_a13_a01_a14_a09_a12, fifthBranch_a13_a01_a14_a09_a13, fifthBranch_a13_a01_a14_a09_a14, fifthBranch_a13_a01_a14_a09_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a14) a09) a14) &&
      (TNF.canonicalActions 3).all (fifthBranch_a13_a01_a14_a09)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
