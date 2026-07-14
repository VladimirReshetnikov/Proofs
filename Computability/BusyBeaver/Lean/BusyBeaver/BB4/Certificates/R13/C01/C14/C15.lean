import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C00
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C01
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C02
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C03
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C04
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C05
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C06
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C07
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C08
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C09
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C10
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C11
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C12
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C13
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C14
import BusyBeaver.BB4.Certificates.R13.C01.C14.C15.C15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem fourthBranch_a13_a01_a14_a15 :
    fourthBranch_a13_a01_a14 a15 = true := by
  have hAll : (TNF.canonicalActions 4).all (fifthBranch_a13_a01_a14_a15) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fifthBranch_a13_a01_a14_a15_a00, fifthBranch_a13_a01_a14_a15_a01, fifthBranch_a13_a01_a14_a15_a02, fifthBranch_a13_a01_a14_a15_a03, fifthBranch_a13_a01_a14_a15_a04, fifthBranch_a13_a01_a14_a15_a05, fifthBranch_a13_a01_a14_a15_a06, fifthBranch_a13_a01_a14_a15_a07, fifthBranch_a13_a01_a14_a15_a08, fifthBranch_a13_a01_a14_a15_a09, fifthBranch_a13_a01_a14_a15_a10, fifthBranch_a13_a01_a14_a15_a11, fifthBranch_a13_a01_a14_a15_a12, fifthBranch_a13_a01_a14_a15_a13, fifthBranch_a13_a01_a14_a15_a14, fifthBranch_a13_a01_a14_a15_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a14) a15) &&
      (TNF.canonicalActions 4).all (fifthBranch_a13_a01_a14_a15)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
