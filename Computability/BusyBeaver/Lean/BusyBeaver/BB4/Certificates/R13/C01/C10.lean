import BusyBeaver.BB4.Certificates.R13.C01.C10.C00
import BusyBeaver.BB4.Certificates.R13.C01.C10.C01
import BusyBeaver.BB4.Certificates.R13.C01.C10.C02
import BusyBeaver.BB4.Certificates.R13.C01.C10.C03
import BusyBeaver.BB4.Certificates.R13.C01.C10.C04
import BusyBeaver.BB4.Certificates.R13.C01.C10.C05
import BusyBeaver.BB4.Certificates.R13.C01.C10.C06
import BusyBeaver.BB4.Certificates.R13.C01.C10.C07
import BusyBeaver.BB4.Certificates.R13.C01.C10.C08
import BusyBeaver.BB4.Certificates.R13.C01.C10.C09
import BusyBeaver.BB4.Certificates.R13.C01.C10.C10
import BusyBeaver.BB4.Certificates.R13.C01.C10.C11
import BusyBeaver.BB4.Certificates.R13.C01.C10.C12
import BusyBeaver.BB4.Certificates.R13.C01.C10.C13
import BusyBeaver.BB4.Certificates.R13.C01.C10.C14
import BusyBeaver.BB4.Certificates.R13.C01.C10.C15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem thirdBranch_a13_a01_a10 :
    thirdBranch_a13_a01 a10 = true := by
  have hAll : (TNF.canonicalActions 3).all (fourthBranch_a13_a01_a10) = true := by
    rw [canonicalActions_three_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, fourthBranch_a13_a01_a10_a00, fourthBranch_a13_a01_a10_a01, fourthBranch_a13_a01_a10_a02, fourthBranch_a13_a01_a10_a03, fourthBranch_a13_a01_a10_a04, fourthBranch_a13_a01_a10_a05, fourthBranch_a13_a01_a10_a06, fourthBranch_a13_a01_a10_a07, fourthBranch_a13_a01_a10_a08, fourthBranch_a13_a01_a10_a09, fourthBranch_a13_a01_a10_a10, fourthBranch_a13_a01_a10_a11, fourthBranch_a13_a01_a10_a12, fourthBranch_a13_a01_a10_a13, fourthBranch_a13_a01_a10_a14, fourthBranch_a13_a01_a10_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (initial 4) a13) a01) a10) &&
      (TNF.canonicalActions 3).all (fourthBranch_a13_a01_a10)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
