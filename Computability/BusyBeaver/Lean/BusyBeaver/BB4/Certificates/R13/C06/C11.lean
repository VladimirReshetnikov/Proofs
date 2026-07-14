import BusyBeaver.BB4.Certificates.R13.C06.C11.A00
import BusyBeaver.BB4.Certificates.R13.C06.C11.A01
import BusyBeaver.BB4.Certificates.R13.C06.C11.A02
import BusyBeaver.BB4.Certificates.R13.C06.C11.A03
import BusyBeaver.BB4.Certificates.R13.C06.C11.A04
import BusyBeaver.BB4.Certificates.R13.C06.C11.A05
import BusyBeaver.BB4.Certificates.R13.C06.C11.A06
import BusyBeaver.BB4.Certificates.R13.C06.C11.A07
import BusyBeaver.BB4.Certificates.R13.C06.C11.A08
import BusyBeaver.BB4.Certificates.R13.C06.C11.A09
import BusyBeaver.BB4.Certificates.R13.C06.C11.A10
import BusyBeaver.BB4.Certificates.R13.C06.C11.A11
import BusyBeaver.BB4.Certificates.R13.C06.C11.A12
import BusyBeaver.BB4.Certificates.R13.C06.C11.A13
import BusyBeaver.BB4.Certificates.R13.C06.C11.A14
import BusyBeaver.BB4.Certificates.R13.C06.C11.A15

import BusyBeaver.BB4.Certificates.R13.C06.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem thirdBranch_a13_a06_a11 :
    thirdBranch_a13_a06 a11 = true := by
  have hAll :
      (TNF.canonicalActions 4).all (fourthBranch_a13_a06_a11) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fourthBranch_a13_a06_a11_a00, fourthBranch_a13_a06_a11_a01,
      fourthBranch_a13_a06_a11_a02, fourthBranch_a13_a06_a11_a03,
      fourthBranch_a13_a06_a11_a04, fourthBranch_a13_a06_a11_a05,
      fourthBranch_a13_a06_a11_a06, fourthBranch_a13_a06_a11_a07,
      fourthBranch_a13_a06_a11_a08, fourthBranch_a13_a06_a11_a09,
      fourthBranch_a13_a06_a11_a10, fourthBranch_a13_a06_a11_a11,
      fourthBranch_a13_a06_a11_a12, fourthBranch_a13_a06_a11_a13,
      fourthBranch_a13_a06_a11_a14, fourthBranch_a13_a06_a11_a15]
    simp
  change
    (haltWritesSafe
        (stepGo (stepGo (stepGo (initial 4) a13) a06) a11) &&
      (TNF.canonicalActions 4).all (fourthBranch_a13_a06_a11)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
