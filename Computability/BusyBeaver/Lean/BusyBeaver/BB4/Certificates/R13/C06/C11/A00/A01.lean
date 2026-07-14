import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A00
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A01
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A02
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A03
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A04
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A05
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A06
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A07
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A08
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A09
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A10
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A11
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A12
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A13
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A14
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01.A15
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem fifthBranch_a13_a06_a11_a00_a01 :
    fifthBranch_a13_a06_a11_a00 a01 = true := by
  have hAll :
      (TNF.canonicalActions 4).all (sixthBranch_a13_a06_a11_a00_a01) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      sixthBranch_a13_a06_a11_a00_a01_a00,
      sixthBranch_a13_a06_a11_a00_a01_a01,
      sixthBranch_a13_a06_a11_a00_a01_a02,
      sixthBranch_a13_a06_a11_a00_a01_a03,
      sixthBranch_a13_a06_a11_a00_a01_a04,
      sixthBranch_a13_a06_a11_a00_a01_a05,
      sixthBranch_a13_a06_a11_a00_a01_a06,
      sixthBranch_a13_a06_a11_a00_a01_a07,
      sixthBranch_a13_a06_a11_a00_a01_a08,
      sixthBranch_a13_a06_a11_a00_a01_a09,
      sixthBranch_a13_a06_a11_a00_a01_a10,
      sixthBranch_a13_a06_a11_a00_a01_a11,
      sixthBranch_a13_a06_a11_a00_a01_a12,
      sixthBranch_a13_a06_a11_a00_a01_a13,
      sixthBranch_a13_a06_a11_a00_a01_a14,
      sixthBranch_a13_a06_a11_a00_a01_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a06) a11) a00) a01) a06) a11) a00) a13) a06) &&
      (TNF.canonicalActions 4).all (sixthBranch_a13_a06_a11_a00_a01)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
