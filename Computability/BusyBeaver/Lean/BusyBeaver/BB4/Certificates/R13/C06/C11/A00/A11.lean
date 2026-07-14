import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A00
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A01
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A02
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A03
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A04
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A05
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A06
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A07
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A08
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A09
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A10
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A11
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A12
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A13
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A14
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11.A15
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem fifthBranch_a13_a06_a11_a00_a11 :
    fifthBranch_a13_a06_a11_a00 a11 = true := by
  have hAll :
      (TNF.canonicalActions 4).all (sixthBranch_a13_a06_a11_a00_a11) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      sixthBranch_a13_a06_a11_a00_a11_a00,
      sixthBranch_a13_a06_a11_a00_a11_a01,
      sixthBranch_a13_a06_a11_a00_a11_a02,
      sixthBranch_a13_a06_a11_a00_a11_a03,
      sixthBranch_a13_a06_a11_a00_a11_a04,
      sixthBranch_a13_a06_a11_a00_a11_a05,
      sixthBranch_a13_a06_a11_a00_a11_a06,
      sixthBranch_a13_a06_a11_a00_a11_a07,
      sixthBranch_a13_a06_a11_a00_a11_a08,
      sixthBranch_a13_a06_a11_a00_a11_a09,
      sixthBranch_a13_a06_a11_a00_a11_a10,
      sixthBranch_a13_a06_a11_a00_a11_a11,
      sixthBranch_a13_a06_a11_a00_a11_a12,
      sixthBranch_a13_a06_a11_a00_a11_a13,
      sixthBranch_a13_a06_a11_a00_a11_a14,
      sixthBranch_a13_a06_a11_a00_a11_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a06) a11) a00) a11) a00) a13) a06) &&
      (TNF.canonicalActions 4).all (sixthBranch_a13_a06_a11_a00_a11)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
