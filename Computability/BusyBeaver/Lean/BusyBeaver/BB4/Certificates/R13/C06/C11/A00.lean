import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A00
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A01
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A03
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A04
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A05
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A06
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A07
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A08
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A09
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A10
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A11
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A12
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A13
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A14
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A15
import BusyBeaver.BB4.Certificates.R13.C06.C11.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem fourthBranch_a13_a06_a11_a00 :
    fourthBranch_a13_a06_a11 a00 = true := by
  have hAll :
      (TNF.canonicalActions 4).all
        (fifthBranch_a13_a06_a11_a00) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fifthBranch_a13_a06_a11_a00_a00,
      fifthBranch_a13_a06_a11_a00_a01,
      fifthBranch_a13_a06_a11_a00_a02,
      fifthBranch_a13_a06_a11_a00_a03,
      fifthBranch_a13_a06_a11_a00_a04,
      fifthBranch_a13_a06_a11_a00_a05,
      fifthBranch_a13_a06_a11_a00_a06,
      fifthBranch_a13_a06_a11_a00_a07,
      fifthBranch_a13_a06_a11_a00_a08,
      fifthBranch_a13_a06_a11_a00_a09,
      fifthBranch_a13_a06_a11_a00_a10,
      fifthBranch_a13_a06_a11_a00_a11,
      fifthBranch_a13_a06_a11_a00_a12,
      fifthBranch_a13_a06_a11_a00_a13,
      fifthBranch_a13_a06_a11_a00_a14,
      fifthBranch_a13_a06_a11_a00_a15]
    simp
  change
    (haltWritesSafe
        (stepGo
          (stepGo (stepGo (stepGo (initial 4) a13) a06) a11)
          a00) &&
      (TNF.canonicalActions 4).all
        (fifthBranch_a13_a06_a11_a00)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
