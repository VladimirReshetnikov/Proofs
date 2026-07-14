import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A00
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A01
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A02
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A03
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A04
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A05
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A06
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A07
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A08
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A09
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A10
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A11
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A12
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A13
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A14
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A05.A15
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem sixthBranch_a13_a06_a11_a00_a02_a05 :
    sixthBranch_a13_a06_a11_a00_a02 a05 = true := by
  have hAll :
      (TNF.canonicalActions 4).all (seventhBranch_a13_a06_a11_a00_a02_a05) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      seventhBranch_a13_a06_a11_a00_a02_a05_a00,
      seventhBranch_a13_a06_a11_a00_a02_a05_a01,
      seventhBranch_a13_a06_a11_a00_a02_a05_a02,
      seventhBranch_a13_a06_a11_a00_a02_a05_a03,
      seventhBranch_a13_a06_a11_a00_a02_a05_a04,
      seventhBranch_a13_a06_a11_a00_a02_a05_a05,
      seventhBranch_a13_a06_a11_a00_a02_a05_a06,
      seventhBranch_a13_a06_a11_a00_a02_a05_a07,
      seventhBranch_a13_a06_a11_a00_a02_a05_a08,
      seventhBranch_a13_a06_a11_a00_a02_a05_a09,
      seventhBranch_a13_a06_a11_a00_a02_a05_a10,
      seventhBranch_a13_a06_a11_a00_a02_a05_a11,
      seventhBranch_a13_a06_a11_a00_a02_a05_a12,
      seventhBranch_a13_a06_a11_a00_a02_a05_a13,
      seventhBranch_a13_a06_a11_a00_a02_a05_a14,
      seventhBranch_a13_a06_a11_a00_a02_a05_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a06) a11) a00) a02) a11) a00) a13) a06) a05) a06) a11) a00) a13) a06) a05) &&
      (TNF.canonicalActions 4).all (seventhBranch_a13_a06_a11_a00_a02_a05)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
