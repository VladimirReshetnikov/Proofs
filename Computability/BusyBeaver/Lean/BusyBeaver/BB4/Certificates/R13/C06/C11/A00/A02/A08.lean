import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A00
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A01
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A02
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A03
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A04
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A05
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A06
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A07
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A08
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A09
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A10
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A11
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A12
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A13
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A14
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.A08.A15
import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem sixthBranch_a13_a06_a11_a00_a02_a08 :
    sixthBranch_a13_a06_a11_a00_a02 a08 = true := by
  have hAll :
      (TNF.canonicalActions 4).all (seventhBranch_a13_a06_a11_a00_a02_a08) = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      seventhBranch_a13_a06_a11_a00_a02_a08_a00,
      seventhBranch_a13_a06_a11_a00_a02_a08_a01,
      seventhBranch_a13_a06_a11_a00_a02_a08_a02,
      seventhBranch_a13_a06_a11_a00_a02_a08_a03,
      seventhBranch_a13_a06_a11_a00_a02_a08_a04,
      seventhBranch_a13_a06_a11_a00_a02_a08_a05,
      seventhBranch_a13_a06_a11_a00_a02_a08_a06,
      seventhBranch_a13_a06_a11_a00_a02_a08_a07,
      seventhBranch_a13_a06_a11_a00_a02_a08_a08,
      seventhBranch_a13_a06_a11_a00_a02_a08_a09,
      seventhBranch_a13_a06_a11_a00_a02_a08_a10,
      seventhBranch_a13_a06_a11_a00_a02_a08_a11,
      seventhBranch_a13_a06_a11_a00_a02_a08_a12,
      seventhBranch_a13_a06_a11_a00_a02_a08_a13,
      seventhBranch_a13_a06_a11_a00_a02_a08_a14,
      seventhBranch_a13_a06_a11_a00_a02_a08_a15]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a06) a11) a00) a02) a11) a00) a13) a06) a08) a13) &&
      (TNF.canonicalActions 4).all (seventhBranch_a13_a06_a11_a00_a02_a08)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
