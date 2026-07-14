import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A00
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A01
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A02
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A03
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A04
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A05
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A06
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A07
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A08
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A09
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A10
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A11
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A12
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A13
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A14
import BusyBeaver.BB4.Certificates.R05.A02.A03.A14.A15

namespace SetTheory.BusyBeaver.BB4.Certificates

theorem fourthBranchA02A03_a14 : fourthBranchA02A03 a14 = true := by
  have hAll : (TNF.canonicalActions 4).all fifthBranchA02A03A14 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      fifthBranchA02A03A14_a00,
      fifthBranchA02A03A14_a01,
      fifthBranchA02A03A14_a02,
      fifthBranchA02A03A14_a03,
      fifthBranchA02A03A14_a04,
      fifthBranchA02A03A14_a05,
      fifthBranchA02A03A14_a06,
      fifthBranchA02A03A14_a07,
      fifthBranchA02A03A14_a08,
      fifthBranchA02A03A14_a09,
      fifthBranchA02A03A14_a10,
      fifthBranchA02A03A14_a11,
      fifthBranchA02A03A14_a12,
      fifthBranchA02A03A14_a13,
      fifthBranchA02A03A14_a14,
      fifthBranchA02A03A14_a15]
    simp
  change
    (haltWritesSafe beforeFifthA02A03A14 &&
      (TNF.canonicalActions 4).all fifthBranchA02A03A14) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
