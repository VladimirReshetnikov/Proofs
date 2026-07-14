import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A00
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A01
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A02
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A03
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A04
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A05
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A06
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A07
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A08
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A09
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A10
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A11
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A12
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A13
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A14
import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.A09.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem sixthBranchA02A07A08A15_a09 : sixthBranchA02A07A08A15 a09 = true := by
  have hAll : (TNF.canonicalActions 4).all seventhBranchA02A07A08A15A09 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      seventhBranchA02A07A08A15A09_a00,
      seventhBranchA02A07A08A15A09_a01,
      seventhBranchA02A07A08A15A09_a02,
      seventhBranchA02A07A08A15A09_a03,
      seventhBranchA02A07A08A15A09_a04,
      seventhBranchA02A07A08A15A09_a05,
      seventhBranchA02A07A08A15A09_a06,
      seventhBranchA02A07A08A15A09_a07,
      seventhBranchA02A07A08A15A09_a08,
      seventhBranchA02A07A08A15A09_a09,
      seventhBranchA02A07A08A15A09_a10,
      seventhBranchA02A07A08A15A09_a11,
      seventhBranchA02A07A08A15A09_a12,
      seventhBranchA02A07A08A15A09_a13,
      seventhBranchA02A07A08A15A09_a14,
      seventhBranchA02A07A08A15A09_a15]
    simp
  change
    (haltWritesSafe beforeSeventhA02A07A08A15A09 &&
      (TNF.canonicalActions 4).all seventhBranchA02A07A08A15A09) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
