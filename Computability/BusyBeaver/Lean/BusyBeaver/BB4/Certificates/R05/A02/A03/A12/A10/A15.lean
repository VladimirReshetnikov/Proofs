import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A00
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A01
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A02
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A03
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A04
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A05
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A06
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A07
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A08
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A09
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A10
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A11
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A12
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A13
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A14
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A15.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem sixthBranchA02A03A12A10_a15 : sixthBranchA02A03A12A10 a15 = true := by
  have hAll : (TNF.canonicalActions 4).all seventhBranchA02A03A12A10A15 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      seventhBranchA02A03A12A10A15_a00,
      seventhBranchA02A03A12A10A15_a01,
      seventhBranchA02A03A12A10A15_a02,
      seventhBranchA02A03A12A10A15_a03,
      seventhBranchA02A03A12A10A15_a04,
      seventhBranchA02A03A12A10A15_a05,
      seventhBranchA02A03A12A10A15_a06,
      seventhBranchA02A03A12A10A15_a07,
      seventhBranchA02A03A12A10A15_a08,
      seventhBranchA02A03A12A10A15_a09,
      seventhBranchA02A03A12A10A15_a10,
      seventhBranchA02A03A12A10A15_a11,
      seventhBranchA02A03A12A10A15_a12,
      seventhBranchA02A03A12A10A15_a13,
      seventhBranchA02A03A12A10A15_a14,
      seventhBranchA02A03A12A10A15_a15]
    simp
  change
    (haltWritesSafe beforeSeventhA02A03A12A10A15 &&
      (TNF.canonicalActions 4).all seventhBranchA02A03A12A10A15) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
