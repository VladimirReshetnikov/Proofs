import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A00
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A01
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A02
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A03
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A04
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A05
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A06
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A07
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A08
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A09
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A10
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A11
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A12
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A13
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A14
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.A13.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem sixthBranchA02A03A12A10_a13 : sixthBranchA02A03A12A10 a13 = true := by
  have hAll : (TNF.canonicalActions 4).all seventhBranchA02A03A12A10A13 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      seventhBranchA02A03A12A10A13_a00,
      seventhBranchA02A03A12A10A13_a01,
      seventhBranchA02A03A12A10A13_a02,
      seventhBranchA02A03A12A10A13_a03,
      seventhBranchA02A03A12A10A13_a04,
      seventhBranchA02A03A12A10A13_a05,
      seventhBranchA02A03A12A10A13_a06,
      seventhBranchA02A03A12A10A13_a07,
      seventhBranchA02A03A12A10A13_a08,
      seventhBranchA02A03A12A10A13_a09,
      seventhBranchA02A03A12A10A13_a10,
      seventhBranchA02A03A12A10A13_a11,
      seventhBranchA02A03A12A10A13_a12,
      seventhBranchA02A03A12A10A13_a13,
      seventhBranchA02A03A12A10A13_a14,
      seventhBranchA02A03A12A10A13_a15]
    simp
  change
    (haltWritesSafe beforeSeventhA02A03A12A10A13 &&
      (TNF.canonicalActions 4).all seventhBranchA02A03A12A10A13) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
