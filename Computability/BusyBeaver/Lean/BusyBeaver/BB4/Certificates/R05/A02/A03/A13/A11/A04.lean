import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A00
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A01
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A02
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A03
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A04
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A05
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A06
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A07
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A08
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A09
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A10
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A11
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A12
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A13
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A14
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem sixthBranchA02A03A13A11_a04 : sixthBranchA02A03A13A11 a04 = true := by
  have hAll : (TNF.canonicalActions 4).all seventhBranchA02A03A13A11A04 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      seventhBranchA02A03A13A11A04_a00,
      seventhBranchA02A03A13A11A04_a01,
      seventhBranchA02A03A13A11A04_a02,
      seventhBranchA02A03A13A11A04_a03,
      seventhBranchA02A03A13A11A04_a04,
      seventhBranchA02A03A13A11A04_a05,
      seventhBranchA02A03A13A11A04_a06,
      seventhBranchA02A03A13A11A04_a07,
      seventhBranchA02A03A13A11A04_a08,
      seventhBranchA02A03A13A11A04_a09,
      seventhBranchA02A03A13A11A04_a10,
      seventhBranchA02A03A13A11A04_a11,
      seventhBranchA02A03A13A11A04_a12,
      seventhBranchA02A03A13A11A04_a13,
      seventhBranchA02A03A13A11A04_a14,
      seventhBranchA02A03A13A11A04_a15]
    simp
  change
    (haltWritesSafe beforeSeventhA02A03A13A11A04 &&
      (TNF.canonicalActions 4).all seventhBranchA02A03A13A11A04) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
