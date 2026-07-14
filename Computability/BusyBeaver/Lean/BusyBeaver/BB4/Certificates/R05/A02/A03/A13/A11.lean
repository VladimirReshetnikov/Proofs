import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A00
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A01
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A02
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A03
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A04
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A05
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A06
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A07
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A08
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A09
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A10
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A11
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A12
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A13
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A14
import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem fifthBranchA02A03A13_a11 : fifthBranchA02A03A13 a11 = true := by
  have hAll : (TNF.canonicalActions 4).all sixthBranchA02A03A13A11 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      sixthBranchA02A03A13A11_a00,
      sixthBranchA02A03A13A11_a01,
      sixthBranchA02A03A13A11_a02,
      sixthBranchA02A03A13A11_a03,
      sixthBranchA02A03A13A11_a04,
      sixthBranchA02A03A13A11_a05,
      sixthBranchA02A03A13A11_a06,
      sixthBranchA02A03A13A11_a07,
      sixthBranchA02A03A13A11_a08,
      sixthBranchA02A03A13A11_a09,
      sixthBranchA02A03A13A11_a10,
      sixthBranchA02A03A13A11_a11,
      sixthBranchA02A03A13A11_a12,
      sixthBranchA02A03A13A11_a13,
      sixthBranchA02A03A13A11_a14,
      sixthBranchA02A03A13A11_a15]
    simp
  change
    (haltWritesSafe beforeSixthA02A03A13A11 &&
      (TNF.canonicalActions 4).all sixthBranchA02A03A13A11) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
