import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A00
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A01
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A02
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A03
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A04
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A05
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A06
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A07
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A08
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A09
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A10
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A11
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A12
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A13
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A14
import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.A10.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem fifthBranchA02A07A13_a10 : fifthBranchA02A07A13 a10 = true := by
  have hAll : (TNF.canonicalActions 4).all sixthBranchA02A07A13A10 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      sixthBranchA02A07A13A10_a00,
      sixthBranchA02A07A13A10_a01,
      sixthBranchA02A07A13A10_a02,
      sixthBranchA02A07A13A10_a03,
      sixthBranchA02A07A13A10_a04,
      sixthBranchA02A07A13A10_a05,
      sixthBranchA02A07A13A10_a06,
      sixthBranchA02A07A13A10_a07,
      sixthBranchA02A07A13A10_a08,
      sixthBranchA02A07A13A10_a09,
      sixthBranchA02A07A13A10_a10,
      sixthBranchA02A07A13A10_a11,
      sixthBranchA02A07A13A10_a12,
      sixthBranchA02A07A13A10_a13,
      sixthBranchA02A07A13A10_a14,
      sixthBranchA02A07A13A10_a15]
    simp
  change
    (haltWritesSafe beforeSixthA02A07A13A10 &&
      (TNF.canonicalActions 4).all sixthBranchA02A07A13A10) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
