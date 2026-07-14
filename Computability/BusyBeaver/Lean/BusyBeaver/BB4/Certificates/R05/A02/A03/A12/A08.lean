import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A00
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A01
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A02
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A03
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A04
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A05
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A06
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A07
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A08
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A09
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A10
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A11
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A12
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A13
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A14
import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A08.A15
namespace SetTheory.BusyBeaver.BB4.Certificates
theorem fifthBranchA02A03A12_a08 : fifthBranchA02A03A12 a08 = true := by
  have hAll : (TNF.canonicalActions 4).all sixthBranchA02A03A12A08 = true := by
    rw [canonicalActions_four_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      sixthBranchA02A03A12A08_a00,
      sixthBranchA02A03A12A08_a01,
      sixthBranchA02A03A12A08_a02,
      sixthBranchA02A03A12A08_a03,
      sixthBranchA02A03A12A08_a04,
      sixthBranchA02A03A12A08_a05,
      sixthBranchA02A03A12A08_a06,
      sixthBranchA02A03A12A08_a07,
      sixthBranchA02A03A12A08_a08,
      sixthBranchA02A03A12A08_a09,
      sixthBranchA02A03A12A08_a10,
      sixthBranchA02A03A12A08_a11,
      sixthBranchA02A03A12A08_a12,
      sixthBranchA02A03A12A08_a13,
      sixthBranchA02A03A12A08_a14,
      sixthBranchA02A03A12A08_a15]
    simp
  change
    (haltWritesSafe beforeSixthA02A03A12A08 &&
      (TNF.canonicalActions 4).all sixthBranchA02A03A12A08) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩
end SetTheory.BusyBeaver.BB4.Certificates
