/-
  BusyBeaverBB3/Certificates.lean

  Assembly of the twelve independently kernel-checked first-transition
  groups for the exhaustive three-state lazy search.
-/

import BusyBeaver.BB3.Certificates.C00
import BusyBeaver.BB3.Certificates.C01
import BusyBeaver.BB3.Certificates.C02
import BusyBeaver.BB3.Certificates.C03
import BusyBeaver.BB3.Certificates.C04
import BusyBeaver.BB3.Certificates.C05
import BusyBeaver.BB3.Certificates.C06
import BusyBeaver.BB3.Certificates.C07
import BusyBeaver.BB3.Certificates.C08
import BusyBeaver.BB3.Certificates.C09
import BusyBeaver.BB3.Certificates.C10
import BusyBeaver.BB3.Certificates.C11

namespace SetTheory
namespace BusyBeaver
namespace BB3
namespace Certificates

/-- Every branch of the complete lazy three-state score search is accepted by
the independently proved leaf pipeline. -/
theorem check_leaf : check NGram.leaf = true := by
  unfold check
  change
    (haltWritesSafe (initial 3) && actionList.all firstBranch) = true
  apply Bool.and_eq_true_iff.mpr
  constructor
  · decide
  · rw [actionList_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      firstBranch_a00, firstBranch_a01, firstBranch_a02, firstBranch_a03,
      firstBranch_a04, firstBranch_a05, firstBranch_a06, firstBranch_a07,
      firstBranch_a08, firstBranch_a09, firstBranch_a10, firstBranch_a11]
    simp

end Certificates
end BB3
end BusyBeaver
end SetTheory
