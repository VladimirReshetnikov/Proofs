/-
  BusyBeaverBB4/Certificates/R12.lean

  Kernel-checked TNF coverage certificate for the root action that writes a
  mark, moves right, and returns to state A.
-/

import SetTheory.BusyBeaverBB4.Certificates.Common

namespace SetTheory
namespace BusyBeaver
namespace BB4
namespace Certificates

theorem rootBranch_a12 : rootBranch a12 = true := by
  decide

end Certificates
end BB4
end BusyBeaver
end SetTheory
