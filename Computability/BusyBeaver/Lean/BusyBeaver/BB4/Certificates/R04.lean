/-
  BusyBeaver/BB4/Certificates/R04.lean

  Kernel-checked TNF coverage certificate for the root action that writes
  blank, moves right, and returns to state A.
-/

import BusyBeaver.BB4.Certificates.Common

namespace SetTheory
namespace BusyBeaver
namespace BB4
namespace Certificates

theorem rootBranch_a04 : rootBranch a04 = true := by
  decide

end Certificates
end BB4
end BusyBeaver
end SetTheory
