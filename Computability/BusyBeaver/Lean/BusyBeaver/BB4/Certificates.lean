/-
  BusyBeaver/BB4/Certificates.lean

  Assembly of the four root-normalized TNF coverage certificates.
-/

import BusyBeaver.BB4.Certificates.R04
import BusyBeaver.BB4.Certificates.R05
import BusyBeaver.BB4.Certificates.R12
import BusyBeaver.BB4.Certificates.R13

namespace SetTheory
namespace BusyBeaver
namespace BB4
namespace Certificates

/-- The complete guided certificate for the four root representatives.

The inexpensive `a04` and `a12` roots reuse the original TNF checker.  The
larger `a05` and `a13` roots use their independently checked guided trees. -/
def rootCertificate : GoAction -> Guided.Certificate :=
  Guided.Certificate.roots4
    .legacy guidedCertificate_a05 .legacy guidedCertificate_a13

/-- Every branch of the root-reflection score search is kernel checked. -/
theorem verifyRoot_rootCertificate :
    Guided.verifyRoot rootCertificate = true := by
  unfold Guided.verifyRoot
  have h04 :
      Guided.verify 106 (TNF.grow 1 a04)
        (PTable.empty.set (0 : Fin 4) false a04)
        (stepGo (initial 4) a04) .legacy = true := by
    simpa only [Guided.verify, rootBranch] using rootBranch_a04
  have h12 :
      Guided.verify 106 (TNF.grow 1 a12)
        (PTable.empty.set (0 : Fin 4) false a12)
        (stepGo (initial 4) a12) .legacy = true := by
    simpa only [Guided.verify, rootBranch] using rootBranch_a12
  change
    (haltWritesSafe (initial 4) &&
      TNF.rootActions.all (fun action =>
        Guided.verify 106 (TNF.grow 1 action)
          (PTable.empty.set (0 : Fin 4) false action)
          (stepGo (initial 4) action) (rootCertificate action))) = true
  apply Bool.and_eq_true_iff.mpr
  constructor
  · decide
  · rw [rootActions_eq]
    simp [rootCertificate, Guided.Certificate.roots4, h04, h12,
      guidedRootBranch_a05, guidedRootBranch_a13]

end Certificates
end BB4
end BusyBeaver
end SetTheory
