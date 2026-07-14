/-
  BusyBeaver/BB4/Certificates/R05.lean

  Hybrid kernel certificate for the root action `a05`.  Eleven second-level
  branches reuse the original exhaustive TNF checker; the exceptional `a14`
  branch uses its separately generated guided certificate.
-/

import BusyBeaver.BB4.Certificates.R05.A00
import BusyBeaver.BB4.Certificates.R05.A01
import BusyBeaver.BB4.Certificates.R05.A02
import BusyBeaver.BB4.Certificates.R05.A04
import BusyBeaver.BB4.Certificates.R05.A05
import BusyBeaver.BB4.Certificates.R05.A06
import BusyBeaver.BB4.Certificates.R05.A08
import BusyBeaver.BB4.Certificates.R05.A09
import BusyBeaver.BB4.Certificates.R05.A10
import BusyBeaver.BB4.Certificates.R05.A12
import BusyBeaver.BB4.Certificates.R05.A13
import BusyBeaver.BB4.Certificates.R05.A14.Guided

namespace SetTheory.BusyBeaver.BB4.Certificates

/-- The guided verifier tree below the normalized root action `a05`.

Only the canonical `a14` child needs a guided subtree.  Every other child is
checked by the legacy TNF verifier; the four noncanonical slots are present
only because `branch16` is a total function on continuing actions. -/
def guidedCertificate_a05 : Guided.Certificate :=
  Guided.Certificate.branch16
    .legacy .legacy .legacy .legacy
    .legacy .legacy .legacy .legacy
    .legacy .legacy .legacy .legacy
    .legacy .legacy R05A14Guided.certificate .legacy

/-- Kernel verification of the complete TNF subtree below root action `a05`. -/
theorem guidedRootBranch_a05 :
    Guided.verify 106 (TNF.grow 1 a05)
      (PTable.empty.set (0 : Fin 4) false a05)
      (stepGo (initial 4) a05) guidedCertificate_a05 = true := by
  have legacyChild (action : GoAction)
      (h : secondBranch a05 action = true) :
      Guided.verify 105 (TNF.grow (TNF.grow 1 a05) action)
        ((PTable.empty.set (0 : Fin 4) false a05).set
          a05.next false action)
        (stepGo (stepGo (initial 4) a05) action) .legacy = true := by
    simpa only [Guided.verify, secondBranch] using h
  have h00 := legacyChild a00 secondBranch_a05_a00
  have h01 := legacyChild a01 secondBranch_a05_a01
  have h02 := legacyChild a02 secondBranch_a05_a02
  have h04 := legacyChild a04 secondBranch_a05_a04
  have h05 := legacyChild a05 secondBranch_a05_a05
  have h06 := legacyChild a06 secondBranch_a05_a06
  have h08 := legacyChild a08 secondBranch_a05_a08
  have h09 := legacyChild a09 secondBranch_a05_a09
  have h10 := legacyChild a10 secondBranch_a05_a10
  have h12 := legacyChild a12 secondBranch_a05_a12
  have h13 := legacyChild a13 secondBranch_a05_a13
  have h14 :
      Guided.verify 105 (TNF.grow (TNF.grow 1 a05) a14)
        ((PTable.empty.set (0 : Fin 4) false a05).set
          a05.next false a14)
        (stepGo (stepGo (initial 4) a05) a14)
        R05A14Guided.certificate = true := by
    simpa only [R05A14Guided.pathCheck, R05A14Guided.after,
      R05A14.CertWork.after, R05A14.CertWork.start,
      R05A14Guided.ofCertWork, Guided.Work.check] using
        R05A14Guided.verified
  have hAll :
      (TNF.canonicalActions (TNF.grow 1 a05)).all
        (fun action =>
          Guided.verify 105 (TNF.grow (TNF.grow 1 a05) action)
            ((PTable.empty.set (0 : Fin 4) false a05).set
              a05.next false action)
            (stepGo (stepGo (initial 4) a05) action)
            (Guided.Certificate.children16
              .legacy .legacy .legacy .legacy
              .legacy .legacy .legacy .legacy
              .legacy .legacy .legacy .legacy
              .legacy .legacy R05A14Guided.certificate .legacy action)) =
        true := by
    have hActions :
        TNF.canonicalActions (TNF.grow 1 a05) =
          [a00, a01, a02, a04, a05, a06, a08, a09, a10, a12, a13, a14] := by
      simpa only [show TNF.grow 1 a05 = 2 by decide] using
        canonicalActions_two_eq
    rw [hActions]
    simp only [List.all_cons, List.all_nil,
      Guided.Certificate.children16_a00,
      Guided.Certificate.children16_a01,
      Guided.Certificate.children16_a02,
      Guided.Certificate.children16_a04,
      Guided.Certificate.children16_a05,
      Guided.Certificate.children16_a06,
      Guided.Certificate.children16_a08,
      Guided.Certificate.children16_a09,
      Guided.Certificate.children16_a10,
      Guided.Certificate.children16_a12,
      Guided.Certificate.children16_a13,
      Guided.Certificate.children16_a14,
      h00, h01, h02, h04, h05, h06, h08, h09, h10, h12, h13, h14]
  change
    (haltWritesSafe (stepGo (initial 4) a05) &&
      (TNF.canonicalActions (TNF.grow 1 a05)).all
        (fun action =>
          Guided.verify 105 (TNF.grow (TNF.grow 1 a05) action)
            ((PTable.empty.set (0 : Fin 4) false a05).set
              a05.next false action)
            (stepGo (stepGo (initial 4) a05) action)
            (Guided.Certificate.children16
              .legacy .legacy .legacy .legacy
              .legacy .legacy .legacy .legacy
              .legacy .legacy .legacy .legacy
              .legacy .legacy R05A14Guided.certificate .legacy action))) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates
