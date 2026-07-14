import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof012.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof012.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof012.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof012.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append012 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids012_parts :
    explicitMids012Part0 ++
      (explicitMids012Part1 ++
        (explicitMids012Part2 ++ explicitMids012Part3)) =
      explicitMids012 := by
  decide

theorem explicitMidLengths012 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids012 := by
  have h := explicitAll_append012 explicitMidLengths012Part0
    (explicitAll_append012 explicitMidLengths012Part1
      (explicitAll_append012 explicitMidLengths012Part2
        explicitMidLengths012Part3))
  rw [explicitMids012_parts] at h
  exact h

theorem explicitClosed012 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids012 := by
  have h := explicitAll_append012 explicitClosed012Part0
    (explicitAll_append012 explicitClosed012Part1
      (explicitAll_append012 explicitClosed012Part2
        explicitClosed012Part3))
  rw [explicitMids012_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
