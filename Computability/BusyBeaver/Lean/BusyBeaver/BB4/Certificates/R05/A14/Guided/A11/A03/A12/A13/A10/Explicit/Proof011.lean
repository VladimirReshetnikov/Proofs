import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof011.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof011.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof011.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof011.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append011 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids011_parts :
    explicitMids011Part0 ++
      (explicitMids011Part1 ++
        (explicitMids011Part2 ++ explicitMids011Part3)) =
      explicitMids011 := by
  decide

theorem explicitMidLengths011 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids011 := by
  have h := explicitAll_append011 explicitMidLengths011Part0
    (explicitAll_append011 explicitMidLengths011Part1
      (explicitAll_append011 explicitMidLengths011Part2
        explicitMidLengths011Part3))
  rw [explicitMids011_parts] at h
  exact h

theorem explicitClosed011 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids011 := by
  have h := explicitAll_append011 explicitClosed011Part0
    (explicitAll_append011 explicitClosed011Part1
      (explicitAll_append011 explicitClosed011Part2
        explicitClosed011Part3))
  rw [explicitMids011_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
