import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof081.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof081.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof081.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof081.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append081 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids081_parts :
    explicitMids081Part0 ++
      (explicitMids081Part1 ++
        (explicitMids081Part2 ++ explicitMids081Part3)) =
      explicitMids081 := by
  decide

theorem explicitMidLengths081 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids081 := by
  have h := explicitAll_append081 explicitMidLengths081Part0
    (explicitAll_append081 explicitMidLengths081Part1
      (explicitAll_append081 explicitMidLengths081Part2
        explicitMidLengths081Part3))
  rw [explicitMids081_parts] at h
  exact h

theorem explicitClosed081 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids081 := by
  have h := explicitAll_append081 explicitClosed081Part0
    (explicitAll_append081 explicitClosed081Part1
      (explicitAll_append081 explicitClosed081Part2
        explicitClosed081Part3))
  rw [explicitMids081_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
