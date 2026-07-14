import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof072.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof072.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof072.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof072.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append072 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids072_parts :
    explicitMids072Part0 ++
      (explicitMids072Part1 ++
        (explicitMids072Part2 ++ explicitMids072Part3)) =
      explicitMids072 := by
  decide

theorem explicitMidLengths072 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids072 := by
  have h := explicitAll_append072 explicitMidLengths072Part0
    (explicitAll_append072 explicitMidLengths072Part1
      (explicitAll_append072 explicitMidLengths072Part2
        explicitMidLengths072Part3))
  rw [explicitMids072_parts] at h
  exact h

theorem explicitClosed072 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids072 := by
  have h := explicitAll_append072 explicitClosed072Part0
    (explicitAll_append072 explicitClosed072Part1
      (explicitAll_append072 explicitClosed072Part2
        explicitClosed072Part3))
  rw [explicitMids072_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
