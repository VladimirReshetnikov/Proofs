import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof057.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof057.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof057.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof057.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append057 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids057_parts :
    explicitMids057Part0 ++
      (explicitMids057Part1 ++
        (explicitMids057Part2 ++ explicitMids057Part3)) =
      explicitMids057 := by
  decide

theorem explicitMidLengths057 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids057 := by
  have h := explicitAll_append057 explicitMidLengths057Part0
    (explicitAll_append057 explicitMidLengths057Part1
      (explicitAll_append057 explicitMidLengths057Part2
        explicitMidLengths057Part3))
  rw [explicitMids057_parts] at h
  exact h

theorem explicitClosed057 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids057 := by
  have h := explicitAll_append057 explicitClosed057Part0
    (explicitAll_append057 explicitClosed057Part1
      (explicitAll_append057 explicitClosed057Part2
        explicitClosed057Part3))
  rw [explicitMids057_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
