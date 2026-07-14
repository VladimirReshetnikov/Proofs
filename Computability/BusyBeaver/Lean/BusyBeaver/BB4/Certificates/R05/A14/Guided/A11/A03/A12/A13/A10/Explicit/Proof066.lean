import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof066.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof066.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof066.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof066.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append066 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids066_parts :
    explicitMids066Part0 ++
      (explicitMids066Part1 ++
        (explicitMids066Part2 ++ explicitMids066Part3)) =
      explicitMids066 := by
  decide

theorem explicitMidLengths066 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids066 := by
  have h := explicitAll_append066 explicitMidLengths066Part0
    (explicitAll_append066 explicitMidLengths066Part1
      (explicitAll_append066 explicitMidLengths066Part2
        explicitMidLengths066Part3))
  rw [explicitMids066_parts] at h
  exact h

theorem explicitClosed066 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids066 := by
  have h := explicitAll_append066 explicitClosed066Part0
    (explicitAll_append066 explicitClosed066Part1
      (explicitAll_append066 explicitClosed066Part2
        explicitClosed066Part3))
  rw [explicitMids066_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
