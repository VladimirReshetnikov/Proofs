import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof050.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof050.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof050.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof050.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append050 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids050_parts :
    explicitMids050Part0 ++
      (explicitMids050Part1 ++
        (explicitMids050Part2 ++ explicitMids050Part3)) =
      explicitMids050 := by
  decide

theorem explicitMidLengths050 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids050 := by
  have h := explicitAll_append050 explicitMidLengths050Part0
    (explicitAll_append050 explicitMidLengths050Part1
      (explicitAll_append050 explicitMidLengths050Part2
        explicitMidLengths050Part3))
  rw [explicitMids050_parts] at h
  exact h

theorem explicitClosed050 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids050 := by
  have h := explicitAll_append050 explicitClosed050Part0
    (explicitAll_append050 explicitClosed050Part1
      (explicitAll_append050 explicitClosed050Part2
        explicitClosed050Part3))
  rw [explicitMids050_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
