import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof015.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof015.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof015.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof015.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append015 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids015_parts :
    explicitMids015Part0 ++
      (explicitMids015Part1 ++
        (explicitMids015Part2 ++ explicitMids015Part3)) =
      explicitMids015 := by
  decide

theorem explicitMidLengths015 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids015 := by
  have h := explicitAll_append015 explicitMidLengths015Part0
    (explicitAll_append015 explicitMidLengths015Part1
      (explicitAll_append015 explicitMidLengths015Part2
        explicitMidLengths015Part3))
  rw [explicitMids015_parts] at h
  exact h

theorem explicitClosed015 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids015 := by
  have h := explicitAll_append015 explicitClosed015Part0
    (explicitAll_append015 explicitClosed015Part1
      (explicitAll_append015 explicitClosed015Part2
        explicitClosed015Part3))
  rw [explicitMids015_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
