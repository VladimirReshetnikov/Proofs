import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof067.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof067.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof067.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof067.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append067 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids067_parts :
    explicitMids067Part0 ++
      (explicitMids067Part1 ++
        (explicitMids067Part2 ++ explicitMids067Part3)) =
      explicitMids067 := by
  decide

theorem explicitMidLengths067 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids067 := by
  have h := explicitAll_append067 explicitMidLengths067Part0
    (explicitAll_append067 explicitMidLengths067Part1
      (explicitAll_append067 explicitMidLengths067Part2
        explicitMidLengths067Part3))
  rw [explicitMids067_parts] at h
  exact h

theorem explicitClosed067 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids067 := by
  have h := explicitAll_append067 explicitClosed067Part0
    (explicitAll_append067 explicitClosed067Part1
      (explicitAll_append067 explicitClosed067Part2
        explicitClosed067Part3))
  rw [explicitMids067_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
