import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof048.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof048.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof048.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof048.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append048 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids048_parts :
    explicitMids048Part0 ++
      (explicitMids048Part1 ++
        (explicitMids048Part2 ++ explicitMids048Part3)) =
      explicitMids048 := by
  decide

theorem explicitMidLengths048 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids048 := by
  have h := explicitAll_append048 explicitMidLengths048Part0
    (explicitAll_append048 explicitMidLengths048Part1
      (explicitAll_append048 explicitMidLengths048Part2
        explicitMidLengths048Part3))
  rw [explicitMids048_parts] at h
  exact h

theorem explicitClosed048 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids048 := by
  have h := explicitAll_append048 explicitClosed048Part0
    (explicitAll_append048 explicitClosed048Part1
      (explicitAll_append048 explicitClosed048Part2
        explicitClosed048Part3))
  rw [explicitMids048_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
