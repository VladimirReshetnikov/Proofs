import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof075.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof075.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof075.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof075.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append075 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids075_parts :
    explicitMids075Part0 ++
      (explicitMids075Part1 ++
        (explicitMids075Part2 ++ explicitMids075Part3)) =
      explicitMids075 := by
  decide

theorem explicitMidLengths075 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids075 := by
  have h := explicitAll_append075 explicitMidLengths075Part0
    (explicitAll_append075 explicitMidLengths075Part1
      (explicitAll_append075 explicitMidLengths075Part2
        explicitMidLengths075Part3))
  rw [explicitMids075_parts] at h
  exact h

theorem explicitClosed075 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids075 := by
  have h := explicitAll_append075 explicitClosed075Part0
    (explicitAll_append075 explicitClosed075Part1
      (explicitAll_append075 explicitClosed075Part2
        explicitClosed075Part3))
  rw [explicitMids075_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
