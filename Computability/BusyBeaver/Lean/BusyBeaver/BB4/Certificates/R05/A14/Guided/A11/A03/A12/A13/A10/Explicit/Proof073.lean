import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof073.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof073.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof073.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof073.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append073 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids073_parts :
    explicitMids073Part0 ++
      (explicitMids073Part1 ++
        (explicitMids073Part2 ++ explicitMids073Part3)) =
      explicitMids073 := by
  decide

theorem explicitMidLengths073 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids073 := by
  have h := explicitAll_append073 explicitMidLengths073Part0
    (explicitAll_append073 explicitMidLengths073Part1
      (explicitAll_append073 explicitMidLengths073Part2
        explicitMidLengths073Part3))
  rw [explicitMids073_parts] at h
  exact h

theorem explicitClosed073 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids073 := by
  have h := explicitAll_append073 explicitClosed073Part0
    (explicitAll_append073 explicitClosed073Part1
      (explicitAll_append073 explicitClosed073Part2
        explicitClosed073Part3))
  rw [explicitMids073_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
