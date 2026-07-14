import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof068.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof068.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof068.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof068.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append068 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids068_parts :
    explicitMids068Part0 ++
      (explicitMids068Part1 ++
        (explicitMids068Part2 ++ explicitMids068Part3)) =
      explicitMids068 := by
  decide

theorem explicitMidLengths068 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids068 := by
  have h := explicitAll_append068 explicitMidLengths068Part0
    (explicitAll_append068 explicitMidLengths068Part1
      (explicitAll_append068 explicitMidLengths068Part2
        explicitMidLengths068Part3))
  rw [explicitMids068_parts] at h
  exact h

theorem explicitClosed068 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids068 := by
  have h := explicitAll_append068 explicitClosed068Part0
    (explicitAll_append068 explicitClosed068Part1
      (explicitAll_append068 explicitClosed068Part2
        explicitClosed068Part3))
  rw [explicitMids068_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
