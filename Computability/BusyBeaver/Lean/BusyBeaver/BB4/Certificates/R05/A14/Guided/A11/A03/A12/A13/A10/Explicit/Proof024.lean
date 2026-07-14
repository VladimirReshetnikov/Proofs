import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof024.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof024.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof024.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof024.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append024 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids024_parts :
    explicitMids024Part0 ++
      (explicitMids024Part1 ++
        (explicitMids024Part2 ++ explicitMids024Part3)) =
      explicitMids024 := by
  decide

theorem explicitMidLengths024 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids024 := by
  have h := explicitAll_append024 explicitMidLengths024Part0
    (explicitAll_append024 explicitMidLengths024Part1
      (explicitAll_append024 explicitMidLengths024Part2
        explicitMidLengths024Part3))
  rw [explicitMids024_parts] at h
  exact h

theorem explicitClosed024 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids024 := by
  have h := explicitAll_append024 explicitClosed024Part0
    (explicitAll_append024 explicitClosed024Part1
      (explicitAll_append024 explicitClosed024Part2
        explicitClosed024Part3))
  rw [explicitMids024_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
