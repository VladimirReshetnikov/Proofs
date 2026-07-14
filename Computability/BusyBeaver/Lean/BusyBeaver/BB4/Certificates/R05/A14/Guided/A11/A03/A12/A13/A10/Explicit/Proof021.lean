import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof021.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof021.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof021.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof021.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append021 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids021_parts :
    explicitMids021Part0 ++
      (explicitMids021Part1 ++
        (explicitMids021Part2 ++ explicitMids021Part3)) =
      explicitMids021 := by
  decide

theorem explicitMidLengths021 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids021 := by
  have h := explicitAll_append021 explicitMidLengths021Part0
    (explicitAll_append021 explicitMidLengths021Part1
      (explicitAll_append021 explicitMidLengths021Part2
        explicitMidLengths021Part3))
  rw [explicitMids021_parts] at h
  exact h

theorem explicitClosed021 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids021 := by
  have h := explicitAll_append021 explicitClosed021Part0
    (explicitAll_append021 explicitClosed021Part1
      (explicitAll_append021 explicitClosed021Part2
        explicitClosed021Part3))
  rw [explicitMids021_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
