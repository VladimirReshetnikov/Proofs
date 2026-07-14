import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof008.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof008.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof008.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof008.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append008 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids008_parts :
    explicitMids008Part0 ++
      (explicitMids008Part1 ++
        (explicitMids008Part2 ++ explicitMids008Part3)) =
      explicitMids008 := by
  decide

theorem explicitMidLengths008 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids008 := by
  have h := explicitAll_append008 explicitMidLengths008Part0
    (explicitAll_append008 explicitMidLengths008Part1
      (explicitAll_append008 explicitMidLengths008Part2
        explicitMidLengths008Part3))
  rw [explicitMids008_parts] at h
  exact h

theorem explicitClosed008 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids008 := by
  have h := explicitAll_append008 explicitClosed008Part0
    (explicitAll_append008 explicitClosed008Part1
      (explicitAll_append008 explicitClosed008Part2
        explicitClosed008Part3))
  rw [explicitMids008_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
