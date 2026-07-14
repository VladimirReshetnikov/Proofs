import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof086.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof086.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof086.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof086.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append086 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids086_parts :
    explicitMids086Part0 ++
      (explicitMids086Part1 ++
        (explicitMids086Part2 ++ explicitMids086Part3)) =
      explicitMids086 := by
  decide

theorem explicitMidLengths086 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids086 := by
  have h := explicitAll_append086 explicitMidLengths086Part0
    (explicitAll_append086 explicitMidLengths086Part1
      (explicitAll_append086 explicitMidLengths086Part2
        explicitMidLengths086Part3))
  rw [explicitMids086_parts] at h
  exact h

theorem explicitClosed086 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids086 := by
  have h := explicitAll_append086 explicitClosed086Part0
    (explicitAll_append086 explicitClosed086Part1
      (explicitAll_append086 explicitClosed086Part2
        explicitClosed086Part3))
  rw [explicitMids086_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
