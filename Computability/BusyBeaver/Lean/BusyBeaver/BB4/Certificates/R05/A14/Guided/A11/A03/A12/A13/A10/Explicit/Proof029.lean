import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof029.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof029.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof029.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof029.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append029 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids029_parts :
    explicitMids029Part0 ++
      (explicitMids029Part1 ++
        (explicitMids029Part2 ++ explicitMids029Part3)) =
      explicitMids029 := by
  decide

theorem explicitMidLengths029 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids029 := by
  have h := explicitAll_append029 explicitMidLengths029Part0
    (explicitAll_append029 explicitMidLengths029Part1
      (explicitAll_append029 explicitMidLengths029Part2
        explicitMidLengths029Part3))
  rw [explicitMids029_parts] at h
  exact h

theorem explicitClosed029 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids029 := by
  have h := explicitAll_append029 explicitClosed029Part0
    (explicitAll_append029 explicitClosed029Part1
      (explicitAll_append029 explicitClosed029Part2
        explicitClosed029Part3))
  rw [explicitMids029_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
