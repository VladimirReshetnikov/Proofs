import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof028.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof028.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof028.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof028.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append028 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids028_parts :
    explicitMids028Part0 ++
      (explicitMids028Part1 ++
        (explicitMids028Part2 ++ explicitMids028Part3)) =
      explicitMids028 := by
  decide

theorem explicitMidLengths028 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids028 := by
  have h := explicitAll_append028 explicitMidLengths028Part0
    (explicitAll_append028 explicitMidLengths028Part1
      (explicitAll_append028 explicitMidLengths028Part2
        explicitMidLengths028Part3))
  rw [explicitMids028_parts] at h
  exact h

theorem explicitClosed028 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids028 := by
  have h := explicitAll_append028 explicitClosed028Part0
    (explicitAll_append028 explicitClosed028Part1
      (explicitAll_append028 explicitClosed028Part2
        explicitClosed028Part3))
  rw [explicitMids028_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
