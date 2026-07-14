import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof077.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof077.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof077.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof077.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append077 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids077_parts :
    explicitMids077Part0 ++
      (explicitMids077Part1 ++
        (explicitMids077Part2 ++ explicitMids077Part3)) =
      explicitMids077 := by
  decide

theorem explicitMidLengths077 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids077 := by
  have h := explicitAll_append077 explicitMidLengths077Part0
    (explicitAll_append077 explicitMidLengths077Part1
      (explicitAll_append077 explicitMidLengths077Part2
        explicitMidLengths077Part3))
  rw [explicitMids077_parts] at h
  exact h

theorem explicitClosed077 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids077 := by
  have h := explicitAll_append077 explicitClosed077Part0
    (explicitAll_append077 explicitClosed077Part1
      (explicitAll_append077 explicitClosed077Part2
        explicitClosed077Part3))
  rw [explicitMids077_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
