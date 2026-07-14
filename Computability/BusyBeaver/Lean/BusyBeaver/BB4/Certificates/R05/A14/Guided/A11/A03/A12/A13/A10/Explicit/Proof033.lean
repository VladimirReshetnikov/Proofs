import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof033.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof033.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof033.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof033.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append033 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids033_parts :
    explicitMids033Part0 ++
      (explicitMids033Part1 ++
        (explicitMids033Part2 ++ explicitMids033Part3)) =
      explicitMids033 := by
  decide

theorem explicitMidLengths033 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids033 := by
  have h := explicitAll_append033 explicitMidLengths033Part0
    (explicitAll_append033 explicitMidLengths033Part1
      (explicitAll_append033 explicitMidLengths033Part2
        explicitMidLengths033Part3))
  rw [explicitMids033_parts] at h
  exact h

theorem explicitClosed033 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids033 := by
  have h := explicitAll_append033 explicitClosed033Part0
    (explicitAll_append033 explicitClosed033Part1
      (explicitAll_append033 explicitClosed033Part2
        explicitClosed033Part3))
  rw [explicitMids033_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
