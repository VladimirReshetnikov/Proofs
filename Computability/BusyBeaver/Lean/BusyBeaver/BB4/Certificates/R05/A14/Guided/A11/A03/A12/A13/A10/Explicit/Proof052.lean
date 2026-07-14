import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof052.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof052.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof052.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof052.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append052 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids052_parts :
    explicitMids052Part0 ++
      (explicitMids052Part1 ++
        (explicitMids052Part2 ++ explicitMids052Part3)) =
      explicitMids052 := by
  decide

theorem explicitMidLengths052 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids052 := by
  have h := explicitAll_append052 explicitMidLengths052Part0
    (explicitAll_append052 explicitMidLengths052Part1
      (explicitAll_append052 explicitMidLengths052Part2
        explicitMidLengths052Part3))
  rw [explicitMids052_parts] at h
  exact h

theorem explicitClosed052 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids052 := by
  have h := explicitAll_append052 explicitClosed052Part0
    (explicitAll_append052 explicitClosed052Part1
      (explicitAll_append052 explicitClosed052Part2
        explicitClosed052Part3))
  rw [explicitMids052_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
