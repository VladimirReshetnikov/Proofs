import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof071.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof071.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof071.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof071.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append071 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids071_parts :
    explicitMids071Part0 ++
      (explicitMids071Part1 ++
        (explicitMids071Part2 ++ explicitMids071Part3)) =
      explicitMids071 := by
  decide

theorem explicitMidLengths071 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids071 := by
  have h := explicitAll_append071 explicitMidLengths071Part0
    (explicitAll_append071 explicitMidLengths071Part1
      (explicitAll_append071 explicitMidLengths071Part2
        explicitMidLengths071Part3))
  rw [explicitMids071_parts] at h
  exact h

theorem explicitClosed071 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids071 := by
  have h := explicitAll_append071 explicitClosed071Part0
    (explicitAll_append071 explicitClosed071Part1
      (explicitAll_append071 explicitClosed071Part2
        explicitClosed071Part3))
  rw [explicitMids071_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
