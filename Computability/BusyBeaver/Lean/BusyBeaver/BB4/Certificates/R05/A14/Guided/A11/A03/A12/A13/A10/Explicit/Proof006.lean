import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof006.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof006.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof006.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof006.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append006 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids006_parts :
    explicitMids006Part0 ++
      (explicitMids006Part1 ++
        (explicitMids006Part2 ++ explicitMids006Part3)) =
      explicitMids006 := by
  decide

theorem explicitMidLengths006 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids006 := by
  have h := explicitAll_append006 explicitMidLengths006Part0
    (explicitAll_append006 explicitMidLengths006Part1
      (explicitAll_append006 explicitMidLengths006Part2
        explicitMidLengths006Part3))
  rw [explicitMids006_parts] at h
  exact h

theorem explicitClosed006 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids006 := by
  have h := explicitAll_append006 explicitClosed006Part0
    (explicitAll_append006 explicitClosed006Part1
      (explicitAll_append006 explicitClosed006Part2
        explicitClosed006Part3))
  rw [explicitMids006_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
