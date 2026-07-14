import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof020.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof020.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof020.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof020.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append020 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids020_parts :
    explicitMids020Part0 ++
      (explicitMids020Part1 ++
        (explicitMids020Part2 ++ explicitMids020Part3)) =
      explicitMids020 := by
  decide

theorem explicitMidLengths020 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids020 := by
  have h := explicitAll_append020 explicitMidLengths020Part0
    (explicitAll_append020 explicitMidLengths020Part1
      (explicitAll_append020 explicitMidLengths020Part2
        explicitMidLengths020Part3))
  rw [explicitMids020_parts] at h
  exact h

theorem explicitClosed020 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids020 := by
  have h := explicitAll_append020 explicitClosed020Part0
    (explicitAll_append020 explicitClosed020Part1
      (explicitAll_append020 explicitClosed020Part2
        explicitClosed020Part3))
  rw [explicitMids020_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
