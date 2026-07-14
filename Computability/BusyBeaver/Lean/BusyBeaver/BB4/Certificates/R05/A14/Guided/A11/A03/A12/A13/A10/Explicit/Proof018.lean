import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof018.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof018.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof018.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof018.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append018 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids018_parts :
    explicitMids018Part0 ++
      (explicitMids018Part1 ++
        (explicitMids018Part2 ++ explicitMids018Part3)) =
      explicitMids018 := by
  decide

theorem explicitMidLengths018 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids018 := by
  have h := explicitAll_append018 explicitMidLengths018Part0
    (explicitAll_append018 explicitMidLengths018Part1
      (explicitAll_append018 explicitMidLengths018Part2
        explicitMidLengths018Part3))
  rw [explicitMids018_parts] at h
  exact h

theorem explicitClosed018 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids018 := by
  have h := explicitAll_append018 explicitClosed018Part0
    (explicitAll_append018 explicitClosed018Part1
      (explicitAll_append018 explicitClosed018Part2
        explicitClosed018Part3))
  rw [explicitMids018_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
