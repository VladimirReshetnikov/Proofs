import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof051.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof051.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof051.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof051.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append051 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids051_parts :
    explicitMids051Part0 ++
      (explicitMids051Part1 ++
        (explicitMids051Part2 ++ explicitMids051Part3)) =
      explicitMids051 := by
  decide

theorem explicitMidLengths051 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids051 := by
  have h := explicitAll_append051 explicitMidLengths051Part0
    (explicitAll_append051 explicitMidLengths051Part1
      (explicitAll_append051 explicitMidLengths051Part2
        explicitMidLengths051Part3))
  rw [explicitMids051_parts] at h
  exact h

theorem explicitClosed051 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids051 := by
  have h := explicitAll_append051 explicitClosed051Part0
    (explicitAll_append051 explicitClosed051Part1
      (explicitAll_append051 explicitClosed051Part2
        explicitClosed051Part3))
  rw [explicitMids051_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
