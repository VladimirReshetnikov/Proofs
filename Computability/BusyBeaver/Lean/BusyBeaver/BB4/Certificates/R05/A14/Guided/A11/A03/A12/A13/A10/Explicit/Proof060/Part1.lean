import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Certificate

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

def explicitMids060Part1 : List (NGram.MidWord NGram.HistorySymbol) :=
  (explicitMids060.drop 8).take 8

theorem explicitMidLengths060Part1 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids060Part1 := by
  decide

set_option maxHeartbeats 1600000 in
theorem explicitClosed060Part1 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids060Part1 := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
