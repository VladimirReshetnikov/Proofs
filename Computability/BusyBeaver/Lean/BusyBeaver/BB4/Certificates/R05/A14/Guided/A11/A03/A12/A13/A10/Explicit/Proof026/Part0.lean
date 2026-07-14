import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Certificate

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

def explicitMids026Part0 : List (NGram.MidWord NGram.HistorySymbol) :=
  (explicitMids026.drop 0).take 8

theorem explicitMidLengths026Part0 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids026Part0 := by
  decide

set_option maxHeartbeats 1600000 in
theorem explicitClosed026Part0 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids026Part0 := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
