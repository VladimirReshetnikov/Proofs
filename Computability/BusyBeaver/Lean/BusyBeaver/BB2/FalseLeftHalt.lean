import BusyBeaver.BB2.Core

namespace SetTheory.BusyBeaver.BB2.Certificate

open KnownValues

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem false_left_halt :
    tablesCheckFor (halt false Move.left) = true := by decide

end SetTheory.BusyBeaver.BB2.Certificate
