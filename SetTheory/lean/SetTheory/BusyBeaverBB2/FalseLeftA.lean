import SetTheory.BusyBeaverBB2.Core

namespace SetTheory.BusyBeaver.BB2.Certificate

open KnownValues

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem false_left_a :
    tablesCheckFor (go false Move.left (0 : Fin 2)) = true := by decide

end SetTheory.BusyBeaver.BB2.Certificate
