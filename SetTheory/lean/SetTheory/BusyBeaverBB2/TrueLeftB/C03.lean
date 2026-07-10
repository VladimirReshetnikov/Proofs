import SetTheory.BusyBeaverBB2.Core
namespace SetTheory.BusyBeaver.BB2.Certificate.TrueLeftB
open KnownValues
set_option maxRecDepth 100000
set_option maxHeartbeats 0 in
theorem c03 : tablesCheckFor2 (go true Move.left (1 : Fin 2))
    (halt false Move.right) = true := by decide
end SetTheory.BusyBeaver.BB2.Certificate.TrueLeftB
