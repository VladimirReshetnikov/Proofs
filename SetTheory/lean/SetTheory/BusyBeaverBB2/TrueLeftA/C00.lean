import SetTheory.BusyBeaverBB2.Core
namespace SetTheory.BusyBeaver.BB2.Certificate.TrueLeftA
open KnownValues
set_option maxRecDepth 100000
set_option maxHeartbeats 0 in
theorem c00 : tablesCheckFor2 (go true Move.left (0 : Fin 2))
    (halt false Move.left) = true := by decide
end SetTheory.BusyBeaver.BB2.Certificate.TrueLeftA
