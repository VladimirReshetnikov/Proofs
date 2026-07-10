import SetTheory.BusyBeaverBB2.Core
namespace SetTheory.BusyBeaver.BB2.Certificate.TrueLeftA
open KnownValues
set_option maxRecDepth 100000
set_option maxHeartbeats 0 in
theorem c04 : tablesCheckFor2 (go true Move.left (0 : Fin 2))
    (go false Move.right (0 : Fin 2)) = true := by decide
end SetTheory.BusyBeaver.BB2.Certificate.TrueLeftA
