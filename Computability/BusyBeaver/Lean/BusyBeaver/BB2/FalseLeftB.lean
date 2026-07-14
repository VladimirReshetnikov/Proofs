import BusyBeaver.BB2.FalseLeftB.C00
import BusyBeaver.BB2.FalseLeftB.C01
import BusyBeaver.BB2.FalseLeftB.C02
import BusyBeaver.BB2.FalseLeftB.C03
import BusyBeaver.BB2.FalseLeftB.C04
import BusyBeaver.BB2.FalseLeftB.C05
import BusyBeaver.BB2.FalseLeftB.C06
import BusyBeaver.BB2.FalseLeftB.C07
import BusyBeaver.BB2.FalseLeftB.C08
import BusyBeaver.BB2.FalseLeftB.C09
import BusyBeaver.BB2.FalseLeftB.C10
import BusyBeaver.BB2.FalseLeftB.C11

namespace SetTheory.BusyBeaver.BB2.Certificate

open KnownValues

theorem false_left_b :
    tablesCheckFor (go false Move.left (1 : Fin 2)) = true := by
  simp [tablesCheckFor, actionList, FalseLeftB.c00, FalseLeftB.c01,
    FalseLeftB.c02, FalseLeftB.c03, FalseLeftB.c04, FalseLeftB.c05,
    FalseLeftB.c06, FalseLeftB.c07, FalseLeftB.c08, FalseLeftB.c09,
    FalseLeftB.c10, FalseLeftB.c11]

end SetTheory.BusyBeaver.BB2.Certificate
