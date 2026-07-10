import SetTheory.BusyBeaverBB2.TrueLeftB.C00
import SetTheory.BusyBeaverBB2.TrueLeftB.C01
import SetTheory.BusyBeaverBB2.TrueLeftB.C02
import SetTheory.BusyBeaverBB2.TrueLeftB.C03
import SetTheory.BusyBeaverBB2.TrueLeftB.C04
import SetTheory.BusyBeaverBB2.TrueLeftB.C05
import SetTheory.BusyBeaverBB2.TrueLeftB.C06
import SetTheory.BusyBeaverBB2.TrueLeftB.C07
import SetTheory.BusyBeaverBB2.TrueLeftB.C08
import SetTheory.BusyBeaverBB2.TrueLeftB.C09
import SetTheory.BusyBeaverBB2.TrueLeftB.C10
import SetTheory.BusyBeaverBB2.TrueLeftB.C11

namespace SetTheory.BusyBeaver.BB2.Certificate

open KnownValues

theorem true_left_b :
    tablesCheckFor (go true Move.left (1 : Fin 2)) = true := by
  simp [tablesCheckFor, actionList, TrueLeftB.c00, TrueLeftB.c01,
    TrueLeftB.c02, TrueLeftB.c03, TrueLeftB.c04, TrueLeftB.c05,
    TrueLeftB.c06, TrueLeftB.c07, TrueLeftB.c08, TrueLeftB.c09,
    TrueLeftB.c10, TrueLeftB.c11]

end SetTheory.BusyBeaver.BB2.Certificate
