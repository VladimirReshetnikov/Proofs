import SetTheory.BusyBeaverBB2.TrueLeftA.C00
import SetTheory.BusyBeaverBB2.TrueLeftA.C01
import SetTheory.BusyBeaverBB2.TrueLeftA.C02
import SetTheory.BusyBeaverBB2.TrueLeftA.C03
import SetTheory.BusyBeaverBB2.TrueLeftA.C04
import SetTheory.BusyBeaverBB2.TrueLeftA.C05
import SetTheory.BusyBeaverBB2.TrueLeftA.C06
import SetTheory.BusyBeaverBB2.TrueLeftA.C07
import SetTheory.BusyBeaverBB2.TrueLeftA.C08
import SetTheory.BusyBeaverBB2.TrueLeftA.C09
import SetTheory.BusyBeaverBB2.TrueLeftA.C10
import SetTheory.BusyBeaverBB2.TrueLeftA.C11

namespace SetTheory.BusyBeaver.BB2.Certificate

open KnownValues

theorem true_left_a :
    tablesCheckFor (go true Move.left (0 : Fin 2)) = true := by
  simp [tablesCheckFor, actionList, TrueLeftA.c00, TrueLeftA.c01,
    TrueLeftA.c02, TrueLeftA.c03, TrueLeftA.c04, TrueLeftA.c05,
    TrueLeftA.c06, TrueLeftA.c07, TrueLeftA.c08, TrueLeftA.c09,
    TrueLeftA.c10, TrueLeftA.c11]

end SetTheory.BusyBeaver.BB2.Certificate
