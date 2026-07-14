import BusyBeaver.BB4.Certificates.R13.C06.C11.A00.A02.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def seventhBranch_a13_a06_a11_a00_a02_a07 (seventh : GoAction) : Bool :=
  TNF.checkFrom leaf 89 (TNF.grow 4 seventh)
    (((((((PTable.empty.set (0 : Fin 4) false a13).set (1 : Fin 4) false a06).set (2 : Fin 4) false a11).set (3 : Fin 4) false a00).set (0 : Fin 4) true a02).set (2 : Fin 4) true a07).set (3 : Fin 4) true seventh)
    (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a06) a11) a00) a02) a11) a00) a13) a06) a07) a00) a13) a06) a11) a00) a02) a11) seventh)

end SetTheory.BusyBeaver.BB4.Certificates
