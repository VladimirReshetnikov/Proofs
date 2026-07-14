import BusyBeaver.BB4.Certificates.R13.C01.C02.C11.C04.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def seventhBranch_a13_a01_a02_a11_a04_a15 (seventh : GoAction) : Bool :=
  TNF.checkFrom leaf 95 (TNF.grow 4 seventh)
    ((((((((PTable.empty.set (0 : Fin 4) false a13).set (1 : Fin 4) false a01).set (1 : Fin 4) true a02).set (2 : Fin 4) false a11).set (3 : Fin 4) false a04).set (0 : Fin 4) true a15)).set (3 : Fin 4) true seventh)
    (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) a11) a04) a15) a04) a13) a01) a02) a11) seventh)

end SetTheory.BusyBeaver.BB4.Certificates
