import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.C12.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def seventhBranch_a13_a01_a02_a15_a12_a11 (seventh : GoAction) : Bool :=
  TNF.checkFrom leaf 97 (TNF.grow 4 seventh)
    ((((((((PTable.empty.set (0 : Fin 4) false a13).set (1 : Fin 4) false a01).set (1 : Fin 4) true a02).set (2 : Fin 4) false a15).set (3 : Fin 4) false a12).set (2 : Fin 4) true a11)).set (3 : Fin 4) true seventh)
    (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) a15) a12) a13) a01) a02) a11) seventh)

end SetTheory.BusyBeaver.BB4.Certificates
