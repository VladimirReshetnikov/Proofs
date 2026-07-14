import BusyBeaver.BB4.Certificates.R13.C01.C06.C03.C08.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def seventhBranch_a13_a01_a06_a03_a08_a11 (seventh : GoAction) : Bool :=
  TNF.checkFrom leaf 93 (TNF.grow 4 seventh)
    ((((((((PTable.empty.set (0 : Fin 4) false a13).set (1 : Fin 4) false a01).set (1 : Fin 4) true a06).set (2 : Fin 4) false a03).set (3 : Fin 4) false a08).set (0 : Fin 4) true a11)).set (2 : Fin 4) true seventh)
    (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a06) a03) a08) a13) a06) a03) a08) a11) a08) a13) a06) seventh)

end SetTheory.BusyBeaver.BB4.Certificates
