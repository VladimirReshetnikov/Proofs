import BusyBeaver.BB4.Certificates.R13.C01.C02.C08.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def sixthBranch_a13_a01_a02_a08_a14 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 98 (TNF.grow 3 sixth)
    (((((((PTable.empty.set (0 : Fin 4) false a13).set (1 : Fin 4) false a01).set (1 : Fin 4) true a02).set (2 : Fin 4) false a08).set (2 : Fin 4) true a14)).set (0 : Fin 4) true sixth)
    (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) a08) a13) a02) a14) a08) sixth)

end SetTheory.BusyBeaver.BB4.Certificates
