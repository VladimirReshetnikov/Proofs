import BusyBeaver.BB4.Certificates.R13.C01.C02.C15.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def sixthBranch_a13_a01_a02_a15_a08 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 101 (TNF.grow 4 sixth)
    (((((((PTable.empty.set (0 : Fin 4) false a13).set (1 : Fin 4) false a01).set (1 : Fin 4) true a02).set (2 : Fin 4) false a15).set (3 : Fin 4) false a08)).set (0 : Fin 4) true sixth)
    (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) a15) a08) sixth)

end SetTheory.BusyBeaver.BB4.Certificates
