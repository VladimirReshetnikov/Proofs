import BusyBeaver.BB4.Certificates.R13.C01.C06.C11.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def sixthBranch_a13_a01_a06_a11_a15 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 101 (TNF.grow 4 sixth)
    (((((((PTable.empty.set (0 : Fin 4) false a13).set (1 : Fin 4) false a01).set (1 : Fin 4) true a06).set (2 : Fin 4) false a11).set (3 : Fin 4) false a15)).set (3 : Fin 4) true sixth)
    (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a06) a11) a15) sixth)

end SetTheory.BusyBeaver.BB4.Certificates
