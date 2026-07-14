import BusyBeaver.BB4.Certificates.R13.C01.C06.C03.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def sixthBranch_a13_a01_a06_a03_a08 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 97 (TNF.grow 4 sixth)
    (((((((PTable.empty.set (0 : Fin 4) false a13).set (1 : Fin 4) false a01).set (1 : Fin 4) true a06).set (2 : Fin 4) false a03).set (3 : Fin 4) false a08)).set (0 : Fin 4) true sixth)
    (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a06) a03) a08) a13) a06) a03) a08) sixth)

end SetTheory.BusyBeaver.BB4.Certificates
