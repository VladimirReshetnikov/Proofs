import BusyBeaver.BB4.Certificates.R13.C06.C11.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def fifthBranch_a13_a06_a11_a00 (fifth : GoAction) : Bool :=
  TNF.checkFrom leaf 102 (TNF.grow 4 fifth)
    ((((((PTable.empty.set (0 : Fin 4) false a13).set
      (1 : Fin 4) false a06).set (2 : Fin 4) false a11).set
      (3 : Fin 4) false a00)).set (0 : Fin 4) true fifth)
    (stepGo
      (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a06) a11) a00)
      fifth)

end SetTheory.BusyBeaver.BB4.Certificates
