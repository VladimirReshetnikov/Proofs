import BusyBeaver.BB4.Certificates.R13.C01.C06.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def fifthBranch_a13_a01_a06_a03 (fifth : GoAction) : Bool :=
  TNF.checkFrom leaf 102 (TNF.grow 4 fifth)
    ((((((PTable.empty.set (0 : Fin 4) false a13).set a13.next false a01).set a01.next true a06).set (2 : Fin 4) false a03)).set (3 : Fin 4) false fifth)
    (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a06) a03) fifth)

end SetTheory.BusyBeaver.BB4.Certificates
