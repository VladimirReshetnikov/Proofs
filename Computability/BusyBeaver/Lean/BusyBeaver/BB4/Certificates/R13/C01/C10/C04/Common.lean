import BusyBeaver.BB4.Certificates.R13.C01.C10.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def fifthBranch_a13_a01_a10_a04 (fifth : GoAction) : Bool :=
  TNF.checkFrom leaf 102 (TNF.grow 3 fifth)
    ((((((PTable.empty.set (0 : Fin 4) false a13).set a13.next false a01).set a01.next true a10).set (2 : Fin 4) false a04)).set (0 : Fin 4) true fifth)
    (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a10) a04) fifth)

end SetTheory.BusyBeaver.BB4.Certificates
