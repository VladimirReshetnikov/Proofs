import BusyBeaver.BB4.Certificates.R13.C01.C02.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def fifthBranch_a13_a01_a02_a15 (fifth : GoAction) : Bool :=
  TNF.checkFrom leaf 102 (TNF.grow 4 fifth)
    ((((((PTable.empty.set (0 : Fin 4) false a13).set a13.next false a01).set a01.next true a02).set (2 : Fin 4) false a15)).set (3 : Fin 4) false fifth)
    (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) a15) fifth)

end SetTheory.BusyBeaver.BB4.Certificates
