import BusyBeaver.BB4.Certificates.R13.C01.C14.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def fifthBranch_a13_a01_a14_a08 (fifth : GoAction) : Bool :=
  TNF.checkFrom leaf 102 (TNF.grow 3 fifth)
    ((((((PTable.empty.set (0 : Fin 4) false a13).set a13.next false a01).set a01.next true a14).set (2 : Fin 4) false a08)).set (0 : Fin 4) true fifth)
    (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a14) a08) fifth)

end SetTheory.BusyBeaver.BB4.Certificates
