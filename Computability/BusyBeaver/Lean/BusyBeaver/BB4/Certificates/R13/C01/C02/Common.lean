import BusyBeaver.BB4.Certificates.R13.C01.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def fourthBranch_a13_a01_a02 (fourth : GoAction) : Bool :=
  TNF.checkFrom leaf 103 (TNF.grow 3 fourth)
    (((((PTable.empty.set (0 : Fin 4) false a13).set a13.next false a01).set a01.next true a02)).set (2 : Fin 4) false fourth)
    (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a02) fourth)

end SetTheory.BusyBeaver.BB4.Certificates
