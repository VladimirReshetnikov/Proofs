import BusyBeaver.BB4.Certificates.R13.C01.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def fourthBranch_a13_a01_a08 (fourth : GoAction) : Bool :=
  TNF.checkFrom leaf 101 (TNF.grow 2 fourth)
    (((((PTable.empty.set (0 : Fin 4) false a13).set a13.next false a01).set a01.next true a08)).set (0 : Fin 4) true fourth)
    (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a01) a08) a13) a08) fourth)

end SetTheory.BusyBeaver.BB4.Certificates
