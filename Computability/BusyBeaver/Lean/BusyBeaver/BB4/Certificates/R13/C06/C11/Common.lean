import BusyBeaver.BB4.Certificates.R13.C06.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def fourthBranch_a13_a06_a11 (fourth : GoAction) : Bool :=
  TNF.checkFrom leaf 103 (TNF.grow 4 fourth)
    (((((PTable.empty.set (0 : Fin 4) false a13).set
      a13.next false a06).set a06.next false a11)).set
      (3 : Fin 4) false fourth)
    (stepGo (stepGo (stepGo (stepGo (initial 4) a13) a06) a11) fourth)

end SetTheory.BusyBeaver.BB4.Certificates
