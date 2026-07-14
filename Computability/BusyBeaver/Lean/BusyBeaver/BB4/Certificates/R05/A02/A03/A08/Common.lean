import BusyBeaver.BB4.Certificates.R05.A02.A03.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

/-- The fresh `B,1` transition after `a05,a02,a03,a08` rebounds through `A,0`. -/
def fifthBranchA02A03A08 (fifth : GoAction) : Bool :=
  TNF.checkFrom leaf 101
    (TNF.grow
      (TNF.grow (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a03) a08)
      fifth)
    (((((PTable.empty.set (0 : Fin 4) false a05).set a05.next false a02).set
      a02.next false a03).set a03.next false a08).set a05.next true fifth)
    (stepGo
      (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a03) a08)
        a05) fifth)

end SetTheory.BusyBeaver.BB4.Certificates
