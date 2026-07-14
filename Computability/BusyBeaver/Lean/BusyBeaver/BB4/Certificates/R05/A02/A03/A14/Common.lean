import BusyBeaver.BB4.Certificates.R05.A02.A03.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def fourthTableA02A03A14 : PTable :=
  (((PTable.empty.set (0 : Fin 4) false a05).set a05.next false a02).set
    a02.next false a03).set a03.next false a14

def beforeFifthA02A03A14 : Config 4 :=
  stepGo
    (stepGo
      (stepGo
        (stepGo
          (stepGo (initial 4) a05) a02) a03) a14)
      a03

/-- The fresh `D,1` transition after `a14` and known `C,0`. -/
def fifthBranchA02A03A14 (fifth : GoAction) : Bool :=
  TNF.checkFrom leaf 101
    (TNF.grow
      (TNF.grow (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a03) a14)
      fifth)
    (fourthTableA02A03A14.set a03.next true fifth)
    (stepGo beforeFifthA02A03A14 fifth)

end SetTheory.BusyBeaver.BB4.Certificates
