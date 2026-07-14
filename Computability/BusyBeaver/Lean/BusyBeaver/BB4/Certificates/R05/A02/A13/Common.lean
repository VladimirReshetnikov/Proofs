import BusyBeaver.BB4.Certificates.R05.A02.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def thirdTableA02A13 : PTable :=
  (((PTable.empty.set (0 : Fin 4) false a05).set a05.next false a02).set
    a02.next false a13)
def beforeFourthA02A13 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a13) a02
def fourthBranchA02A13 (fourth : GoAction) : Bool :=
  TNF.checkFrom leaf 102
    (TNF.grow
      (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a13)
      fourth)
    (thirdTableA02A13.set a02.next true fourth)
    (stepGo beforeFourthA02A13 fourth)
end SetTheory.BusyBeaver.BB4.Certificates
