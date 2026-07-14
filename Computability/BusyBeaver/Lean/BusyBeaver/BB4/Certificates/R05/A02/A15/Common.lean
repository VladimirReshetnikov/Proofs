import BusyBeaver.BB4.Certificates.R05.A02.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def thirdTableA02A15 : PTable :=
  (((PTable.empty.set (0 : Fin 4) false a05).set a05.next false a02).set
    a02.next false a15)
def beforeFourthA02A15 : Config 4 :=
  stepGo (stepGo (stepGo (initial 4) a05) a02) a15
def fourthBranchA02A15 (fourth : GoAction) : Bool :=
  TNF.checkFrom leaf 103
    (TNF.grow
      (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a15)
      fourth)
    (thirdTableA02A15.set a15.next false fourth)
    (stepGo beforeFourthA02A15 fourth)
end SetTheory.BusyBeaver.BB4.Certificates
