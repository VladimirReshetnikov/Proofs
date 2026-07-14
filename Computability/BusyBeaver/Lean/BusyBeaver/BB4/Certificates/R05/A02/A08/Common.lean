import BusyBeaver.BB4.Certificates.R05.A02.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def thirdTableA02A08 : PTable :=
  (((PTable.empty.set (0 : Fin 4) false a05).set a05.next false a02).set
    a02.next false a08)
def beforeFourthA02A08 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a08) a05
def fourthBranchA02A08 (fourth : GoAction) : Bool :=
  TNF.checkFrom leaf 102
    (TNF.grow
      (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a08)
      fourth)
    (thirdTableA02A08.set a05.next true fourth)
    (stepGo beforeFourthA02A08 fourth)
end SetTheory.BusyBeaver.BB4.Certificates
