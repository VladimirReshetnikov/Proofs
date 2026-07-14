import BusyBeaver.BB4.Certificates.R05.A02.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def thirdTableA02A11 : PTable :=
  (((PTable.empty.set (0 : Fin 4) false a05).set a05.next false a02).set
    a02.next false a11)
def beforeFourthA02A11 : Config 4 :=
  stepGo (stepGo (stepGo (initial 4) a05) a02) a11
def fourthBranchA02A11 (fourth : GoAction) : Bool :=
  TNF.checkFrom leaf 103
    (TNF.grow
      (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a11)
      fourth)
    (thirdTableA02A11.set a11.next false fourth)
    (stepGo beforeFourthA02A11 fourth)
end SetTheory.BusyBeaver.BB4.Certificates
