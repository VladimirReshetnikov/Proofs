import BusyBeaver.BB4.Certificates.R05.A02.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def thirdTableA02A07 : PTable :=
  (((PTable.empty.set (0 : Fin 4) false a05).set a05.next false a02).set
    a02.next false a07)
def beforeFourthA02A07 : Config 4 :=
  stepGo (stepGo (stepGo (initial 4) a05) a02) a07
def fourthBranchA02A07 (fourth : GoAction) : Bool :=
  TNF.checkFrom leaf 103
    (TNF.grow
      (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a07)
      fourth)
    (thirdTableA02A07.set a07.next false fourth)
    (stepGo beforeFourthA02A07 fourth)
end SetTheory.BusyBeaver.BB4.Certificates
