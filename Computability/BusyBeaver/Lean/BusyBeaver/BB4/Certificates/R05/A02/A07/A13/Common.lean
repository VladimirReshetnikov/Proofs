import BusyBeaver.BB4.Certificates.R05.A02.A07.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def fourthTableA02A07A13 : PTable :=
  thirdTableA02A07.set a07.next false a13
def beforeFifthA02A07A13 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a07) a13) a02
def fifthBranchA02A07A13 (fifth : GoAction) : Bool :=
  TNF.checkFrom leaf 101
    (TNF.grow
      (TNF.grow
        (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a07)
        a13)
      fifth)
    (fourthTableA02A07A13.set a02.next true fifth)
    (stepGo beforeFifthA02A07A13 fifth)
end SetTheory.BusyBeaver.BB4.Certificates
