import BusyBeaver.BB4.Certificates.R05.A02.A07.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def fourthTableA02A07A08 : PTable :=
  thirdTableA02A07.set a07.next false a08
def beforeFifthA02A07A08 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a07) a08) a05
def fifthBranchA02A07A08 (fifth : GoAction) : Bool :=
  TNF.checkFrom leaf 101
    (TNF.grow
      (TNF.grow
        (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a07)
        a08)
      fifth)
    (fourthTableA02A07A08.set a05.next true fifth)
    (stepGo beforeFifthA02A07A08 fifth)
end SetTheory.BusyBeaver.BB4.Certificates
