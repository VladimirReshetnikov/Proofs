import BusyBeaver.BB4.Certificates.R05.A02.A07.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def fourthTableA02A07A10 : PTable :=
  thirdTableA02A07.set a07.next false a10
def beforeFifthA02A07A10 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a07) a10) a07
def fifthBranchA02A07A10 (fifth : GoAction) : Bool :=
  TNF.checkFrom leaf 101
    (TNF.grow
      (TNF.grow
        (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a07)
        a10)
      fifth)
    (fourthTableA02A07A10.set a07.next true fifth)
    (stepGo beforeFifthA02A07A10 fifth)
end SetTheory.BusyBeaver.BB4.Certificates
