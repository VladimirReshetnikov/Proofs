import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def fifthTableA02A07A08A15 : PTable :=
  fourthTableA02A07A08.set a05.next true a15
def beforeSixthA02A07A08A15 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a07) a08) a05) a15) a08
def sixthBranchA02A07A08A15 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 99
    (TNF.grow
      (TNF.grow
        (TNF.grow
          (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a07)
          a08)
        a15)
      sixth)
    (fifthTableA02A07A08A15.set (0 : Fin 4) true sixth)
    (stepGo beforeSixthA02A07A08A15 sixth)
end SetTheory.BusyBeaver.BB4.Certificates
