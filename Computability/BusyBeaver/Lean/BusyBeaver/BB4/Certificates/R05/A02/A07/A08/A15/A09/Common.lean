import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.A15.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def sixthTableA02A07A08A15A09 : PTable :=
  fifthTableA02A07A08A15.set (0 : Fin 4) true a09
def beforeSeventhA02A07A08A15A09 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a07) a08) a05) a15) a08) a09) a02) a07) a08) a05) a15
def seventhBranchA02A07A08A15A09 (seventh : GoAction) : Bool :=
  TNF.checkFrom leaf 93
    (TNF.grow
      (TNF.grow
        (TNF.grow
          (TNF.grow
            (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a07)
            a08)
          a15)
        a09)
      seventh)
    (sixthTableA02A07A08A15A09.set a07.next true seventh)
    (stepGo beforeSeventhA02A07A08A15A09 seventh)
end SetTheory.BusyBeaver.BB4.Certificates
