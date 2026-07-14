import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A12.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def sixthTableA02A03A13A12A10 : PTable :=
  fifthTableA02A03A13A12.set a03.next true a10
def beforeSeventhA02A03A13A12A10 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a03) a13) a02) a12) a05) a02) a03) a10) a03) a13) a02) a12) a05
def seventhBranchA02A03A13A12A10 (seventh : GoAction) : Bool :=
  TNF.checkFrom leaf 91
    (TNF.grow
      (TNF.grow
        (TNF.grow
          (TNF.grow (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a03) a13)
          a12)
        a10)
      seventh)
    (sixthTableA02A03A13A12A10.set a05.next true seventh)
    (stepGo beforeSeventhA02A03A13A12A10 seventh)
end SetTheory.BusyBeaver.BB4.Certificates
