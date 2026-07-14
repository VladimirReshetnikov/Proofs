import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.A11.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def sixthTableA02A03A13A11A04 : PTable :=
  fifthTableA02A03A13A11.set a05.next true a04
def beforeSeventhA02A03A13A11A04 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a03) a13) a02) a11) a13) a04) a05) a02) a03) a13) a02) a11
def seventhBranchA02A03A13A11A04 (seventh : GoAction) : Bool :=
  TNF.checkFrom leaf 92
    (TNF.grow
      (TNF.grow
        (TNF.grow
          (TNF.grow (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a03) a13)
          a11)
        a04)
      seventh)
    (sixthTableA02A03A13A11A04.set a03.next true seventh)
    (stepGo beforeSeventhA02A03A13A11A04 seventh)
end SetTheory.BusyBeaver.BB4.Certificates
