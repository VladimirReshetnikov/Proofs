import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a08_a03_a05_a08 : Guided.Work :=
  after [a08, a03, a05, a08]

def certificate_a08_a03_a05_a08 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a08_a03_a05_a08 :
    work_a08_a03_a05_a08.check certificate_a08_a03_a05_a08 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
