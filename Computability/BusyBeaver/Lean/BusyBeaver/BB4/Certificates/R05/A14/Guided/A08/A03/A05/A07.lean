import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a08_a03_a05_a07 : Guided.Work :=
  after [a08, a03, a05, a07]

def certificate_a08_a03_a05_a07 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a08_a03_a05_a07 :
    work_a08_a03_a05_a07.check certificate_a08_a03_a05_a07 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
