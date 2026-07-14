import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a15_a08_a07_a05 : Guided.Work :=
  after [a15, a08, a07, a05]

def certificate_a15_a08_a07_a05 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a15_a08_a07_a05 :
    work_a15_a08_a07_a05.check certificate_a15_a08_a07_a05 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
