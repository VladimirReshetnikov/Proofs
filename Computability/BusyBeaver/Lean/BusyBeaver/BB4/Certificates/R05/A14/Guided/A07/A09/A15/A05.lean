import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a07_a09_a15_a05 : Guided.Work :=
  after [a07, a09, a15, a05]

def certificate_a07_a09_a15_a05 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a07_a09_a15_a05 :
    work_a07_a09_a15_a05.check certificate_a07_a09_a15_a05 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
