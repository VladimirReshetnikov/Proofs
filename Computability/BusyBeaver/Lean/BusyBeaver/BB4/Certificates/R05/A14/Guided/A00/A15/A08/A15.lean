import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a00_a15_a08_a15 : Guided.Work :=
  after [a00, a15, a08, a15]

def certificate_a00_a15_a08_a15 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a00_a15_a08_a15 :
    work_a00_a15_a08_a15.check certificate_a00_a15_a08_a15 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
