import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a15_a08_a02_a02 : Guided.Work :=
  after [a15, a08, a02, a02]

def certificate_a15_a08_a02_a02 : Guided.Certificate :=
  Guided.Certificate.bool3

theorem verified_a15_a08_a02_a02 :
    work_a15_a08_a02_a02.check certificate_a15_a08_a02_a02 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
