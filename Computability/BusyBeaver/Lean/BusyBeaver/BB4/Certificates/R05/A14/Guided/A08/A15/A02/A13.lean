import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a08_a15_a02_a13 : Guided.Work :=
  after [a08, a15, a02, a13]

def certificate_a08_a15_a02_a13 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a08_a15_a02_a13 :
    work_a08_a15_a02_a13.check certificate_a08_a15_a02_a13 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
