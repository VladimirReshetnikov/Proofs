import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a02_a15_a08_a08 : Guided.Work :=
  after [a11, a02, a15, a08, a08]

def certificate_a11_a02_a15_a08_a08 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a11_a02_a15_a08_a08 :
    work_a11_a02_a15_a08_a08.check certificate_a11_a02_a15_a08_a08 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
