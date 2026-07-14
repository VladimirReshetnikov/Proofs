import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a07_a11_a08_a10 : Guided.Work :=
  after [a07, a11, a08, a10]

def certificate_a07_a11_a08_a10 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a07_a11_a08_a10 :
    work_a07_a11_a08_a10.check certificate_a07_a11_a08_a10 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
