import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a03_a09_a13_a10 : Guided.Work :=
  after [a03, a09, a13, a10]

def certificate_a03_a09_a13_a10 : Guided.Certificate :=
  Guided.Certificate.bool3

theorem verified_a03_a09_a13_a10 :
    work_a03_a09_a13_a10.check certificate_a03_a09_a13_a10 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
