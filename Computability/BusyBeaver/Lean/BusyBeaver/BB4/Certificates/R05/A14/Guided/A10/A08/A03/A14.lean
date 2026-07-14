import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a10_a08_a03_a14 : Guided.Work :=
  after [a10, a08, a03, a14]

def certificate_a10_a08_a03_a14 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a10_a08_a03_a14 :
    work_a10_a08_a03_a14.check certificate_a10_a08_a03_a14 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
