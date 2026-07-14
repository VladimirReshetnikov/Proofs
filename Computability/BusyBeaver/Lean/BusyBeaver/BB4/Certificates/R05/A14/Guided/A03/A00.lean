import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a03_a00 : Guided.Work :=
  after [a03, a00]

def certificate_a03_a00 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a03_a00 :
    work_a03_a00.check certificate_a03_a00 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
