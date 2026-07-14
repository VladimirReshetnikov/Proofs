import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a01_a03_a15 : Guided.Work :=
  after [a01, a03, a15]

def certificate_a01_a03_a15 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a01_a03_a15 :
    work_a01_a03_a15.check certificate_a01_a03_a15 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
