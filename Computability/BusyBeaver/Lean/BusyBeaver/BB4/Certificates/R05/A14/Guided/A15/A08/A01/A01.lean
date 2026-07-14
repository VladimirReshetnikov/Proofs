import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a15_a08_a01_a01 : Guided.Work :=
  after [a15, a08, a01, a01]

def certificate_a15_a08_a01_a01 : Guided.Certificate :=
  Guided.Certificate.bool3

theorem verified_a15_a08_a01_a01 :
    work_a15_a08_a01_a01.check certificate_a15_a08_a01_a01 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
