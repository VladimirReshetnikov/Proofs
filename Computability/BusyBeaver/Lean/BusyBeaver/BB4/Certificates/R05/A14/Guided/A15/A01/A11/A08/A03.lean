import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a15_a01_a11_a08_a03 : Guided.Work :=
  after [a15, a01, a11, a08, a03]

def certificate_a15_a01_a11_a08_a03 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a15_a01_a11_a08_a03 :
    work_a15_a01_a11_a08_a03.check certificate_a15_a01_a11_a08_a03 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
