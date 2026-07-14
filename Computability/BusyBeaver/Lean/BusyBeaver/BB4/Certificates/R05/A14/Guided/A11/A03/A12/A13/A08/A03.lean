import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a03_a12_a13_a08_a03 : Guided.Work :=
  after [a11, a03, a12, a13, a08, a03]

def certificate_a11_a03_a12_a13_a08_a03 : Guided.Certificate :=
  Guided.Certificate.complete

theorem verified_a11_a03_a12_a13_a08_a03 :
    work_a11_a03_a12_a13_a08_a03.check certificate_a11_a03_a12_a13_a08_a03 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
