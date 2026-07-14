import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a08_a14_a03 : Guided.Work :=
  after [a11, a08, a14, a03]

def certificate_a11_a08_a14_a03 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a11_a08_a14_a03 :
    work_a11_a08_a14_a03.check certificate_a11_a08_a14_a03 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
