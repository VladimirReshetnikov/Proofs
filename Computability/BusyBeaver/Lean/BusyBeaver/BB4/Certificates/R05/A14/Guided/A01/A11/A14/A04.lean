import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a01_a11_a14_a04 : Guided.Work :=
  after [a01, a11, a14, a04]

def certificate_a01_a11_a14_a04 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a01_a11_a14_a04 :
    work_a01_a11_a14_a04.check certificate_a01_a11_a14_a04 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
