import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a01_a11_a13_a07 : Guided.Work :=
  after [a01, a11, a13, a07]

def certificate_a01_a11_a13_a07 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a01_a11_a13_a07 :
    work_a01_a11_a13_a07.check certificate_a01_a11_a13_a07 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
