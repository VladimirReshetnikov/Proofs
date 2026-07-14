import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a09_a11_a14_a10 : Guided.Work :=
  after [a09, a11, a14, a10]

def certificate_a09_a11_a14_a10 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a09_a11_a14_a10 :
    work_a09_a11_a14_a10.check certificate_a09_a11_a14_a10 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
