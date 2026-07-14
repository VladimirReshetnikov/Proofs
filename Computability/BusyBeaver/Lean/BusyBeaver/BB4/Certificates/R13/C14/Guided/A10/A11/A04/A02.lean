import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a10_a11_a04_a02 : Guided.Work :=
  after [a10, a11, a04, a02]

def certificate_a10_a11_a04_a02 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a10_a11_a04_a02 :
    work_a10_a11_a04_a02.check certificate_a10_a11_a04_a02 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
