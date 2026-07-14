import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a09_a04_a10_a02 : Guided.Work :=
  after [a09, a04, a10, a02]

def certificate_a09_a04_a10_a02 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a09_a04_a10_a02 :
    work_a09_a04_a10_a02.check certificate_a09_a04_a10_a02 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
