import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a08_a10_a15_a12 : Guided.Work :=
  after [a08, a10, a15, a12]

def certificate_a08_a10_a15_a12 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a08_a10_a15_a12 :
    work_a08_a10_a15_a12.check certificate_a08_a10_a15_a12 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
