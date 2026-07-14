import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a10_a15_a05 : Guided.Work :=
  after [a10, a15, a05]

def certificate_a10_a15_a05 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a10_a15_a05 :
    work_a10_a15_a05.check certificate_a10_a15_a05 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
