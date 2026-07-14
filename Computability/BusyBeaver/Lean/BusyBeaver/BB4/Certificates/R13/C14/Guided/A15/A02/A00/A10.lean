import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a15_a02_a00_a10 : Guided.Work :=
  after [a15, a02, a00, a10]

def certificate_a15_a02_a00_a10 : Guided.Certificate :=
  Guided.Certificate.bool3

theorem verified_a15_a02_a00_a10 :
    work_a15_a02_a00_a10.check certificate_a15_a02_a00_a10 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
