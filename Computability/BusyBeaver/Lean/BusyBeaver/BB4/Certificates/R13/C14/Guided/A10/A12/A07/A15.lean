import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a10_a12_a07_a15 : Guided.Work :=
  after [a10, a12, a07, a15]

def certificate_a10_a12_a07_a15 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a10_a12_a07_a15 :
    work_a10_a12_a07_a15.check certificate_a10_a12_a07_a15 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
