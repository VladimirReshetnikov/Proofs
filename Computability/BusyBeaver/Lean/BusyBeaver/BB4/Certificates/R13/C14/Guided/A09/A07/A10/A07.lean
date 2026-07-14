import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a09_a07_a10_a07 : Guided.Work :=
  after [a09, a07, a10, a07]

def certificate_a09_a07_a10_a07 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a09_a07_a10_a07 :
    work_a09_a07_a10_a07.check certificate_a09_a07_a10_a07 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
