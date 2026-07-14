import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a07_a10_a05 : Guided.Work :=
  after [a07, a10, a05]

def certificate_a07_a10_a05 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a07_a10_a05 :
    work_a07_a10_a05.check certificate_a07_a10_a05 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
