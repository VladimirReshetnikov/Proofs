import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a10_a04_a07_a14 : Guided.Work :=
  after [a10, a04, a07, a14]

def certificate_a10_a04_a07_a14 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a10_a04_a07_a14 :
    work_a10_a04_a07_a14.check certificate_a10_a04_a07_a14 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
