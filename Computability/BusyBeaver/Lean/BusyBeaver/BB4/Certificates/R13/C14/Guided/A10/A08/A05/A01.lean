import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a10_a08_a05_a01 : Guided.Work :=
  after [a10, a08, a05, a01]

def certificate_a10_a08_a05_a01 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a10_a08_a05_a01 :
    work_a10_a08_a05_a01.check certificate_a10_a08_a05_a01 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
