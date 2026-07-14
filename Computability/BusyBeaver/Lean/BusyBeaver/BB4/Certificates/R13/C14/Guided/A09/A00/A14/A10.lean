import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a09_a00_a14_a10 : Guided.Work :=
  after [a09, a00, a14, a10]

def certificate_a09_a00_a14_a10 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a09_a00_a14_a10 :
    work_a09_a00_a14_a10.check certificate_a09_a00_a14_a10 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
