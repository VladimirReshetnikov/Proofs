import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a03_a10_a01_a14 : Guided.Work :=
  after [a03, a10, a01, a14]

def certificate_a03_a10_a01_a14 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a03_a10_a01_a14 :
    work_a03_a10_a01_a14.check certificate_a03_a10_a01_a14 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
