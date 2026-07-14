import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a03_a12_a13_a10 : Guided.Work :=
  after [a11, a03, a12, a13, a10]

def certificate_a11_a03_a12_a13_a10 : Guided.Certificate :=
  Guided.Certificate.suppliedHistory 4 2 explicitCertificate

theorem verified_a11_a03_a12_a13_a10 :
    work_a11_a03_a12_a13_a10.check certificate_a11_a03_a12_a13_a10 = true := by
  change NGram.historyCertificateCheck
    work_a11_a03_a12_a13_a10.table 4 2 explicitCertificate = true
  apply NGram.historyCertificateCheck_of_valid
  simpa [work_a11_a03_a12_a13_a10, explicitTable, explicitBlank] using explicitValid

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
