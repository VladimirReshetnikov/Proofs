/-
  Trust-surface audit for the exact four-state Busy Beaver score.

  This module is intentionally separate from the default BusyBeaver facade:

      lake --dir Computability/BusyBeaver/Lean build +BusyBeaver.BB4.Audit

  The output records every axiom used by the assembled certificate theorem,
  its semantic upper bound, and the final exact-score and Sigma statements.
-/

import BusyBeaver.BB4

open SetTheory

#check @BusyBeaver.BB4.Certificates.verifyRoot_rootCertificate
#check @BusyBeaver.BB4.searchCoverage
#check @BusyBeaver.BB4.all_tables_score_le_thirteen
#check @BusyBeaver.BB4.upperBound_four
#check @BusyBeaver.BB4.exactScore_four
#check @BusyBeaver.BB4.sigma_four_eq_thirteen

#print axioms BusyBeaver.BB4.Certificates.verifyRoot_rootCertificate
#print axioms BusyBeaver.BB4.searchCoverage
#print axioms BusyBeaver.BB4.all_tables_score_le_thirteen
#print axioms BusyBeaver.BB4.upperBound_four
#print axioms BusyBeaver.BB4.exactScore_four
#print axioms BusyBeaver.BB4.sigma_four_eq_thirteen
