/-
  AuditMathlib.lean — assumption audit for the repository-root busy-beaver
  targets, the companion of `Audit.lean` for expensive certificate modules
  and mathlib-backed bridges that the standalone default aggregate
  deliberately excludes.

  Like `BusyBeaverMathlib.lean` itself, this file is NOT imported by the
  core `BusyBeaver.lean` facade; it is built from the repository-root Lake
  workspace, which supplies mathlib v4.31.0:

      lake build +BusyBeaver.AuditMathlib  # from the repository root

  Expected: only Lean's standard classical axioms
  (`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no `axiom`.
-/
import BusyBeaver.BB2
import BusyBeaver.BB3
import BusyBeaver.Mathlib

open SetTheory

-- the compiler interface, proved unconditionally from mathlib's
-- recursion theory and Turing-machine reductions
#check @BusyBeaver.totalRecursiveMathlib_hasEventuallyAtMostLowerBoundCompiler
#print axioms BusyBeaver.totalRecursiveMathlib_hasEventuallyAtMostLowerBoundCompiler

-- the headline: any busy-beaver score function eventually dominates
-- every mathlib-total-recursive function `Nat -> Nat`
#check @BusyBeaver.sigma_eventually_dominates_every_totalRecursiveMathlib
#print axioms BusyBeaver.sigma_eventually_dominates_every_totalRecursiveMathlib

-- the exhaustive two-state score classification
#check @BusyBeaver.BB2.all_tables_score_le_four
#check @BusyBeaver.BB2.upperBound_two
#check @BusyBeaver.BB2.exactScore_two
#check @BusyBeaver.BB2.sigma_two_eq_four
#print axioms BusyBeaver.BB2.all_tables_score_le_four
#print axioms BusyBeaver.BB2.upperBound_two
#print axioms BusyBeaver.BB2.sigma_two_eq_four

-- the independent exhaustive three-state score classification; its sharded
-- branch computations use ordinary kernel `decide`, not `native_decide`
#check @BusyBeaver.BB3.searchCoverage
#check @BusyBeaver.BB3.all_tables_score_le_six
#check @BusyBeaver.BB3.upperBound_three
#check @BusyBeaver.BB3.exactScore_three
#check @BusyBeaver.BB3.sigma_three_eq_six
#print axioms BusyBeaver.BB3.searchCoverage
#print axioms BusyBeaver.BB3.all_tables_score_le_six
#print axioms BusyBeaver.BB3.upperBound_three
#print axioms BusyBeaver.BB3.exactScore_three
#print axioms BusyBeaver.BB3.sigma_three_eq_six
