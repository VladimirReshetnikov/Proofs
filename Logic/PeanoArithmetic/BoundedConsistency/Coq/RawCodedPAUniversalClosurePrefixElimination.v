(**
  One exact proof-producing step out of an iterated universal closure.

  [RawCodedUniversalClosure] is oriented from the unclosed input toward its
  universally quantified output.  A proof consumer runs in the opposite
  direction.  The theorem below is the bridge needed by that reverse orbit:
  it verifies that an explicitly supplied [count]-prefix is the immediate
  child of a [(count + 1)]-closure, then applies the represented
  single-substitution graph through the genuine [RP_allE] constructor.

  Notice that neither formula code is decoded.  Functionality of the
  universal-closure graph identifies the caller's prefix with the predecessor
  exposed by successor inversion, so the result remains valid for
  nonstandard counts and nonstandard formula codes.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedProofAllEConstructor RawCodedPALocalProofExistential
  RawCodedPALocalProofUniversalElimination.

Module PABoundedRawCodedPAUniversalClosurePrefixElimination.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofUniversalElimination.

(** Eliminate the outermost quantifier of an arbitrary model-coded closure.

    The output root is definitionally the exact [RP_allE] node whose child is
    the incoming proof.  Keeping that root visible is important for the later
    beta-coded orbit: its successor row can store the root without choosing a
    proof by classical description. *)
Theorem raw_codedPALocalProofOf_universalClosure_prefix_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      count body universal prefix replacement conclusion context child,
  RawCodedUniversalClosure M (raw_succ M count) body universal ->
  RawCodedUniversalClosure M count body prefix ->
  RawCodedFormulaSingleSubstitution M replacement prefix conclusion ->
  RawCodedPALocalProofOf M context universal child ->
  RawCodedPALocalProofOf M context conclusion
    (rawProofAllERoot M context prefix replacement child).
Proof.
  intros M hPA count body universal prefix replacement conclusion
    context child hsuccessor hprefix hsubstitution hchild.
  destruct (raw_codedUniversalClosure_succ_inversion M hPA
    count body universal hsuccessor) as
    [invertedPrefix [hinvertedPrefix huniversal]].
  assert (hprefixEq : invertedPrefix = prefix).
  {
    exact (raw_codedUniversalClosure_functional M hPA
      count body invertedPrefix prefix hinvertedPrefix hprefix).
  }
  subst invertedPrefix. subst universal.
  exact (raw_codedPALocalProofOf_allE M hPA
    context prefix replacement conclusion child hchild hsubstitution).
Qed.

End PABoundedRawCodedPAUniversalClosurePrefixElimination.
