(**
  Raw-model reduction for the transparent canonical checker trace.

  [CanonicalRestrictedPAProofFormula] has the same public input convention
  as the earlier checker graph: free variable zero is the external hierarchy
  bound and free variable one is the candidate proof code.  We therefore use
  the same [fixedBoundSubstitution] when fixing an external bound [n].

  The result below is deliberately conditional.  Standard execution of the
  compiled Minsky machine does not rule out a trace whose entries are elements
  of a nonstandard PA model.  Raw-model completeness reduces the desired PA
  proof exactly to rejection of such canonical traces in every raw PA model;
  it does not supply that rejection.
*)

From Stdlib Require Import List Arith Lia Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedCheckerFormula CodedCheckerRawReduction
  CanonicalCheckerTrace RawModelCompleteness.

Set Implicit Arguments.

Import ListNotations.

Module PABoundedCanonicalCheckerRawReduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedCheckerFormula.
Import PABoundedCodedCheckerRawReduction.
Import PABoundedCanonicalCheckerTrace.
Import PABoundedRawModelCompleteness.

(** Fix variable zero of the canonical graph to the standard numeral [n],
    expose its variable one as the sole bound certificate variable, and then
    universally reject that certificate.  Spare variables are sent to zero
    by [fixedBoundSubstitution], just as for the executable checker graph. *)
Definition NoCanonicalRestrictedPAProofFormula (n : nat) : formula :=
  pAll (pImp
    (Formula.subst (fixedBoundSubstitution n)
      CanonicalRestrictedPAProofFormula)
    pBot).

(** Substitution leaves at most variable zero free; the outer universal
    quantifier consequently closes the formula.  This argument does not need
    a free-variable analysis of the large generated trace formula. *)
Theorem NoCanonicalRestrictedPAProofFormula_sentence : forall n,
  Formula.Sentence (NoCanonicalRestrictedPAProofFormula n).
Proof.
  intros n k hfree.
  unfold NoCanonicalRestrictedPAProofFormula in hfree.
  change
    (Formula.Free (S k)
      (Formula.subst (fixedBoundSubstitution n)
        CanonicalRestrictedPAProofFormula) \/ False)
    in hfree.
  destruct hfree as [hfree | hfree]; [| contradiction].
  pose proof (@formula_free_subst_below
    CanonicalRestrictedPAProofFormula 1
    (fixedBoundSubstitution n) (S k)
    (@fixedBoundSubstitution_free_below_one n) hfree).
  lia.
Qed.

(** The raw environment uses precisely the public checker input order:
    [0] is the externally fixed standard numeral, [1] is an arbitrary model
    element serving as certificate, and every spare input is zero. *)
Definition rawCanonicalRestrictedCheckerEnv (M : RawPAModel)
    (n : nat) (p : M) (k : nat) : M :=
  match k with
  | 0 => rawStandardNumeral M n
  | 1 => p
  | _ => raw_zero M
  end.

Lemma raw_fixedBoundSubstitution_canonical_env : forall
    (M : RawPAModel) n (p : M) (e : nat -> M),
  (fun k => raw_term_eval M (scons M p e)
    (fixedBoundSubstitution n k)) =
  @rawCanonicalRestrictedCheckerEnv M n p.
Proof.
  intros M n p e.
  rewrite raw_fixedBoundSubstitution_env.
  reflexivity.
Qed.

(** Exact evaluation in an arbitrary law-free arithmetic structure.  Notice
    that the right side still says satisfaction of the explicit trace
    formula; it does not replace this by execution of the Rocq Boolean
    checker, which would be unsound for nonstandard model elements. *)
Theorem raw_NoCanonicalRestrictedPAProofFormula_iff : forall
    (M : RawPAModel) n (e : nat -> M),
  raw_formula_sat M e (NoCanonicalRestrictedPAProofFormula n) <->
  forall p : M,
    ~ raw_formula_sat M (@rawCanonicalRestrictedCheckerEnv M n p)
        CanonicalRestrictedPAProofFormula.
Proof.
  intros M n e.
  unfold NoCanonicalRestrictedPAProofFormula.
  change
    ((forall p : M,
        raw_formula_sat M (scons M p e)
          (Formula.subst (fixedBoundSubstitution n)
            CanonicalRestrictedPAProofFormula) -> False) <->
      forall p : M,
        ~ raw_formula_sat M
          (@rawCanonicalRestrictedCheckerEnv M n p)
          CanonicalRestrictedPAProofFormula).
  split.
  - intros hall p htrace.
    apply (hall p).
    apply (proj2 (raw_formula_sat_subst M
      CanonicalRestrictedPAProofFormula
      (fixedBoundSubstitution n) (scons M p e))).
    rewrite raw_fixedBoundSubstitution_canonical_env.
    exact htrace.
  - intros hreject p hsubst.
    apply (hreject p).
    rewrite <- (@raw_fixedBoundSubstitution_canonical_env M n p e).
    apply (proj1 (raw_formula_sat_subst M
      CanonicalRestrictedPAProofFormula
      (fixedBoundSubstitution n) (scons M p e))).
    exact hsubst.
Qed.

(** The exact genuinely nonstandard obligation left by the construction. *)
Definition RawCanonicalRestrictedCheckerRejection (n : nat) : Prop :=
  forall (M : RawPAModel), RawPASatisfies M -> forall p : M,
    ~ raw_formula_sat M (@rawCanonicalRestrictedCheckerEnv M n p)
        CanonicalRestrictedPAProofFormula.

(** Raw-model completeness turns model-independent trace rejection into an
    object-language PA derivation of the fixed-bound consistency sentence. *)
Theorem PA_BProv_NoCanonicalRestrictedPAProofFormula_of_raw_rejection :
  forall n,
  RawCanonicalRestrictedCheckerRejection n ->
  Formula.BProv Formula.Ax_s []
    (NoCanonicalRestrictedPAProofFormula n).
Proof.
  intros n hreject.
  apply PA_BProv_of_raw_valid.
  - apply NoCanonicalRestrictedPAProofFormula_sentence.
  - intros M hPA e.
    apply (proj2 (@raw_NoCanonicalRestrictedPAProofFormula_iff M n e)).
    exact (hreject M hPA).
Qed.

(** Raw PA soundness supplies the converse.  Consequently the rejection
    obligation is equivalent to, rather than merely sufficient for, the
    desired object-level theorem for this canonical sentence. *)
Theorem PA_BProv_NoCanonicalRestrictedPAProofFormula_iff_raw_rejection :
  forall n,
  Formula.BProv Formula.Ax_s []
      (NoCanonicalRestrictedPAProofFormula n) <->
  RawCanonicalRestrictedCheckerRejection n.
Proof.
  intro n. split.
  - intros hproof M hPA p htrace.
    pose proof (@raw_sat_of_BProv_axs M
      (NoCanonicalRestrictedPAProofFormula n) hPA hproof
      (fun _ => raw_zero M)) as hsat.
    apply (proj1 (@raw_NoCanonicalRestrictedPAProofFormula_iff M n
      (fun _ => raw_zero M)) hsat p).
    exact htrace.
  - apply PA_BProv_NoCanonicalRestrictedPAProofFormula_of_raw_rejection.
Qed.

End PABoundedCanonicalCheckerRawReduction.
