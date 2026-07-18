(**
  A standard-model PA formula for the exact restricted-proof checker.

  [RestrictedPAProofFormula] has two distinguished free variables: variable
  zero is the external quantifier-group bound and variable one is the natural
  certificate code.  Its standard-model semantics is exactly

      checkRestrictedPAProofCode bound code = true.

  The formula is obtained through the repository's verified route from
  extracted computability to a Diophantine graph and then to first-order PA.
  Classical epsilon selects one graph formula from the proved existence
  theorem; it does not add a semantic axiom.

  This is deliberately not advertised as the requested object-level
  reflection theorem.  In particular, [NoRestrictedPAProofFormula n] below
  is now an actual closed PA formula and is true in the standard model, but a
  derivation [PA |- NoRestrictedPAProofFormula n] still requires fixed-level
  partial truth sound for nonstandard certificate and formula codes.
*)

From Stdlib Require Import Arith Bool Lia FunctionalExtensionality.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import DiophantineFormula ComputableFormula.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedSyntax CodedProof
  CodedCheckerComputability CodedCheckerStructuralComputability
  CodedCheckerDecisionComputability.

From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LBool LNat.

Set Implicit Arguments.

Module PABoundedCodedCheckerFormula.

Import PA.
Import PABoundedCodedProof.
Import PABoundedCodedCheckerDecisionComputability.
Import GenEncode.

(** Natural-valued characteristic function used by the generic binary graph
    theorem. *)
Definition restrictedProofFlag (n p : nat) : nat :=
  if checkRestrictedPAProofCode n p then 1 else 0.

Lemma one_eq_restrictedProofFlag : forall n p,
  1 = restrictedProofFlag n p <->
  checkRestrictedPAProofCode n p = true.
Proof.
  intros n p. unfold restrictedProofFlag.
  destruct (checkRestrictedPAProofCode n p); cbn; split; congruence.
Qed.

#[local] Instance term_restrictedProofFlag : computable restrictedProofFlag.
Proof.
  extract.
Qed.

(** The generic graph convention is output-first.  This substitution fixes
    that output to one and exposes the two checker inputs as variables zero
    and one.  Unused variables are normalized to zero. *)
Definition checkerTruthSubstitution (k : nat) : term :=
  match k with
  | 0 => Term.numeral 1
  | 1 => tVar 0
  | 2 => tVar 1
  | _ => tZero
  end.

Definition RestrictedPAProofFormula : formula :=
  Formula.subst checkerTruthSubstitution
    (binaryGraphFormula restrictedProofFlag).

Lemma checkerTruthSubstitution_env (e : nat -> nat) :
  (fun k => Term.eval natModel e (checkerTruthSubstitution k)) =
  graphEnv (binaryInputs (e 0) (e 1)) 1.
Proof.
  apply functional_extensionality. intros [|[|[|k]]].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold graphEnv, vectorEnv, binaryInputs, checkerTruthSubstitution.
    cbn. destruct (lt_dec (S (S (S k))) 3); [lia | reflexivity].
Qed.

Theorem RestrictedPAProofFormula_spec (e : nat -> nat) :
  Formula.Sat natModel e RestrictedPAProofFormula <->
  checkRestrictedPAProofCode (e 0) (e 1) = true.
Proof.
  unfold RestrictedPAProofFormula.
  rewrite Formula.Sat_subst, checkerTruthSubstitution_env.
  rewrite (binaryGraphFormula_correct term_restrictedProofFlag
    (binaryInputs (e 0) (e 1)) 1).
  cbn [binaryGraph binaryInputs Vector.nth].
  apply one_eq_restrictedProofFlag.
Qed.

(** Fix the bound to a metatheoretic numeral and bind the certificate code.
    The resulting formula is closed because all spare graph variables were
    normalized to zero above. *)
Definition fixedBoundSubstitution (n k : nat) : term :=
  match k with
  | 0 => Term.numeral n
  | 1 => tVar 0
  | _ => tZero
  end.

Definition NoRestrictedPAProofFormula (n : nat) : formula :=
  pAll (pImp
    (Formula.subst (fixedBoundSubstitution n) RestrictedPAProofFormula)
    pBot).

Lemma fixedBoundSubstitution_env (n p : nat) (e : nat -> nat) :
  (fun k => Term.eval natModel (scons nat p e)
    (fixedBoundSubstitution n k)) =
  fun k => match k with 0 => n | 1 => p | _ => 0 end.
Proof.
  apply functional_extensionality. intros [|[|k]].
  - apply Term.eval_numeral_natModel.
  - reflexivity.
  - reflexivity.
Qed.

Theorem NoRestrictedPAProofFormula_spec (n : nat) (e : nat -> nat) :
  Formula.Sat natModel e (NoRestrictedPAProofFormula n) <->
  forall p, checkRestrictedPAProofCode n p = false.
Proof.
  unfold NoRestrictedPAProofFormula. cbn [Formula.Sat].
  split.
  - intros h p.
    destruct (checkRestrictedPAProofCode n p) eqn:hcheck;
      [exfalso | reflexivity].
    apply (h p).
    rewrite Formula.Sat_subst, fixedBoundSubstitution_env.
    apply (proj2 (RestrictedPAProofFormula_spec
      (fun k => match k with 0 => n | 1 => p | _ => 0 end))).
    exact hcheck.
  - intros h p hsat.
    rewrite Formula.Sat_subst, fixedBoundSubstitution_env in hsat.
    apply RestrictedPAProofFormula_spec in hsat.
    rewrite (h p) in hsat. discriminate.
Qed.

Corollary NoRestrictedPAProofFormula_standard_true
    (n : nat) (e : nat -> nat) :
  Formula.Sat natModel e (NoRestrictedPAProofFormula n).
Proof.
  apply (proj2 (NoRestrictedPAProofFormula_spec n e)).
  apply checkedRestrictedPA_consistent_standard.
Qed.

End PABoundedCodedCheckerFormula.
