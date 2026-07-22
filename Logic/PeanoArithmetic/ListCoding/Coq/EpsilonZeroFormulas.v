(* ===================================================================== *)
(*  EpsilonZeroFormulas.v                                                *)
(*                                                                       *)
(*  Actual PA formula values for the executable epsilon-zero notation     *)
(*  predicates and operations.                                           *)
(*                                                                       *)
(*  There are two boundaries worth keeping visible:                      *)
(*                                                                       *)
(*  - the [computable] instances below are constructive extraction       *)
(*    certificates for the executable definitions in EpsilonZero.v;      *)
(*  - [unaryGraphFormula] and [binaryGraphFormula] from                   *)
(*    ComputableFormula.v use classical epsilon only to choose an actual  *)
(*    PA formula from a constructively proved Prop-level existence.       *)
(*                                                                       *)
(*  Every selected graph formula is normalized by substitution before it  *)
(*  is exposed here.  Besides arranging the requested variables, that     *)
(*  substitution sends all unused free variables to zero.  Thus the       *)
(*  specifications hold for arbitrary environments, even though the      *)
(*  epsilon-selected formula could syntactically mention irrelevant high  *)
(*  variables.                                                           *)
(* ===================================================================== *)

From Stdlib Require Import Arith Bool Lia List PeanoNat Vector.
From Stdlib Require Import Logic.FunctionalExtensionality.

From PAHF Require Import PAHF.
From PAListCoding Require Import
  EpsilonZero EpsilonZeroLaws DiophantineFormula ComputableFormula.

From Undecidability.L.Datatypes Require Import LBool LNat LProd.
From Undecidability.L.Tactics Require Import GenEncode.

Module PAEpsilonZeroFormulas.

Import PAEpsilonZero PAEpsilonZeroLaws.
Import GenEncode.

(** * Boolean decision procedures for the Prop-level predicates *)

Definition comparisonLtBool (c : comparison) : bool :=
  match c with Lt => true | _ => false end.

Definition topBelowBool (bound o : ONote) : bool :=
  match o with
  | ozero => true
  | oadd e _ _ => comparisonLtBool (onoteCompare e bound)
  end.

Fixpoint nfBool (a : ONote) : bool :=
  match a with
  | ozero => true
  | oadd e _ r => nfBool e && (nfBool r && topBelowBool e r)
  end.

Lemma comparisonLtBool_spec : forall c,
  comparisonLtBool c = true <-> c = Lt.
Proof. intros []; cbn; split; congruence. Qed.

Lemma topBelowBool_spec : forall bound o,
  topBelowBool bound o = true <-> PAEpsilonZeroLaws.TopBelow bound o.
Proof.
  intros bound [|e c r]; cbn [topBelowBool TopBelow].
  - tauto.
  - apply comparisonLtBool_spec.
Qed.

Lemma nfBool_spec : forall a, nfBool a = true <-> NF a.
Proof.
  induction a as [|e IHe c r IHr]; cbn [nfBool NF].
  - tauto.
  - rewrite Bool.andb_true_iff, Bool.andb_true_iff,
      IHe, IHr, topBelowBool_spec.
    reflexivity.
Qed.

Definition validCodeBool (code : nat) : bool := nfBool (decode code).

Definition ordinalLTBool (a b : nat) : bool :=
  validCodeBool a &&
    (validCodeBool b && comparisonLtBool (onoteCompare (decode a) (decode b))).

Lemma validCodeBool_spec : forall code,
  validCodeBool code = true <-> ValidOrdinalCode code.
Proof. intro code. apply nfBool_spec. Qed.

Lemma ordinalLTBool_spec : forall a b,
  ordinalLTBool a b = true <-> OrdinalLT a b.
Proof.
  intros a b.
  unfold ordinalLTBool, OrdinalLT.
  rewrite Bool.andb_true_iff, Bool.andb_true_iff,
    !validCodeBool_spec, comparisonLtBool_spec.
  reflexivity.
Qed.

Definition truthNat (b : bool) : nat := if b then 1 else 0.
Definition validCodeFlag (code : nat) : nat := truthNat (validCodeBool code).
Definition ordinalLTFlag (a b : nat) : nat := truthNat (ordinalLTBool a b).

Lemma one_eq_truthNat : forall b, 1 = truthNat b <-> b = true.
Proof. intros []; cbn; split; congruence. Qed.

Lemma one_eq_validCodeFlag : forall code,
  1 = validCodeFlag code <-> ValidOrdinalCode code.
Proof.
  intro code. unfold validCodeFlag.
  rewrite one_eq_truthNat. apply validCodeBool_spec.
Qed.

Lemma one_eq_ordinalLTFlag : forall a b,
  1 = ordinalLTFlag a b <-> OrdinalLT a b.
Proof.
  intros a b. unfold ordinalLTFlag.
  rewrite one_eq_truthNat. apply ordinalLTBool_spec.
Qed.

(** * Constructive extraction certificates *)

(* The extraction framework needs encodings for the two inductive result
   types traversed by the ordinal algorithms. *)
MetaRocq Run (tmGenEncode "comparison_enc" comparison).
#[local] Hint Resolve comparison_enc_correct : Lrewrite.

#[local] Instance term_comparison_Eq : computable Eq.
Proof. extract constructor. Qed.
#[local] Instance term_comparison_Lt : computable Lt.
Proof. extract constructor. Qed.
#[local] Instance term_comparison_Gt : computable Gt.
Proof. extract constructor. Qed.

MetaRocq Run (tmGenEncode "onote_enc" ONote).
#[local] Hint Resolve onote_enc_correct : Lrewrite.

#[local] Instance term_ozero : computable ozero.
Proof. extract constructor. Qed.
#[local] Instance term_oadd : computable oadd.
Proof. extract constructor. Qed.

(* [Nat.sqrt] is a transparent wrapper around this structurally recursive
   iterator, so registering the iterator makes square unpairing extractible. *)
#[local] Instance term_nat_sqrt_iter : computable Nat.sqrt_iter.
Proof. extract. Qed.
#[local] Instance term_nat_sqrt : computable Nat.sqrt.
Proof. extract. Qed.
#[local] Instance term_nat_compare : computable Nat.compare.
Proof. extract. Qed.

#[local] Instance term_squarePair : computable squarePair.
Proof. extract. Qed.
#[local] Instance term_squareUnpair : computable squareUnpair.
Proof. extract. Qed.
#[local] Instance term_onoteCompare : computable onoteCompare.
Proof. extract. Qed.
#[local] Instance term_encode : computable encode.
Proof. extract. Qed.
#[local] Instance term_decodeFuel : computable decodeFuel.
Proof. extract. Qed.
#[local] Instance term_decode : computable decode.
Proof. extract. Qed.

#[local] Instance term_comparisonLtBool : computable comparisonLtBool.
Proof. extract. Qed.
#[local] Instance term_topBelowBool : computable topBelowBool.
Proof. extract. Qed.
#[local] Instance term_nfBool : computable nfBool.
Proof. extract. Qed.
#[local] Instance term_validCodeBool : computable validCodeBool.
Proof. extract. Qed.
#[local] Instance term_ordinalLTBool : computable ordinalLTBool.
Proof. extract. Qed.
#[local] Instance term_truthNat : computable truthNat.
Proof. extract. Qed.

#[local] Instance term_validCodeFlag : computable validCodeFlag.
Proof. extract. Qed.
#[local] Instance term_ordinalLTFlag : computable ordinalLTFlag.
Proof. extract. Qed.

#[local] Instance term_onoteAddAux : computable onoteAddAux.
Proof. extract. Qed.
#[local] Instance term_onoteAdd : computable onoteAdd.
Proof. extract. Qed.
#[local] Instance term_onoteSub : computable onoteSub.
Proof. extract. Qed.
#[local] Instance term_coefficientProductPred :
    computable coefficientProductPred.
Proof. extract. Qed.
#[local] Instance term_onoteMul : computable onoteMul.
Proof. extract. Qed.
#[local] Instance term_onoteSplit' : computable onoteSplit'.
Proof. extract. Qed.
#[local] Instance term_onoteSplit : computable onoteSplit.
Proof. extract. Qed.
#[local] Instance term_onoteScale : computable onoteScale.
Proof. extract. Qed.
#[local] Instance term_onoteMulNat : computable onoteMulNat.
Proof. extract. Qed.
#[local] Instance term_onotePowAux : computable onotePowAux.
Proof. extract. Qed.
#[local] Instance term_onotePowAux2 : computable onotePowAux2.
Proof. extract. Qed.
#[local] Instance term_onotePow : computable onotePow.
Proof. extract. Qed.

#[local] Instance term_addCode : computable addCode.
Proof. extract. Qed.
#[local] Instance term_mulCode : computable mulCode.
Proof. extract. Qed.
#[local] Instance term_powCode : computable powCode.
Proof. extract. Qed.

(** * Normalized graph and truth formulae *)

(* Old graph variables are [result,input] or [result,left,right].  These
   substitutions both arrange the public variables and set every unused
   old variable to zero. *)
Definition unaryTruthSubstitution (n : nat) : PA.term :=
  match n with
  | 0 => PA.Term.numeral 1
  | 1 => PA.tVar 0
  | _ => PA.tZero
  end.

Definition binaryTruthSubstitution (n : nat) : PA.term :=
  match n with
  | 0 => PA.Term.numeral 1
  | 1 => PA.tVar 0
  | 2 => PA.tVar 1
  | _ => PA.tZero
  end.

Definition binaryGraphSubstitution (n : nat) : PA.term :=
  match n with
  | 0 => PA.tVar 0
  | 1 => PA.tVar 1
  | 2 => PA.tVar 2
  | _ => PA.tZero
  end.

Definition unaryTruthFormula (f : nat -> nat) : PA.formula :=
  PA.Formula.subst unaryTruthSubstitution (unaryGraphFormula f).

Definition binaryTruthFormula (f : nat -> nat -> nat) : PA.formula :=
  PA.Formula.subst binaryTruthSubstitution (binaryGraphFormula f).

Definition normalizedBinaryGraphFormula
    (f : nat -> nat -> nat) : PA.formula :=
  PA.Formula.subst binaryGraphSubstitution (binaryGraphFormula f).

Lemma unaryTruthSubstitution_env (e : nat -> nat) :
  (fun n => PA.Term.eval PA.natModel e (unaryTruthSubstitution n)) =
  graphEnv (unaryInputs (e 0)) 1.
Proof.
  apply functional_extensionality. intros [|[|n]].
  - reflexivity.
  - reflexivity.
  - unfold graphEnv, vectorEnv, unaryInputs, unaryTruthSubstitution.
    cbn. destruct (lt_dec (S (S n)) 2); [lia | reflexivity].
Qed.

Lemma binaryTruthSubstitution_env (e : nat -> nat) :
  (fun n => PA.Term.eval PA.natModel e (binaryTruthSubstitution n)) =
  graphEnv (binaryInputs (e 0) (e 1)) 1.
Proof.
  apply functional_extensionality. intros [|[|[|n]]].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold graphEnv, vectorEnv, binaryInputs, binaryTruthSubstitution.
    cbn. destruct (lt_dec (S (S (S n))) 3); [lia | reflexivity].
Qed.

Lemma binaryGraphSubstitution_env (e : nat -> nat) :
  (fun n => PA.Term.eval PA.natModel e (binaryGraphSubstitution n)) =
  graphEnv (binaryInputs (e 1) (e 2)) (e 0).
Proof.
  apply functional_extensionality. intros [|[|[|n]]].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold graphEnv, vectorEnv, binaryInputs, binaryGraphSubstitution.
    cbn. destruct (lt_dec (S (S (S n))) 3); [lia | reflexivity].
Qed.

Lemma unaryTruthFormula_correct
    (f : nat -> nat) (Hf : computable f) (e : nat -> nat) :
  PA.Formula.Sat PA.natModel e (unaryTruthFormula f) <-> 1 = f (e 0).
Proof.
  unfold unaryTruthFormula.
  rewrite PA.Formula.Sat_subst, unaryTruthSubstitution_env.
  rewrite (unaryGraphFormula_correct Hf (unaryInputs (e 0)) 1).
  reflexivity.
Qed.

Lemma binaryTruthFormula_correct
    (f : nat -> nat -> nat) (Hf : computable f) (e : nat -> nat) :
  PA.Formula.Sat PA.natModel e (binaryTruthFormula f) <->
  1 = f (e 0) (e 1).
Proof.
  unfold binaryTruthFormula.
  rewrite PA.Formula.Sat_subst, binaryTruthSubstitution_env.
  rewrite (binaryGraphFormula_correct Hf
    (binaryInputs (e 0) (e 1)) 1).
  reflexivity.
Qed.

Lemma normalizedBinaryGraphFormula_correct
    (f : nat -> nat -> nat) (Hf : computable f) (e : nat -> nat) :
  PA.Formula.Sat PA.natModel e (normalizedBinaryGraphFormula f) <->
  e 0 = f (e 1) (e 2).
Proof.
  unfold normalizedBinaryGraphFormula.
  rewrite PA.Formula.Sat_subst, binaryGraphSubstitution_env.
  rewrite (binaryGraphFormula_correct Hf
    (binaryInputs (e 1) (e 2)) (e 0)).
  reflexivity.
Qed.

(** * The five public PA formula values *)

Definition ValidOrdinalCodeFormula : PA.formula :=
  unaryTruthFormula validCodeFlag.

Definition OrdinalLTFormula : PA.formula :=
  binaryTruthFormula ordinalLTFlag.

(* Re-index a unary formula so its distinguished input is variable [k]. *)
Definition isolateVariableSubstitution (k n : nat) : PA.term :=
  match n with
  | 0 => PA.tVar k
  | _ => PA.tZero
  end.

Definition validCodeAt (k : nat) : PA.formula :=
  PA.Formula.subst (isolateVariableSubstitution k) ValidOrdinalCodeFormula.

Definition guardedBinaryGraphFormula
    (f : nat -> nat -> nat) : PA.formula :=
  PA.pAnd (validCodeAt 1)
    (PA.pAnd (validCodeAt 2) (normalizedBinaryGraphFormula f)).

Definition OrdinalAddFormula : PA.formula :=
  guardedBinaryGraphFormula addCode.

Definition OrdinalMulFormula : PA.formula :=
  guardedBinaryGraphFormula mulCode.

Definition OrdinalPowFormula : PA.formula :=
  guardedBinaryGraphFormula powCode.

(** * Standard-model specifications *)

Theorem ValidOrdinalCodeFormula_spec (e : nat -> nat) :
  PA.Formula.Sat PA.natModel e ValidOrdinalCodeFormula <->
  ValidOrdinalCode (e 0).
Proof.
  unfold ValidOrdinalCodeFormula.
  rewrite (unaryTruthFormula_correct term_validCodeFlag e).
  apply one_eq_validCodeFlag.
Qed.

Theorem OrdinalLTFormula_spec (e : nat -> nat) :
  PA.Formula.Sat PA.natModel e OrdinalLTFormula <->
  OrdinalLT (e 0) (e 1).
Proof.
  unfold OrdinalLTFormula.
  rewrite (binaryTruthFormula_correct term_ordinalLTFlag e).
  apply one_eq_ordinalLTFlag.
Qed.

Lemma validCodeAt_spec (e : nat -> nat) (k : nat) :
  PA.Formula.Sat PA.natModel e (validCodeAt k) <->
  ValidOrdinalCode (e k).
Proof.
  unfold validCodeAt.
  rewrite PA.Formula.Sat_subst, ValidOrdinalCodeFormula_spec.
  reflexivity.
Qed.

Lemma guardedBinaryGraphFormula_spec
    (f : nat -> nat -> nat) (Hf : computable f) (e : nat -> nat) :
  PA.Formula.Sat PA.natModel e (guardedBinaryGraphFormula f) <->
  ValidOrdinalCode (e 1) /\ ValidOrdinalCode (e 2) /\
  e 0 = f (e 1) (e 2).
Proof.
  unfold guardedBinaryGraphFormula.
  cbn [PA.Formula.Sat].
  rewrite !validCodeAt_spec, (normalizedBinaryGraphFormula_correct Hf e).
  reflexivity.
Qed.

Theorem OrdinalAddFormula_spec (e : nat -> nat) :
  PA.Formula.Sat PA.natModel e OrdinalAddFormula <->
  OrdinalAdd (e 0) (e 1) (e 2).
Proof.
  unfold OrdinalAddFormula, OrdinalAdd.
  apply (guardedBinaryGraphFormula_spec term_addCode e).
Qed.

Theorem OrdinalMulFormula_spec (e : nat -> nat) :
  PA.Formula.Sat PA.natModel e OrdinalMulFormula <->
  OrdinalMul (e 0) (e 1) (e 2).
Proof.
  unfold OrdinalMulFormula, OrdinalMul.
  apply (guardedBinaryGraphFormula_spec term_mulCode e).
Qed.

Theorem OrdinalPowFormula_spec (e : nat -> nat) :
  PA.Formula.Sat PA.natModel e OrdinalPowFormula <->
  OrdinalPow (e 0) (e 1) (e 2).
Proof.
  unfold OrdinalPowFormula, OrdinalPow.
  apply (guardedBinaryGraphFormula_spec term_powCode e).
Qed.

(** * Explicit environments *)

Definition predicateEnv (x : nat) : nat -> nat :=
  fun n => match n with 0 => x | _ => 0 end.

Definition binaryPredicateEnv (a b : nat) : nat -> nat :=
  fun n => match n with 0 => a | 1 => b | _ => 0 end.

Definition outputFirstBinaryEnv (z a b : nat) : nat -> nat :=
  fun n => match n with 0 => z | 1 => a | 2 => b | _ => 0 end.

Corollary ValidOrdinalCodeFormula_standard (code : nat) :
  PA.Formula.Sat PA.natModel (predicateEnv code)
    ValidOrdinalCodeFormula <-> ValidOrdinalCode code.
Proof. apply ValidOrdinalCodeFormula_spec. Qed.

Corollary OrdinalLTFormula_standard (a b : nat) :
  PA.Formula.Sat PA.natModel (binaryPredicateEnv a b)
    OrdinalLTFormula <-> OrdinalLT a b.
Proof. apply OrdinalLTFormula_spec. Qed.

Corollary OrdinalAddFormula_standard (z a b : nat) :
  PA.Formula.Sat PA.natModel (outputFirstBinaryEnv z a b)
    OrdinalAddFormula <-> OrdinalAdd z a b.
Proof. apply OrdinalAddFormula_spec. Qed.

Corollary OrdinalMulFormula_standard (z a b : nat) :
  PA.Formula.Sat PA.natModel (outputFirstBinaryEnv z a b)
    OrdinalMulFormula <-> OrdinalMul z a b.
Proof. apply OrdinalMulFormula_spec. Qed.

Corollary OrdinalPowFormula_standard (z a b : nat) :
  PA.Formula.Sat PA.natModel (outputFirstBinaryEnv z a b)
    OrdinalPowFormula <-> OrdinalPow z a b.
Proof. apply OrdinalPowFormula_spec. Qed.

(* The guards are semantically useful, not cosmetic: the closure laws from
   EpsilonZeroLaws.v now imply validity of every formula-produced result. *)
Corollary OrdinalAddFormula_result_valid (e : nat -> nat) :
  PA.Formula.Sat PA.natModel e OrdinalAddFormula ->
  ValidOrdinalCode (e 0).
Proof.
  intro H. apply (ordinalAdd_result_valid (e 0) (e 1) (e 2)).
  now apply (proj1 (OrdinalAddFormula_spec e)).
Qed.

Corollary OrdinalMulFormula_result_valid (e : nat -> nat) :
  PA.Formula.Sat PA.natModel e OrdinalMulFormula ->
  ValidOrdinalCode (e 0).
Proof.
  intro H. apply (ordinalMul_result_valid (e 0) (e 1) (e 2)).
  now apply (proj1 (OrdinalMulFormula_spec e)).
Qed.

Corollary OrdinalPowFormula_result_valid (e : nat -> nat) :
  PA.Formula.Sat PA.natModel e OrdinalPowFormula ->
  ValidOrdinalCode (e 0).
Proof.
  intro H. apply (ordinalPow_result_valid (e 0) (e 1) (e 2)).
  now apply (proj1 (OrdinalPowFormula_spec e)).
Qed.

End PAEpsilonZeroFormulas.
