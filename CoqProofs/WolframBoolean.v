(*
  Coq port of LeanProofs/WolframBoolean.lean.

  The generated equational certificates live in
  WolframBooleanCertificates.v and WolframBooleanHuntingtonCertificates.v.
  This file exposes their algebraic consequences and the two-valued Boolean
  functional-completeness layer in ordinary Coq definitions.
*)

From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From LeanProofsCoq Require Import
  EquationalLogic
  WolframBooleanCertificates
  WolframBooleanHuntingtonCertificates.

Import ListNotations.
Set Implicit Arguments.
Import LeanProofs.EquationalLogic.

Module LeanProofs.
Module WolframBoolean.

Module WBC :=
  LeanProofsCoq.WolframBooleanCertificates.LeanProofs.WolframBooleanCertificates.
Module WBH :=
  LeanProofsCoq.WolframBooleanHuntingtonCertificates.LeanProofs.WolframBooleanHuntingtonCertificates.

Definition boolNand (p q : bool) : bool :=
  negb (p && q).

Definition boolNor (p q : bool) : bool :=
  negb (p || q).

Definition WolframAxiom {A : Type} (op : A -> A -> A) : Prop :=
  forall a b c, op (op (op a b) c) (op a (op (op a c) a)) = c.

Definition MeredithAxioms {A : Type} (op : A -> A -> A) : Prop :=
  (forall p q r, op p (op q (op p r)) = op (op (op r q) q) p) /\
  (forall p q, op (op p p) (op q p) = p).

Definition ShefferAxioms {A : Type} (op : A -> A -> A) : Prop :=
  (forall a, op (op a a) (op a a) = a) /\
  (forall a b, op a (op b (op b b)) = op a a) /\
  (forall a b c,
    op (op a (op b c)) (op a (op b c)) =
      op (op (op b b) a) (op (op c c) a)).

Definition strokeCompl {A : Type} (op : A -> A -> A) (a : A) : A :=
  op a a.

Definition strokeJoin {A : Type} (op : A -> A -> A) (a b : A) : A :=
  op (strokeCompl op a) (strokeCompl op b).

Definition HuntingtonAxioms {A : Type}
    (sup : A -> A -> A) (compl : A -> A) : Prop :=
  (forall a b, sup a b = sup b a) /\
  (forall a b c, sup a (sup b c) = sup (sup a b) c) /\
  (forall a b,
    sup (compl (sup (compl a) b))
      (compl (sup (compl a) (compl b))) = a).

Definition SameBoolOp (op op' : bool -> bool -> bool) : Prop :=
  forall a b, op a b = op' a b.

Definition IsBooleanSheffer (op : bool -> bool -> bool) : Prop :=
  SameBoolOp op boolNand \/ SameBoolOp op boolNor.

Theorem wolfram_derives_sheffer_axioms {A : Type} (op : A -> A -> A)
    (h : WolframAxiom op) : ShefferAxioms op.
Proof.
  assert (hW : Equation.Valid op WBC.wolframEquation).
  { intro env. exact (h (env 0) (env 1) (env 2)). }
  destruct (@WBC.wolframToSheffer_valid A op hW) as [h1 [h2 h3]].
  split.
  - intro a. exact (h1 (fun _ => a)).
  - split.
    + intros a b.
      exact (h2 (fun n => match n with 0 => a | 1 => b | _ => a end)).
    + intros a b c.
      exact (h3 (fun n => match n with 0 => a | 1 => b | 2 => c | _ => a end)).
Qed.

Theorem meredith_derives_wolfram_axiom {A : Type} (op : A -> A -> A)
    (h : MeredithAxioms op) : WolframAxiom op.
Proof.
  assert (hM1 : Equation.Valid op WBC.meredithEquation1).
  { intro env. exact (proj1 h (env 0) (env 1) (env 2)). }
  assert (hM2 : Equation.Valid op WBC.meredithEquation2).
  { intro env. exact (proj2 h (env 0) (env 1)). }
  pose proof (@WBC.meredithToWolfram_valid A op hM1 hM2) as hW.
  intros a b c.
  exact (hW (fun n => match n with 0 => a | 1 => b | 2 => c | _ => a end)).
Qed.

Theorem meredith_derives_sheffer_axioms {A : Type} (op : A -> A -> A)
    (h : MeredithAxioms op) : ShefferAxioms op.
Proof.
  exact (@wolfram_derives_sheffer_axioms A op
    (@meredith_derives_wolfram_axiom A op h)).
Qed.

Theorem sheffer_derives_huntington_axioms {A : Type} (op : A -> A -> A)
    (h : ShefferAxioms op) : HuntingtonAxioms (strokeJoin op) (strokeCompl op).
Proof.
  destruct h as [hS1 [hS2 hS3]].
  assert (h1 : Equation.Valid op WBC.shefferEquation1).
  { intro env. exact (hS1 (env 0)). }
  assert (h2 : Equation.Valid op WBC.shefferEquation2).
  { intro env. exact (hS2 (env 0) (env 1)). }
  assert (h3 : Equation.Valid op WBC.shefferEquation3).
  { intro env. exact (hS3 (env 0) (env 1) (env 2)). }
  destruct (@WBH.shefferToHuntington_valid A op h1 h2 h3)
    as [hComm [hAssoc hHunt]].
  unfold HuntingtonAxioms, strokeJoin, strokeCompl.
  split.
  - intros a b.
    exact (hComm (fun n => match n with 0 => a | 1 => b | _ => a end)).
  - split.
    + intros a b c.
      exact (hAssoc (fun n => match n with 0 => a | 1 => b | 2 => c | _ => a end)).
    + intros a b.
      exact (hHunt (fun n => match n with 0 => a | 1 => b | _ => a end)).
Qed.

Theorem wolfram_derives_huntington_axioms {A : Type} (op : A -> A -> A)
    (h : WolframAxiom op) : HuntingtonAxioms (strokeJoin op) (strokeCompl op).
Proof.
  exact (@sheffer_derives_huntington_axioms A op
    (@wolfram_derives_sheffer_axioms A op h)).
Qed.

Theorem meredith_derives_huntington_axioms {A : Type} (op : A -> A -> A)
    (h : MeredithAxioms op) : HuntingtonAxioms (strokeJoin op) (strokeCompl op).
Proof.
  exact (@sheffer_derives_huntington_axioms A op
    (@meredith_derives_sheffer_axioms A op h)).
Qed.

Theorem boolNand_wolfram : WolframAxiom boolNand.
Proof.
  intros [] [] []; reflexivity.
Qed.

Theorem boolNor_wolfram : WolframAxiom boolNor.
Proof.
  intros [] [] []; reflexivity.
Qed.

Theorem boolNand_sheffer : ShefferAxioms boolNand.
Proof.
  exact (@wolfram_derives_sheffer_axioms bool boolNand boolNand_wolfram).
Qed.

Theorem boolNor_sheffer : ShefferAxioms boolNor.
Proof.
  exact (@wolfram_derives_sheffer_axioms bool boolNor boolNor_wolfram).
Qed.

Theorem boolNand_meredith : MeredithAxioms boolNand.
Proof.
  split.
  - intros [] [] []; reflexivity.
  - intros [] []; reflexivity.
Qed.

Theorem boolNor_meredith : MeredithAxioms boolNor.
Proof.
  split.
  - intros [] [] []; reflexivity.
  - intros [] []; reflexivity.
Qed.

Ltac prove_same_bool_op :=
  intros [] [];
  unfold boolNand, boolNor;
  cbn;
  repeat match goal with
  | H : ?op false false = _ |- context[?op false false] => rewrite H
  | H : ?op false true = _ |- context[?op false true] => rewrite H
  | H : ?op true false = _ |- context[?op true false] => rewrite H
  | H : ?op true true = _ |- context[?op true true] => rewrite H
  end;
  reflexivity.

Definition wolframHoldsBool (op : bool -> bool -> bool) : bool :=
  let row a b c :=
    Bool.eqb (op (op (op a b) c) (op a (op (op a c) a))) c in
  row false false false &&
  row false false true &&
  row false true false &&
  row false true true &&
  row true false false &&
  row true false true &&
  row true true false &&
  row true true true.

Lemma wolframAxiom_to_bool (op : bool -> bool -> bool)
    (h : WolframAxiom op) : wolframHoldsBool op = true.
Proof.
  unfold wolframHoldsBool.
  repeat rewrite h.
  repeat rewrite Bool.eqb_reflx.
  reflexivity.
Qed.

Ltac finish_bool_table_contradiction H :=
  cbn in H;
  repeat match type of H with
  | context[?op false false] =>
      match goal with Hff : ?op false false = _ |- _ => rewrite Hff in H end
  | context[?op false true] =>
      match goal with Hft : ?op false true = _ |- _ => rewrite Hft in H end
  | context[?op true false] =>
      match goal with Htf : ?op true false = _ |- _ => rewrite Htf in H end
  | context[?op true true] =>
      match goal with Htt : ?op true true = _ |- _ => rewrite Htt in H end
  end;
  discriminate.

Ltac use_wolfram_row h a b c :=
  let H := fresh "Hw" in
  pose proof (h a b c) as H;
  finish_bool_table_contradiction H.

Ltac contradict_wolfram_table h :=
  first [
    use_wolfram_row h false false false
  | use_wolfram_row h false false true
  | use_wolfram_row h false true false
  | use_wolfram_row h false true true
  | use_wolfram_row h true false false
  | use_wolfram_row h true false true
  | use_wolfram_row h true true false
  | use_wolfram_row h true true true
  ].

Theorem wolfram_characterizes_sheffer_on_bool
    (op : bool -> bool -> bool) (h : WolframAxiom op) : IsBooleanSheffer op.
Proof.
  pose proof (@wolframAxiom_to_bool op h) as htable.
  destruct (op false false) eqn:Hff;
  destruct (op false true) eqn:Hft;
  destruct (op true false) eqn:Htf;
  destruct (op true true) eqn:Htt;
  unfold wolframHoldsBool in htable;
  cbn in htable;
  repeat match type of htable with
  | context[op false false] => rewrite Hff in htable
  | context[op false true] => rewrite Hft in htable
  | context[op true false] => rewrite Htf in htable
  | context[op true true] => rewrite Htt in htable
  end;
  cbn in htable;
  try (left; prove_same_bool_op);
  try (right; prove_same_bool_op);
  discriminate.
Qed.

Definition meredithHoldsBool (op : bool -> bool -> bool) : bool :=
  let row1 p q r :=
    Bool.eqb (op p (op q (op p r))) (op (op (op r q) q) p) in
  let row2 p q :=
    Bool.eqb (op (op p p) (op q p)) p in
  row1 false false false &&
  row1 false false true &&
  row1 false true false &&
  row1 false true true &&
  row1 true false false &&
  row1 true false true &&
  row1 true true false &&
  row1 true true true &&
  row2 false false &&
  row2 false true &&
  row2 true false &&
  row2 true true.

Lemma meredithAxioms_to_bool (op : bool -> bool -> bool)
    (h : MeredithAxioms op) : meredithHoldsBool op = true.
Proof.
  destruct h as [h1 h2].
  unfold meredithHoldsBool.
  repeat rewrite h1.
  repeat rewrite h2.
  repeat rewrite Bool.eqb_reflx.
  reflexivity.
Qed.

Ltac use_meredith3 h a b c :=
  let H := fresh "Hm" in
  pose proof (h a b c) as H;
  finish_bool_table_contradiction H.

Ltac use_meredith2 h a b :=
  let H := fresh "Hm" in
  pose proof (h a b) as H;
  finish_bool_table_contradiction H.

Ltac contradict_meredith_table h :=
  destruct h as [h1 h2];
  first [
    use_meredith3 h1 false false false
  | use_meredith3 h1 false false true
  | use_meredith3 h1 false true false
  | use_meredith3 h1 false true true
  | use_meredith3 h1 true false false
  | use_meredith3 h1 true false true
  | use_meredith3 h1 true true false
  | use_meredith3 h1 true true true
  | use_meredith2 h2 false false
  | use_meredith2 h2 false true
  | use_meredith2 h2 true false
  | use_meredith2 h2 true true
  ].

Theorem meredith_characterizes_sheffer_on_bool
    (op : bool -> bool -> bool) (h : MeredithAxioms op) : IsBooleanSheffer op.
Proof.
  pose proof (@meredithAxioms_to_bool op h) as htable.
  destruct (op false false) eqn:Hff;
  destruct (op false true) eqn:Hft;
  destruct (op true false) eqn:Htf;
  destruct (op true true) eqn:Htt;
  unfold meredithHoldsBool in htable;
  cbn in htable;
  repeat match type of htable with
  | context[op false false] => rewrite Hff in htable
  | context[op false true] => rewrite Hft in htable
  | context[op true false] => rewrite Htf in htable
  | context[op true true] => rewrite Htt in htable
  end;
  cbn in htable;
  try (left; prove_same_bool_op);
  try (right; prove_same_bool_op);
  discriminate.
Qed.

Inductive StrokeFormula (A : Type) : Type :=
| SAtom : A -> StrokeFormula A
| Stroke : StrokeFormula A -> StrokeFormula A -> StrokeFormula A.

Arguments SAtom {A} _.
Arguments Stroke {A} _ _.

Fixpoint strokeEvalWith {A : Type} (op : bool -> bool -> bool)
    (v : A -> bool) (p : StrokeFormula A) : bool :=
  match p with
  | SAtom a => v a
  | Stroke p q => op (strokeEvalWith op v p) (strokeEvalWith op v q)
  end.

Inductive ClassicalFormula (A : Type) : Type :=
| CAtom : A -> ClassicalFormula A
| CNeg : ClassicalFormula A -> ClassicalFormula A
| CAnd : ClassicalFormula A -> ClassicalFormula A -> ClassicalFormula A
| COr : ClassicalFormula A -> ClassicalFormula A -> ClassicalFormula A
| CImp : ClassicalFormula A -> ClassicalFormula A -> ClassicalFormula A
| CIff : ClassicalFormula A -> ClassicalFormula A -> ClassicalFormula A.

Arguments CAtom {A} _.
Arguments CNeg {A} _.
Arguments CAnd {A} _ _.
Arguments COr {A} _ _.
Arguments CImp {A} _ _.
Arguments CIff {A} _ _.

Fixpoint classicalEval {A : Type} (v : A -> bool)
    (p : ClassicalFormula A) : bool :=
  match p with
  | CAtom a => v a
  | CNeg p => negb (classicalEval v p)
  | CAnd p q => classicalEval v p && classicalEval v q
  | COr p q => classicalEval v p || classicalEval v q
  | CImp p q => negb (classicalEval v p) || classicalEval v q
  | CIff p q => Bool.eqb (classicalEval v p) (classicalEval v q)
  end.

Fixpoint toNand {A : Type} (p : ClassicalFormula A) : StrokeFormula A :=
  match p with
  | CAtom a => SAtom a
  | CNeg p =>
      let p' := toNand p in Stroke p' p'
  | CAnd p q =>
      let p' := toNand p in
      let q' := toNand q in
      let pq := Stroke p' q' in Stroke pq pq
  | COr p q =>
      let p' := toNand p in
      let q' := toNand q in
      Stroke (Stroke p' p') (Stroke q' q')
  | CImp p q =>
      let p' := toNand p in
      let q' := toNand q in
      Stroke p' (Stroke q' q')
  | CIff p q =>
      let p' := toNand p in
      let q' := toNand q in
      let pq := Stroke p' (Stroke q' q') in
      let qp := Stroke q' (Stroke p' p') in
      let both := Stroke pq qp in
      Stroke both both
  end.

Fixpoint toNor {A : Type} (p : ClassicalFormula A) : StrokeFormula A :=
  match p with
  | CAtom a => SAtom a
  | CNeg p =>
      let p' := toNor p in Stroke p' p'
  | CAnd p q =>
      let p' := toNor p in
      let q' := toNor q in
      Stroke (Stroke p' p') (Stroke q' q')
  | COr p q =>
      let p' := toNor p in
      let q' := toNor q in
      let pq := Stroke p' q' in Stroke pq pq
  | CImp p q =>
      let p' := toNor p in
      let q' := toNor q in
      let np := Stroke p' p' in
      let npq := Stroke np q' in
      Stroke npq npq
  | CIff p q =>
      let p' := toNor p in
      let q' := toNor q in
      let np := Stroke p' p' in
      let nq := Stroke q' q' in
      let pq := Stroke (Stroke np q') (Stroke np q') in
      let qp := Stroke (Stroke nq p') (Stroke nq p') in
      Stroke (Stroke pq pq) (Stroke qp qp)
  end.

Theorem eval_toNand {A : Type} (v : A -> bool) :
    forall p : ClassicalFormula A,
      strokeEvalWith boolNand v (toNand p) = classicalEval v p.
Proof.
  induction p; simpl; try rewrite IHp; try rewrite IHp1; try rewrite IHp2;
    repeat match goal with
    | |- context[classicalEval v ?p] => destruct (classicalEval v p)
    end; reflexivity.
Qed.

Theorem eval_toNor {A : Type} (v : A -> bool) :
    forall p : ClassicalFormula A,
      strokeEvalWith boolNor v (toNor p) = classicalEval v p.
Proof.
  induction p; simpl; try rewrite IHp; try rewrite IHp1; try rewrite IHp2;
    repeat match goal with
    | |- context[classicalEval v ?p] => destruct (classicalEval v p)
    end; reflexivity.
Qed.

Lemma strokeEvalWith_same {A : Type} (op op' : bool -> bool -> bool)
    (hsame : SameBoolOp op op') (v : A -> bool) :
    forall p : StrokeFormula A,
      strokeEvalWith op v p = strokeEvalWith op' v p.
Proof.
  induction p; simpl.
  - reflexivity.
  - rewrite IHp1, IHp2. apply hsame.
Qed.

Theorem wolfram_functionally_complete {A : Type}
    (op : bool -> bool -> bool) (h : WolframAxiom op)
    (p : ClassicalFormula A) :
    exists q : StrokeFormula A,
      forall v : A -> bool, strokeEvalWith op v q = classicalEval v p.
Proof.
  destruct (@wolfram_characterizes_sheffer_on_bool op h) as [hop | hop].
  - exists (toNand p). intro v.
    rewrite (strokeEvalWith_same hop v (toNand p)).
    apply eval_toNand.
  - exists (toNor p). intro v.
    rewrite (strokeEvalWith_same hop v (toNor p)).
    apply eval_toNor.
Qed.

Theorem meredith_functionally_complete {A : Type}
    (op : bool -> bool -> bool) (h : MeredithAxioms op)
    (p : ClassicalFormula A) :
    exists q : StrokeFormula A,
      forall v : A -> bool, strokeEvalWith op v q = classicalEval v p.
Proof.
  destruct (@meredith_characterizes_sheffer_on_bool op h) as [hop | hop].
  - exists (toNand p). intro v.
    rewrite (strokeEvalWith_same hop v (toNand p)).
    apply eval_toNand.
  - exists (toNor p). intro v.
    rewrite (strokeEvalWith_same hop v (toNor p)).
    apply eval_toNor.
Qed.

End WolframBoolean.
End LeanProofs.
