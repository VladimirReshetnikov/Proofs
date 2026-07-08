(*
  Coq port of LeanProofs/WolframBoolean.lean.

  The generated equational certificates live in
  WolframBooleanCertificates.v and WolframBooleanHuntingtonCertificates.v.
  This file exposes their algebraic consequences and the two-valued Boolean
  functional-completeness layer in ordinary Coq definitions.
*)

From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.PeanoNat.
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

Record BinOp : Type := {
  ff : bool;
  ft : bool;
  tf : bool;
  tt : bool
}.

Definition binOpApply (op : BinOp) : bool -> bool -> bool :=
  fun p q =>
    match p, q with
    | false, false => ff op
    | false, true => ft op
    | true, false => tf op
    | true, true => tt op
    end.

Definition binOpEqb (x y : BinOp) : bool :=
  Bool.eqb (ff x) (ff y) &&
  Bool.eqb (ft x) (ft y) &&
  Bool.eqb (tf x) (tf y) &&
  Bool.eqb (tt x) (tt y).

Definition nandTable : BinOp :=
  {| ff := true; ft := true; tf := true; tt := false |}.

Definition norTable : BinOp :=
  {| ff := true; ft := false; tf := false; tt := false |}.

Definition bools : list bool := [false; true].

Definition allBinOps : list BinOp :=
  flat_map (fun ff =>
  flat_map (fun ft =>
  flat_map (fun tf =>
  map (fun tt => {| ff := ff; ft := ft; tf := tf; tt := tt |}) bools)
    bools) bools) bools.

Inductive SearchTerm : Type :=
| TVar : nat -> SearchTerm
| TApp : SearchTerm -> SearchTerm -> SearchTerm.

Fixpoint searchTermEqb (x y : SearchTerm) : bool :=
  match x, y with
  | TVar i, TVar j => Nat.eqb i j
  | TApp xl xr, TApp yl yr => searchTermEqb xl yl && searchTermEqb xr yr
  | _, _ => false
  end.

Definition pairTermEqb (x y : SearchTerm * SearchTerm) : bool :=
  searchTermEqb (fst x) (fst y) && searchTermEqb (snd x) (snd y).

Fixpoint listEqb {A : Type} (eqb : A -> A -> bool)
    (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => eqb x y && listEqb eqb xs' ys'
  | _, _ => false
  end.

Fixpoint nodeCount (t : SearchTerm) : nat :=
  match t with
  | TVar _ => 0
  | TApp l r => nodeCount l + nodeCount r + 1
  end.

Fixpoint varBound (t : SearchTerm) : nat :=
  match t with
  | TVar i => S i
  | TApp l r => Nat.max (varBound l) (varBound r)
  end.

Fixpoint evalSearchTerm (op : BinOp) (env : list bool)
    (t : SearchTerm) : bool :=
  match t with
  | TVar i => nth i env false
  | TApp l r => binOpApply op (evalSearchTerm op env l) (evalSearchTerm op env r)
  end.

Fixpoint allEnvs (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => flat_map (fun env => [false :: env; true :: env]) (allEnvs n')
  end.

Fixpoint canonicalTermsAux (fuel nodes next : nat)
    {struct fuel} : list (SearchTerm * nat) :=
  match nodes with
  | 0 =>
      map (fun i => (TVar i, if Nat.eqb i next then S next else next))
        (seq 0 (S next))
  | S nodes' =>
      match fuel with
      | 0 => []
      | S fuel' =>
          flat_map (fun leftNodes =>
            let rightNodes := nodes' - leftNodes in
            flat_map (fun left =>
              map (fun right => (TApp (fst left) (fst right), snd right))
                (canonicalTermsAux fuel' rightNodes (snd left)))
              (canonicalTermsAux fuel' leftNodes next))
            (seq 0 (S nodes'))
      end
  end.

Definition equationsUpTo (maxNodes : nat) : list (SearchTerm * SearchTerm) :=
  flat_map (fun leftNodes =>
    flat_map (fun rightNodes =>
      flat_map (fun lhs =>
        map (fun rhs => (fst lhs, fst rhs))
          (canonicalTermsAux rightNodes rightNodes (snd lhs)))
        (canonicalTermsAux leftNodes leftNodes 0))
      (seq 0 (S (maxNodes - leftNodes))))
    (seq 0 (S maxNodes)).

Definition equationHolds (op : BinOp) (lhs rhs : SearchTerm) : bool :=
  forallb (fun env =>
    Bool.eqb (evalSearchTerm op env lhs) (evalSearchTerm op env rhs))
    (allEnvs 7).

Definition equationModels (lhs rhs : SearchTerm) : list BinOp :=
  filter (fun op => equationHolds op lhs rhs) allBinOps.

Definition validInBooleanShefferTables (lhs rhs : SearchTerm) : bool :=
  equationHolds nandTable lhs rhs && equationHolds norTable lhs rhs.

Definition hasExactlyModels (models : list BinOp) (lhs rhs : SearchTerm) : bool :=
  listEqb binOpEqb (equationModels lhs rhs) models.

Definition characterizesShefferTables (lhs rhs : SearchTerm) : bool :=
  hasExactlyModels [norTable; nandTable] lhs rhs.

Definition wolframLhs : SearchTerm :=
  let a := TVar 0 in
  let b := TVar 1 in
  let c := TVar 2 in
  TApp
    (TApp (TApp a b) c)
    (TApp a (TApp (TApp a c) a)).

Definition wolframRhs : SearchTerm := TVar 2.

Theorem wolfram_operator_count :
    nodeCount wolframLhs + nodeCount wolframRhs = 6.
Proof. vm_compute. reflexivity. Qed.

Theorem wolfram_equation_characterizes_sheffer_tables :
    characterizesShefferTables wolframLhs wolframRhs = true.
Proof. vm_compute. reflexivity. Qed.

Record FiniteOp : Type := {
  fsize : nat;
  ftable : list nat
}.

Definition finiteApply (op : FiniteOp) (x y : nat) : nat :=
  match fsize op with
  | 0 => 0
  | size => (nth (x * size + y) (ftable op) 0) mod size
  end.

Fixpoint allFiniteEnvs (size n : nat) : list (list nat) :=
  match n with
  | 0 => [[]]
  | S n' =>
      flat_map (fun env => map (fun x => x :: env) (seq 0 size))
        (allFiniteEnvs size n')
  end.

Fixpoint evalFiniteSearchTerm (op : FiniteOp) (env : list nat)
    (t : SearchTerm) : nat :=
  match t with
  | TVar i => nth i env 0
  | TApp l r => finiteApply op (evalFiniteSearchTerm op env l)
    (evalFiniteSearchTerm op env r)
  end.

Definition finiteEquationHolds (op : FiniteOp)
    (lhs rhs : SearchTerm) : bool :=
  forallb (fun env =>
    Nat.eqb (evalFiniteSearchTerm op env lhs) (evalFiniteSearchTerm op env rhs))
    (allFiniteEnvs (fsize op) (Nat.max (varBound lhs) (varBound rhs))).

Definition finiteWolframHolds (op : FiniteOp) : bool :=
  forallb (fun env =>
    let a := nth 0 env 0 in
    let b := nth 1 env 0 in
    let c := nth 2 env 0 in
    let lhs := finiteApply op (finiteApply op (finiteApply op a b) c)
      (finiteApply op a (finiteApply op (finiteApply op a c) a)) in
    Nat.eqb lhs c)
    (allFiniteEnvs (fsize op) 3).

Definition shortCountermodelPool : list FiniteOp := [
  {| fsize := 2; ftable := [0; 0; 0; 0] |};
  {| fsize := 2; ftable := [0; 0; 0; 1] |};
  {| fsize := 2; ftable := [0; 0; 1; 1] |};
  {| fsize := 2; ftable := [0; 1; 0; 1] |};
  {| fsize := 2; ftable := [0; 1; 1; 0] |};
  {| fsize := 3; ftable := [0; 2; 1; 2; 2; 0; 1; 0; 1] |};
  {| fsize := 4; ftable := [0; 3; 3; 0; 2; 1; 1; 2; 0; 3; 3; 0; 2; 1; 1; 2] |};
  {| fsize := 4; ftable := [0; 2; 0; 2; 0; 2; 0; 2; 1; 3; 1; 3; 1; 3; 1; 3] |};
  {| fsize := 2; ftable := [0; 0; 1; 0] |};
  {| fsize := 4; ftable := [0; 3; 3; 0; 0; 3; 3; 0; 1; 2; 2; 1; 1; 2; 2; 1] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 2; 1; 0; 0; 1] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 0; 2; 0; 0; 2] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 0; 2; 2; 0; 2] |};
  {| fsize := 4; ftable := [1; 2; 2; 1; 3; 0; 0; 3; 1; 2; 2; 1; 3; 0; 0; 3] |};
  {| fsize := 3; ftable := [0; 1; 2; 2; 0; 1; 1; 2; 0] |};
  {| fsize := 3; ftable := [0; 0; 1; 0; 2; 1; 1; 1; 1] |};
  {| fsize := 4; ftable := [0; 2; 0; 2; 3; 1; 3; 1; 3; 1; 3; 1; 0; 2; 0; 2] |};
  {| fsize := 4; ftable := [1; 3; 1; 3; 2; 0; 2; 0; 2; 0; 2; 0; 1; 3; 1; 3] |};
  {| fsize := 3; ftable := [0; 2; 1; 1; 0; 2; 2; 1; 0] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 2; 2; 0; 0; 1] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 2; 0; 1; 0; 1] |};
  {| fsize := 4; ftable := [0; 0; 1; 1; 3; 3; 2; 2; 3; 3; 2; 2; 0; 0; 1; 1] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 1; 1; 2; 0; 2] |};
  {| fsize := 4; ftable := [3; 1; 3; 1; 3; 1; 3; 1; 2; 0; 2; 0; 2; 0; 2; 0] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 1; 1; 0; 0; 0] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 2; 2; 0; 0; 2] |};
  {| fsize := 4; ftable := [2; 1; 1; 2; 2; 1; 1; 2; 3; 0; 0; 3; 3; 0; 0; 3] |};
  {| fsize := 4; ftable := [3; 3; 2; 2; 1; 1; 0; 0; 3; 3; 2; 2; 1; 1; 0; 0] |};
  {| fsize := 4; ftable := [0; 0; 1; 1; 2; 2; 3; 3; 0; 0; 1; 1; 2; 2; 3; 3] |};
  {| fsize := 4; ftable := [2; 2; 3; 3; 1; 1; 0; 0; 1; 1; 0; 0; 2; 2; 3; 3] |}
].

Definition hasFiniteNonWolframCountermodel (lhs rhs : SearchTerm) : bool :=
  existsb (fun op =>
    finiteEquationHolds op lhs rhs && negb (finiteWolframHolds op))
    shortCountermodelPool.

Definition shortEquationCountermodelCheck : bool :=
  forallb (fun e =>
    negb (validInBooleanShefferTables (fst e) (snd e)) ||
      hasFiniteNonWolframCountermodel (fst e) (snd e))
    (equationsUpTo 5).

End WolframBoolean.
End LeanProofs.
