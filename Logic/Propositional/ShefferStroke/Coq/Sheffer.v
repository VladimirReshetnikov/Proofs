(*
  Coq port of the Lean module ShefferStroke.Sheffer.

  This is the shared core vocabulary for one-binary-connective propositional
  proofs: NAND/NOR truth tables, formulas over an anonymous stroke, ordinary
  classical propositional formulas, and truth-preserving translations from the
  classical language into pure NAND and pure NOR formulas.
*)

From Stdlib Require Import Bool.Bool.

Set Implicit Arguments.

Module LeanProofs.
Module Sheffer.

Definition boolNand (p q : bool) : bool := negb (andb p q).

Definition boolNor (p q : bool) : bool := negb (orb p q).

Inductive StrokeFormula (A : Type) : Type :=
| strokeAtom : A -> StrokeFormula A
| stroke : StrokeFormula A -> StrokeFormula A -> StrokeFormula A.

Arguments strokeAtom {A} _.
Arguments stroke {A} _ _.

Fixpoint evalWith {A : Type} (op : bool -> bool -> bool) (v : A -> bool)
    (p : StrokeFormula A) : bool :=
  match p with
  | strokeAtom a => v a
  | stroke p q => op (evalWith op v p) (evalWith op v q)
  end.

Inductive ClassicalFormula (A : Type) : Type :=
| classicalAtom : A -> ClassicalFormula A
| classicalNeg : ClassicalFormula A -> ClassicalFormula A
| classicalAnd : ClassicalFormula A -> ClassicalFormula A -> ClassicalFormula A
| classicalOr : ClassicalFormula A -> ClassicalFormula A -> ClassicalFormula A
| classicalImp : ClassicalFormula A -> ClassicalFormula A -> ClassicalFormula A
| classicalIff : ClassicalFormula A -> ClassicalFormula A -> ClassicalFormula A.

Arguments classicalAtom {A} _.
Arguments classicalNeg {A} _.
Arguments classicalAnd {A} _ _.
Arguments classicalOr {A} _ _.
Arguments classicalImp {A} _ _.
Arguments classicalIff {A} _ _.

Fixpoint eval {A : Type} (v : A -> bool) (p : ClassicalFormula A) : bool :=
  match p with
  | classicalAtom a => v a
  | classicalNeg p => negb (eval v p)
  | classicalAnd p q => andb (eval v p) (eval v q)
  | classicalOr p q => orb (eval v p) (eval v q)
  | classicalImp p q => orb (negb (eval v p)) (eval v q)
  | classicalIff p q => Bool.eqb (eval v p) (eval v q)
  end.

Fixpoint toNand {A : Type} (p : ClassicalFormula A) : StrokeFormula A :=
  match p with
  | classicalAtom a => strokeAtom a
  | classicalNeg p =>
      let p' := toNand p in
      stroke p' p'
  | classicalAnd p q =>
      let pq := stroke (toNand p) (toNand q) in
      stroke pq pq
  | classicalOr p q =>
      stroke (stroke (toNand p) (toNand p)) (stroke (toNand q) (toNand q))
  | classicalImp p q =>
      stroke (toNand p) (stroke (toNand q) (toNand q))
  | classicalIff p q =>
      let p' := toNand p in
      let q' := toNand q in
      let both := stroke (stroke p' (stroke q' q')) (stroke q' (stroke p' p')) in
      stroke both both
  end.

Fixpoint toNor {A : Type} (p : ClassicalFormula A) : StrokeFormula A :=
  match p with
  | classicalAtom a => strokeAtom a
  | classicalNeg p =>
      let p' := toNor p in
      stroke p' p'
  | classicalAnd p q =>
      stroke (stroke (toNor p) (toNor p)) (stroke (toNor q) (toNor q))
  | classicalOr p q =>
      let pq := stroke (toNor p) (toNor q) in
      stroke pq pq
  | classicalImp p q =>
      let npq := stroke (stroke (toNor p) (toNor p)) (toNor q) in
      stroke npq npq
  | classicalIff p q =>
      let p' := toNor p in
      let q' := toNor q in
      let pq := stroke (stroke (stroke p' p') q') (stroke (stroke p' p') q') in
      let qp := stroke (stroke (stroke q' q') p') (stroke (stroke q' q') p') in
      stroke (stroke pq pq) (stroke qp qp)
  end.

Theorem eval_toNand {A : Type} (v : A -> bool) :
    forall p : ClassicalFormula A, evalWith boolNand v (toNand p) = eval v p.
Proof.
  induction p; simpl; try rewrite IHp; try rewrite IHp1; try rewrite IHp2;
    repeat match goal with |- context[eval v ?p] => destruct (eval v p) end;
    reflexivity.
Qed.

Theorem eval_toNor {A : Type} (v : A -> bool) :
    forall p : ClassicalFormula A, evalWith boolNor v (toNor p) = eval v p.
Proof.
  induction p; simpl; try rewrite IHp; try rewrite IHp1; try rewrite IHp2;
    repeat match goal with |- context[eval v ?p] => destruct (eval v p) end;
    reflexivity.
Qed.

End Sheffer.
End LeanProofs.
