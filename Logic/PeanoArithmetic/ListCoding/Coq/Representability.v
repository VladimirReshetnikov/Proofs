From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.

Module PAListRepresentability.

Import PA.

Definition env := nat -> nat.

(** A formula represents an environment predicate in the standard model of
    PA.  Keeping the witness in [Type] makes every public representation
    theorem expose an actual formula, rather than merely asserting that one
    exists. *)
Definition Represents (R : env -> Prop) : Type :=
  { phi : formula |
      forall e, Formula.Sat natModel e phi <-> R e }.

Definition representedFormula {R : env -> Prop}
    (h : Represents R) : formula := proj1_sig h.

Lemma representedFormula_spec : forall R (h : Represents R) e,
  Formula.Sat natModel e (representedFormula h) <-> R e.
Proof.
  intros R [phi hphi] e. exact (hphi e).
Qed.

Definition repEq (a b : term) :
    Represents (fun e => Term.eval natModel e a = Term.eval natModel e b).
Proof. exists (pEq a b). reflexivity. Defined.

Definition repBot : Represents (fun _ => False).
Proof. exists pBot. reflexivity. Defined.

Definition repImp (R S : env -> Prop)
    (hR : Represents R) (hS : Represents S) :
    Represents (fun e => R e -> S e).
Proof.
  destruct hR as [r hr], hS as [s hs].
  exists (pImp r s). intro e. simpl. rewrite hr, hs. reflexivity.
Defined.

Definition repAnd (R S : env -> Prop)
    (hR : Represents R) (hS : Represents S) :
    Represents (fun e => R e /\ S e).
Proof.
  destruct hR as [r hr], hS as [s hs].
  exists (pAnd r s). intro e. simpl. rewrite hr, hs. reflexivity.
Defined.

Definition repOr (R S : env -> Prop)
    (hR : Represents R) (hS : Represents S) :
    Represents (fun e => R e \/ S e).
Proof.
  destruct hR as [r hr], hS as [s hs].
  exists (pOr r s). intro e. simpl. rewrite hr, hs. reflexivity.
Defined.

Definition repAll (R : env -> Prop) (hR : Represents R) :
    Represents (fun e => forall x, R (scons nat x e)).
Proof.
  destruct hR as [r hr].
  exists (pAll r). intro e. simpl.
  split; intros h x.
  - apply (proj1 (hr _)). exact (h x).
  - apply (proj2 (hr _)). exact (h x).
Defined.

Definition repEx (R : env -> Prop) (hR : Represents R) :
    Represents (fun e => exists x, R (scons nat x e)).
Proof.
  destruct hR as [r hr].
  exists (pEx r). intro e. simpl.
  split; intros [x hx]; exists x.
  - apply (proj1 (hr _)). exact hx.
  - apply (proj2 (hr _)). exact hx.
Defined.

Definition repRename (R : env -> Prop) (hR : Represents R)
    (r : nat -> nat) :
    Represents (fun e => R (fun n => e (r n))).
Proof.
  destruct hR as [phi hphi].
  exists (Formula.rename r phi). intro e.
  rewrite Formula.Sat_rename. apply hphi.
Defined.

Definition repNot (R : env -> Prop) (hR : Represents R) :
    Represents (fun e => ~ R e) := repImp R (fun _ => False) hR repBot.

Definition repIff (R S : env -> Prop)
    (hR : Represents R) (hS : Represents S) :
    Represents (fun e => (R e <-> S e)).
Proof.
  exact (repAnd
    (fun e => R e -> S e) (fun e => S e -> R e)
    (repImp R S hR hS) (repImp S R hS hR)).
Defined.

Definition liftTerm (n : nat) (t : term) : term :=
  Term.rename (fun i => i + n) t.

Lemma eval_liftTerm : forall n slots e t,
  Term.eval natModel
      (fun i => if i <? n then slots i else e (i - n))
      (liftTerm n t) =
  Term.eval natModel e t.
Proof.
  intros n slots e t. unfold liftTerm.
  rewrite Term.eval_rename. apply Term.eval_ext. intro i.
  change ((if i + n <? n then slots (i + n) else e (i + n - n)) = e i).
  destruct (i + n <? n) eqn:h.
  - apply Nat.ltb_lt in h. lia.
  - replace (i + n - n) with i by lia. reflexivity.
Qed.

Definition pNot (a : formula) : formula := pImp a pBot.

Definition pIff (a b : formula) : formula :=
  pAnd (pImp a b) (pImp b a).

End PAListRepresentability.
