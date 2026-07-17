(* ===================================================================== *)
(*  DiophantineFormula.v                                                 *)
(*                                                                       *)
(*  A semantic bridge from the single-equation Diophantine predicates    *)
(*  used by the Coq Library of Undecidability Proofs to the concrete PA   *)
(*  formula syntax in PAHF.v.                                            *)
(*                                                                       *)
(*  This file deliberately separates two issues.  [diophantineFormula]   *)
(*  is a Type-valued construction from explicit polynomial data.  An     *)
(*  arbitrary proof of [Diophantine R], however, only existentially       *)
(*  packages that data in Prop, so Coq does not permit eliminating it to  *)
(*  define a formula.  The public bridges therefore conclude             *)
(*  [exists phi : PA.formula, ...] in Prop.                               *)
(* ===================================================================== *)

From Stdlib Require Import Arith Lia List Vector.
From Stdlib Require Import Logic.FunctionalExtensionality.

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.

From Undecidability.H10 Require Import H10.
From Undecidability.H10.Util Require Import Diophantine.

Import ListNotations.
Import PA.
Import dio_logic dio_single.

Set Implicit Arguments.

(* Translate an H10 polynomial to a PA term, given interpretations of its
   existential variables and parameters as PA terms. *)
Fixpoint polyTerm {V P : Set}
    (varTerm : V -> PA.term) (parTerm : P -> PA.term)
    (p : dio_polynomial V P) : PA.term :=
  match p with
  | dp_nat n => Term.numeral n
  | dp_var x => varTerm x
  | dp_par x => parTerm x
  | dp_comp do_add p q => tAdd (polyTerm varTerm parTerm p)
                                (polyTerm varTerm parTerm q)
  | dp_comp do_mul p q => tMul (polyTerm varTerm parTerm p)
                                (polyTerm varTerm parTerm q)
  end.

Lemma eval_polyTerm {V P : Set}
    (varTerm : V -> PA.term) (parTerm : P -> PA.term)
    (p : dio_polynomial V P) (e : nat -> nat) :
  Term.eval natModel e (polyTerm varTerm parTerm p) =
  dp_eval (fun x => Term.eval natModel e (varTerm x))
          (fun x => Term.eval natModel e (parTerm x)) p.
Proof.
  induction p as [n | x | x | [] p IHp q IHq]; cbn.
  - apply Term.eval_numeral_natModel.
  - reflexivity.
  - reflexivity.
  - now rewrite IHp, IHq.
  - now rewrite IHp, IHq.
Qed.

Definition finIndex {n} (i : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat i).

Lemma finIndex_lt {n} (i : Fin.t n) : finIndex i < n.
Proof. exact (proj2_sig (Fin.to_nat i)). Qed.

Lemma finIndex_FS {n} (i : Fin.t n) :
  finIndex (Fin.FS i) = S (finIndex i).
Proof.
  unfold finIndex; cbn.
  destruct (Fin.to_nat i); reflexivity.
Qed.

(* An environment determined by a parameter vector.  Values outside the
   vector are irrelevant to the formulas below and are set to zero. *)
Definition vectorEnv {n} (v : Vector.t nat n) (i : nat) : nat :=
  match lt_dec i n with
  | left hi => Vector.nth v (Fin.of_nat_lt hi)
  | right _ => 0
  end.

Lemma vectorEnv_finIndex {n} (v : Vector.t nat n) (i : Fin.t n) :
  vectorEnv v (finIndex i) = Vector.nth v i.
Proof.
  unfold vectorEnv.
  destruct (lt_dec (finIndex i) n) as [hi | hi].
  - f_equal.
    apply Fin.to_nat_inj.
    rewrite Fin.to_nat_of_nat.
    reflexivity.
  - exfalso. apply hi. apply finIndex_lt.
Qed.

Fixpoint existsN (n : nat) (phi : PA.formula) : PA.formula :=
  match n with
  | 0 => phi
  | S n => pEx (existsN n phi)
  end.

(* [pushListEnv xs e] is the environment at the body after choosing the
   existential witnesses in [xs], from the outermost quantifier inward.
   Consequently the body sees [rev xs] at de Bruijn indices 0,1,... . *)
Fixpoint pushListEnv (xs : list nat) (e : nat -> nat) : nat -> nat :=
  match xs with
  | [] => e
  | x :: xs => pushListEnv xs (Fol.scons nat x e)
  end.

Lemma Sat_existsN (n : nat) (phi : PA.formula) (e : nat -> nat) :
  Formula.Sat natModel e (existsN n phi) <->
  exists xs, List.length xs = n /\
             Formula.Sat natModel (pushListEnv xs e) phi.
Proof.
  revert e.
  induction n as [|n IH]; intros e; cbn [existsN Formula.Sat].
  - split.
    + intro H. exists []; auto.
    + intros [xs [Hlen H]]. destruct xs as [|x xs].
      * exact H.
      * cbn in Hlen. discriminate.
  - split.
    + intros [x H].
      apply IH in H.
      destruct H as [xs [Hlen Hsat]].
      exists (x :: xs). cbn. auto.
    + intros [xs [Hlen Hsat]].
      destruct xs as [|x xs]; cbn in Hlen; [discriminate |].
      exists x. apply IH.
      exists xs. cbn in Hsat. auto.
Qed.

Lemma pushListEnv_after (xs : list nat) (e : nat -> nat) (j : nat) :
  pushListEnv xs e (List.length xs + j) = e j.
Proof.
  induction xs as [|x xs IH] in e, j |- *; cbn [pushListEnv].
  - reflexivity.
  - change (pushListEnv xs (Fol.scons nat x e)
        (S (List.length xs) + j) = e j).
    replace (S (List.length xs) + j) with
        (List.length xs + S j) by lia.
    rewrite IH. reflexivity.
Qed.

Lemma pushListEnv_from_end (xs : list nat) (e : nat -> nat) (i : nat) :
  i < List.length xs ->
  pushListEnv xs e (List.length xs - S i) = List.nth i xs 0.
Proof.
  induction xs as [|x xs IH] in e, i |- *; cbn.
  - lia.
  - intro hi. destruct i as [|i].
    + rewrite Nat.sub_0_r.
      replace (List.length xs) with (List.length xs + 0) by lia.
      rewrite pushListEnv_after. reflexivity.
    + apply IH. lia.
Qed.

(* A list containing the values of a finite function in Fin order. *)
Fixpoint finValues (n : nat) : (Fin.t n -> nat) -> list nat :=
  match n as n' return (Fin.t n' -> nat) -> list nat with
  | 0 => fun _ => []
  | S n => fun nu => nu Fin.F1 :: @finValues n (fun i => nu (Fin.FS i))
  end.

Arguments finValues n nu : clear implicits.

Lemma finValues_length (n : nat) (nu : Fin.t n -> nat) :
  List.length (finValues n nu) = n.
Proof.
  induction n as [|n IH] in nu |- *; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma finValues_nth (n : nat) (nu : Fin.t n -> nat) (i : Fin.t n) :
  List.nth (finIndex i) (finValues n nu) 0 = nu i.
Proof.
  induction n as [|n IH] in nu, i |- *.
  - exact (Fin.case0 (fun i =>
      List.nth (finIndex i) (finValues 0 nu) 0 = nu i) i).
  - revert nu.
    refine (Fin.caseS' i
      (fun i => forall nu : Fin.t (S n) -> nat,
        List.nth (finIndex i) (finValues (S n) nu) 0 = nu i) _ _).
    + intro nu. reflexivity.
    + intros j nu. rewrite finIndex_FS. cbn [finValues List.nth].
      apply IH.
Qed.

(* There are [m] existential polynomial variables and [n] parameters.

   [existsN m] introduces witnesses from the outside inward, so the first
   witness ends up at body index [m-1].  Hence polynomial variable [i] is
   represented by [m-1-i = m - S i].  All binders precede the parameters,
   so parameter [j] is represented by body index [m+j]. *)
Definition equationTerm {m n}
    (p : dio_polynomial (Fin.t m) (Fin.t n)) : PA.term :=
  polyTerm
    (fun i => tVar (m - S (finIndex i)))
    (fun j => tVar (m + finIndex j)) p.

Definition equationBody {m n}
    (p q : dio_polynomial (Fin.t m) (Fin.t n)) : PA.formula :=
  pEq (equationTerm p) (equationTerm q).

Definition diophantineFormula {m n}
    (p q : dio_polynomial (Fin.t m) (Fin.t n)) : PA.formula :=
  existsN m (equationBody p q).

Lemma eval_equationTerm {m n}
    (p : dio_polynomial (Fin.t m) (Fin.t n))
    (xs : list nat) (e : nat -> nat) :
  List.length xs = m ->
  Term.eval natModel (pushListEnv xs e) (equationTerm p) =
  dp_eval (fun i => List.nth (finIndex i) xs 0)
          (fun j => e (finIndex j)) p.
Proof.
  intro Hlen.
  unfold equationTerm.
  rewrite eval_polyTerm.
  eapply dp_eval_ext.
  - intros i _.
    cbn [Term.eval].
    replace (m - S (finIndex i)) with
        (List.length xs - S (finIndex i)) by lia.
    apply pushListEnv_from_end.
    pose proof (finIndex_lt i). lia.
  - intros j _.
    cbn [Term.eval].
    replace (m + finIndex j) with
        (List.length xs + finIndex j) by lia.
    apply pushListEnv_after.
Qed.

Theorem diophantineFormula_correct_env {m n}
    (p q : dio_polynomial (Fin.t m) (Fin.t n)) (e : nat -> nat) :
  Formula.Sat natModel e (diophantineFormula p q) <->
  exists nu : Fin.t m -> nat,
    dp_eval nu (fun j => e (finIndex j)) p =
    dp_eval nu (fun j => e (finIndex j)) q.
Proof.
  unfold diophantineFormula.
  rewrite Sat_existsN.
  split.
  - intros [xs [Hlen Hsat]].
    cbn [equationBody Formula.Sat] in Hsat.
    rewrite (eval_equationTerm p xs e Hlen) in Hsat.
    rewrite (eval_equationTerm q xs e Hlen) in Hsat.
    now exists (fun i => List.nth (finIndex i) xs 0).
  - intros [nu Hnu].
    exists (finValues m nu). split.
    + apply finValues_length.
    + cbn [equationBody Formula.Sat].
      rewrite (eval_equationTerm p (finValues m nu) e
        (@finValues_length m nu)).
      rewrite (eval_equationTerm q (finValues m nu) e
        (@finValues_length m nu)).
      assert (Hvalues :
        (fun i => List.nth (finIndex i) (finValues m nu) 0) = nu).
      { apply functional_extensionality. intro i. apply finValues_nth. }
      now rewrite Hvalues.
Qed.

Corollary diophantineFormula_correct_vector {m n}
    (p q : dio_polynomial (Fin.t m) (Fin.t n))
    (v : Vector.t nat n) :
  Formula.Sat natModel (vectorEnv v) (diophantineFormula p q) <->
  exists nu : Fin.t m -> nat,
    dp_eval nu (fun j => Vector.nth v j) p =
    dp_eval nu (fun j => Vector.nth v j) q.
Proof.
  rewrite diophantineFormula_correct_env.
  assert (Henv :
    (fun j : Fin.t n => vectorEnv v (finIndex j)) =
    (fun j : Fin.t n => Vector.nth v j)).
  { apply functional_extensionality. intro j. apply vectorEnv_finIndex. }
  now rewrite Henv.
Qed.

Theorem Diophantine_has_PA_formula {n}
    (R : Vector.t nat n -> Prop) :
  Diophantine R ->
  exists phi : PA.formula, forall v,
    Formula.Sat natModel (vectorEnv v) phi <-> R v.
Proof.
  intros [m [p [q Hpq]]].
  exists (diophantineFormula p q).
  intro v.
  rewrite diophantineFormula_correct_vector.
  specialize (Hpq v). cbn in Hpq. tauto.
Qed.

(* In [Diophantine' R], upstream orders the parameter vector as
   [output ; input_0 ; ... ; input_(k-1)].  Thus the resulting PA graph
   formula has output at free de Bruijn index 0 and the k inputs at free
   indices 1,...,k. *)
Definition graphEnv {k} (v : Vector.t nat k) (y : nat) : nat -> nat :=
  vectorEnv (Vector.cons nat y k v).

Theorem Diophantine'_has_PA_formula {k}
    (R : Vector.t nat k -> nat -> Prop) :
  Diophantine' R ->
  exists phi : PA.formula, forall v y,
    Formula.Sat natModel (graphEnv v y) phi <-> R v y.
Proof.
  unfold Diophantine'.
  intros [m [p [q Hpq]]].
  exists (diophantineFormula p q).
  intros v y.
  unfold graphEnv.
  rewrite diophantineFormula_correct_vector.
  specialize (Hpq (Vector.cons nat y k v)).
  cbn in Hpq. tauto.
Qed.
