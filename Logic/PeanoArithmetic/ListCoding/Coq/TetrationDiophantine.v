(**
  Natural-number tetration is Diophantine.

  We use the height convention

      tetration a 0     = 1
      tetration a (S h) = a ^ tetration a h.

  Exponentiation alone is not enough to obtain this result merely by closure
  under composition: the height is a variable, so a certificate must contain
  an entire finite exponentiation trace.  The Undecidability library theorem
  [dio_rel_rel_iter] supplies exactly this closure property for Diophantine
  binary relations.  Internally it encodes a trace as digits in a sufficiently
  large base and compiles the bounded assertion that every adjacent pair is a
  valid step.

  The base [a] must remain available at every step of the trace.  We therefore
  iterate on the injective polynomial state code

      stateCode a x = (a + x)^2 + x,

  which carries both the fixed base and the current tower value.  A step takes
  [(a,x)] to [(a,a^x)].  Injectivity prevents a trace from changing its base.
*)

From Stdlib Require Import Arith Lia Vector.
From PAListCoding Require Import ExponentiationDiophantine.
From Undecidability.Shared.Libs.DLW.Utils Require Import rel_iter sums.
From Undecidability.H10 Require Import H10.
From Undecidability.H10.Dio
  Require Import dio_logic dio_expo dio_rt_closure dio_single.

Module PAListTetrationDiophantine.

Import PAListExponentiationDiophantine.

(** The right-associated power tower of base [a] and height [h].  In
    particular, height zero has value one and height one has value [a]. *)
Fixpoint tetration (a h : nat) : nat :=
  match h with
  | 0 => 1
  | S h => Nat.pow a (tetration a h)
  end.

(** A polynomial pairing specialized to trace states.  Values with a fixed
    sum [a+x] occupy the interval from [(a+x)^2] through
    [(a+x)^2+(a+x)], while the next sum starts strictly above that interval.
    This makes the code injective without division or subtraction. *)
Definition stateCode (a x : nat) : nat :=
  (a + x) * (a + x) + x.

Lemma stateCode_injective : forall a x b y,
  stateCode a x = stateCode b y -> a = b /\ x = y.
Proof.
  intros a x b y Hcode.
  unfold stateCode in Hcode.
  destruct (Nat.eq_dec (a + x) (b + y)) as [Hsum | Hsum].
  - split; nia.
  - exfalso; apply Hsum; nia.
Qed.

(** A single transition preserves the encoded base and raises it to the
    encoded current value.  This relation has no external parameter, which is
    why it can be passed directly to the generic iteration theorem. *)
Definition TetrationStep (s t : nat) : Prop :=
  exists a x,
    s = stateCode a x /\
    t = stateCode a (Nat.pow a x).

Lemma TetrationStep_from_code : forall a x t,
  TetrationStep (stateCode a x) t <->
  t = stateCode a (Nat.pow a x).
Proof.
  intros a x t; split.
  - intros (b & y & Hsource & Htarget).
    destruct (stateCode_injective _ _ _ _ Hsource) as [-> ->].
    exact Htarget.
  - intro Htarget.
    exists a, x; auto.
Qed.

(** The transition relation is Diophantine.  The only non-polynomial
    subexpression is [a^x]; [dio_fun_expo] is the constructive
    Matiyasevich/Pell representation already used by the exponentiation
    module. *)
Theorem TetrationStep_dio_rel :
  𝔻R (fun nu => TetrationStep (nu 1) (nu 0)).
Proof.
  apply dio_rel_equiv with
      (R := fun nu => exists a x,
        nu 1 = stateCode a x /\
        nu 0 = stateCode a (mscal mult 1 x a)).
  - intro nu. unfold TetrationStep.
    split.
    + intros (a & x & Hsource & Htarget).
      exists a, x; split; [exact Hsource |].
      now rewrite <- nat_pow_eq_mscal.
    + intros (a & x & Hsource & Htarget).
      exists a, x; split; [exact Hsource |].
      now rewrite nat_pow_eq_mscal.
  - unfold stateCode. dio auto.
Defined.

(** Iterating the encoded transition from [(a,1)] has a unique endpoint:
    after [h] steps it is exactly [(a,tetration a h)]. *)
Lemma rel_iter_TetrationStep : forall a h s,
  rel_iter TetrationStep h (stateCode a 1) s <->
  s = stateCode a (tetration a h).
Proof.
  intros a h; induction h as [|h IH]; intro s.
  - cbn [rel_iter tetration]. split; intro H; symmetry; exact H.
  - rewrite rel_iter_S. split.
    + intros (middle & Hprefix & Hlast).
      apply IH in Hprefix. subst middle.
      apply TetrationStep_from_code in Hlast.
      exact Hlast.
    + intro Hendpoint.
      exists (stateCode a (tetration a h)); split.
      * apply IH. reflexivity.
      * apply TetrationStep_from_code.
        exact Hendpoint.
Qed.

(** Semantic characterization of tetration by a finite Diophantine trace. *)
Lemma tetration_rel_iter : forall result base height,
  result = tetration base height <->
  rel_iter TetrationStep height
    (stateCode base 1) (stateCode base result).
Proof.
  intros result base height.
  rewrite rel_iter_TetrationStep. split.
  - now intros ->.
  - intro Hcode.
    now destruct (stateCode_injective _ _ _ _ Hcode).
Qed.

(** The infinite-valuation, result-first graph.  Applying
    [dio_rel_rel_iter] is the substantive closure step: it converts the
    variable-length trace into one Diophantine formula. *)
Theorem Tetration_dio_rel :
  𝔻R (fun nu => nu 0 = tetration (nu 1) (nu 2)).
Proof.
  apply dio_rel_equiv with
      (R := fun nu => rel_iter TetrationStep (nu 2)
        (stateCode (nu 1) 1) (stateCode (nu 1) (nu 0))).
  - intro nu. apply tetration_rel_iter.
  - apply dio_rel_rel_iter.
    + exact TetrationStep_dio_rel.
    + apply dio_fun_var.
    + unfold stateCode. dio auto.
    + unfold stateCode. dio auto.
Defined.

(** An inspectable formula witness for the result-first graph. *)
Definition tetrationDiophantineFormula : dio_formula :=
  proj1_sig Tetration_dio_rel.

Theorem tetrationDiophantineFormula_spec : forall nu,
  df_pred tetrationDiophantineFormula nu <->
  nu 0 = tetration (nu 1) (nu 2).
Proof.
  exact (proj2_sig Tetration_dio_rel).
Qed.

(** Compile the trace formula to a single equality of natural polynomials
    with existentially quantified auxiliary variables. *)
Definition tetrationDiophantineEquation :
  { E : dio_single nat nat |
    forall nu,
      nu 0 = tetration (nu 1) (nu 2) <-> dio_single_pred E nu } :=
  dio_rel_single Tetration_dio_rel.

(** Official three-parameter H10 graph, ordered as result, base, height. *)
Definition TetrationVector (v : Vector.t nat 3) : Prop :=
  Vector.nth v Fin.F1 =
  tetration
    (Vector.nth v (Fin.FS Fin.F1))
    (Vector.nth v (Fin.FS (Fin.FS Fin.F1))).

(** Natural-number tetration is Diophantine in the repository's standard
    finite-vector sense: one polynomial equality with finitely many
    existentially quantified natural-number witnesses. *)
Theorem Tetration_Diophantine :
  Diophantine TetrationVector.
Proof.
  unfold TetrationVector.
  change (Diophantine
    (fun v : Vector.t nat 3 =>
      finiteEnv v 0 = tetration (finiteEnv v 1) (finiteEnv v 2))).
  apply (@dio_rel_Diophantine 3
    (fun nu => nu 0 = tetration (nu 1) (nu 2))).
  exact Tetration_dio_rel.
Qed.

End PAListTetrationDiophantine.
