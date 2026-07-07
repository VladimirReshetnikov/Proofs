(*
  Coq port of LeanProofs/EquationalLogic.lean.

  This is a tiny first-order checker for one-binary-operation equational
  proof certificates.  The checker is executable; the theorems below prove
  that every checked certificate step is semantically sound in every algebra
  satisfying the initial equations.
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.

Import ListNotations.

Set Implicit Arguments.

Module LeanProofs.
Module EquationalLogic.

Inductive Term : Type :=
| Var : nat -> Term
| Op : Term -> Term -> Term.

Fixpoint term_eq_dec (x y : Term) : {x = y} + {x <> y}.
Proof.
  decide equality.
  apply Nat.eq_dec.
Defined.

Module Term.

Fixpoint eval {A : Type} (op : A -> A -> A) (env : nat -> A)
    (t : EquationalLogic.Term) : A :=
  match t with
  | Var n => env n
  | Op l r => op (eval op env l) (eval op env r)
  end.

Fixpoint subterm (t : EquationalLogic.Term) (path : list bool)
    : option EquationalLogic.Term :=
  match t, path with
  | _, [] => Some t
  | Op l _, false :: rest => subterm l rest
  | Op _ r, true :: rest => subterm r rest
  | Var _, _ :: _ => None
  end.

Fixpoint replace (t : EquationalLogic.Term) (path : list bool)
    (replacement : EquationalLogic.Term) : option EquationalLogic.Term :=
  match t, path with
  | _, [] => Some replacement
  | Op l r, false :: rest =>
      match replace l rest replacement with
      | Some l' => Some (Op l' r)
      | None => None
      end
  | Op l r, true :: rest =>
      match replace r rest replacement with
      | Some r' => Some (Op l r')
      | None => None
      end
  | Var _, _ :: _ => None
  end.

Theorem replace_sound {A : Type} {op : A -> A -> A} {env : nat -> A}
    {t old replacement t' : EquationalLogic.Term} {path : list bool}
    (hrep : replace t path replacement = Some t')
    (hsub : subterm t path = Some old)
    (heq : eval op env old = eval op env replacement) :
    eval op env t = eval op env t'.
Proof.
  revert path old t' hrep hsub heq.
  induction t as [n | l IHl r IHr]; intros path old t' hrep hsub heq;
    destruct path as [|dir path]; simpl in *.
  - inversion hrep; inversion hsub; subst; exact heq.
  - discriminate.
  - inversion hrep; inversion hsub; subst; exact heq.
  - destruct dir.
    + destruct (replace r path replacement) as [r'|] eqn:hr;
        inversion hrep; subst.
      simpl. rewrite <- (IHr path old r' hr hsub heq). reflexivity.
    + destruct (replace l path replacement) as [l'|] eqn:hl;
        inversion hrep; subst.
      simpl. rewrite <- (IHl path old l' hl hsub heq). reflexivity.
Qed.

End Term.

Definition Subst := list (nat * Term).

Module Subst.

Fixpoint lookup (sigma : Subst) (n : nat) : option Term :=
  match sigma with
  | [] => None
  | (m, t) :: rest =>
      if Nat.eq_dec m n then Some t else lookup rest n
  end.

Definition evalEnv {A : Type} (op : A -> A -> A) (env : nat -> A)
    (sigma : Subst) : nat -> A :=
  fun n =>
    match lookup sigma n with
    | Some t => Term.eval op env t
    | None => env n
    end.

End Subst.

Module TermInst.

Fixpoint inst (sigma : Subst) (t : Term) : Term :=
  match t with
  | Var n =>
      match Subst.lookup sigma n with
      | Some t' => t'
      | None => Var n
      end
  | Op l r => Op (inst sigma l) (inst sigma r)
  end.

Theorem eval_inst {A : Type} {op : A -> A -> A} {env : nat -> A}
    (sigma : Subst) :
    forall t : Term,
      Term.eval op env (inst sigma t) =
      Term.eval op (Subst.evalEnv op env sigma) t.
Proof.
  induction t as [n | l IHl r IHr]; simpl.
  - unfold Subst.evalEnv.
    destruct (Subst.lookup sigma n); reflexivity.
  - now rewrite IHl, IHr.
Qed.

End TermInst.

Record Equation : Type := {
  lhs : Term;
  rhs : Term
}.

Fixpoint list_bool_eq_dec (xs ys : list bool) : {xs = ys} + {xs <> ys}.
Proof.
  decide equality.
  decide equality.
Defined.

Definition equation_eq_dec (x y : Equation) : {x = y} + {x <> y}.
Proof.
  decide equality; apply term_eq_dec.
Defined.

Module Equation.

Definition symm (e : EquationalLogic.Equation) : EquationalLogic.Equation :=
  {| lhs := rhs e; rhs := lhs e |}.

Definition inst (sigma : Subst) (e : EquationalLogic.Equation)
    : EquationalLogic.Equation :=
  {| lhs := TermInst.inst sigma (lhs e);
     rhs := TermInst.inst sigma (rhs e) |}.

Definition Valid {A : Type} (op : A -> A -> A)
    (e : EquationalLogic.Equation) : Prop :=
  forall env : nat -> A, Term.eval op env (lhs e) = Term.eval op env (rhs e).

Theorem valid_symm {A : Type} {op : A -> A -> A} {e : EquationalLogic.Equation}
    (h : Valid op e) : Valid op (symm e).
Proof.
  intro env. symmetry. apply h.
Qed.

Theorem valid_inst {A : Type} {op : A -> A -> A} {e : EquationalLogic.Equation}
    (h : Valid op e) (sigma : Subst) : Valid op (inst sigma e).
Proof.
  intro env.
  unfold inst; simpl.
  rewrite !TermInst.eval_inst.
  apply h.
Qed.

Record Pos : Type := {
  side : bool;
  path : list bool
}.

Definition pos_eq_dec (x y : Pos) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply list_bool_eq_dec.
  - decide equality.
Defined.

Definition subterm (e : EquationalLogic.Equation) (pos : Pos)
    : option Term :=
  if side pos then Term.subterm (rhs e) (path pos)
  else Term.subterm (lhs e) (path pos).

Definition replace (e : EquationalLogic.Equation) (pos : Pos)
    (replacement : Term) : option EquationalLogic.Equation :=
  if side pos then
    match Term.replace (rhs e) (path pos) replacement with
    | Some rhs' => Some {| lhs := lhs e; rhs := rhs' |}
    | None => None
    end
  else
    match Term.replace (lhs e) (path pos) replacement with
    | Some lhs' => Some {| lhs := lhs'; rhs := rhs e |}
    | None => None
    end.

Theorem replace_valid {A : Type} {op : A -> A -> A}
    {source target : EquationalLogic.Equation} {pos : Pos}
    {old replacement : Term}
    (hrep : replace source pos replacement = Some target)
    (hsub : subterm source pos = Some old)
    (hsource : Valid op source)
    (hrule : Valid op {| lhs := old; rhs := replacement |}) :
    Valid op target.
Proof.
  intro env.
  destruct target as [target_lhs target_rhs].
  destruct pos as [s p]; simpl in *.
  unfold replace, subterm in hrep, hsub; simpl in hrep, hsub.
  destruct s.
  - destruct (Term.replace (rhs source) p replacement) eqn:hr;
      try discriminate.
    inversion hrep; subst; simpl.
    transitivity (Term.eval op env (rhs source)).
    + apply hsource.
    + eapply Term.replace_sound; eauto.
  - destruct (Term.replace (lhs source) p replacement) eqn:hl;
      try discriminate.
    inversion hrep; subst; simpl.
    transitivity (Term.eval op env (lhs source)).
    + symmetry.
      eapply Term.replace_sound; eauto.
    + apply hsource.
Qed.

End Equation.

Module Matching.

Definition bind (n : nat) (t : Term) (sigma : Subst) : option Subst :=
  match Subst.lookup sigma n with
  | None => Some ((n, t) :: sigma)
  | Some old => if term_eq_dec old t then Some sigma else None
  end.

Fixpoint matchTerm (pattern target : Term) (sigma : Subst) : option Subst :=
  match pattern, target with
  | Var n, _ => bind n target sigma
  | Op l r, Op l' r' =>
      match matchTerm l l' sigma with
      | Some sigma' => matchTerm r r' sigma'
      | None => None
      end
  | Op _ _, Var _ => None
  end.

Definition instanceSubst (pattern target : Equation) : option Subst :=
  match matchTerm (lhs pattern) (lhs target) [] with
  | None => None
  | Some sigma1 =>
      match matchTerm (rhs pattern) (rhs target) sigma1 with
      | None => None
      | Some sigma2 =>
          if equation_eq_dec (Equation.inst sigma2 pattern) target
          then Some sigma2 else None
      end
  end.

Theorem instanceSubst_sound {pattern target : Equation} {sigma : Subst}
    (h : instanceSubst pattern target = Some sigma) :
    Equation.inst sigma pattern = target.
Proof.
  unfold instanceSubst in h.
  destruct (matchTerm (lhs pattern) (lhs target) []) as [sigma1|] eqn:h1;
    try discriminate.
  destruct (matchTerm (rhs pattern) (rhs target) sigma1) as [sigma2|] eqn:h2;
    try discriminate.
  destruct (equation_eq_dec (Equation.inst sigma2 pattern) target) as [Heq|Hne].
  - injection h as Hsigma; subst sigma; exact Heq.
  - discriminate.
Qed.

Theorem valid_of_instance {A : Type} {op : A -> A -> A}
    {pattern target : Equation} {sigma : Subst}
    (hinst : instanceSubst pattern target = Some sigma)
    (hvalid : Equation.Valid op pattern) :
    Equation.Valid op target.
Proof.
  pose proof (instanceSubst_sound hinst) as heq.
  rewrite <- heq.
  now apply Equation.valid_inst.
Qed.

End Matching.

Definition AllValid {A : Type} (op : A -> A -> A) (eqs : list Equation)
    : Prop :=
  forall e, In e eqs -> Equation.Valid op e.

Module Certificate.

Definition knownFrom (eqs : list Equation) (target : Equation) : bool :=
  existsb
    (fun pattern =>
      match Matching.instanceSubst pattern target with
      | Some _ => true
      | None =>
          match Matching.instanceSubst (Equation.symm pattern) target with
          | Some _ => true
          | None => false
          end
      end)
    eqs.

Definition known (eqs : list Equation) (target : Equation) : bool :=
  if term_eq_dec (lhs target) (rhs target) then true else knownFrom eqs target.

Theorem knownFrom_sound {A : Type} {op : A -> A -> A}
    {eqs : list Equation} {target : Equation}
    (hknown : knownFrom eqs target = true)
    (hall : AllValid op eqs) :
    Equation.Valid op target.
Proof.
  unfold knownFrom in hknown.
  induction eqs as [|pattern rest IH]; simpl in hknown.
  - discriminate.
  - destruct (Matching.instanceSubst pattern target) as [sigma|] eqn:h1.
    + exact (Matching.valid_of_instance h1 (hall pattern (or_introl eq_refl))).
    + destruct (Matching.instanceSubst (Equation.symm pattern) target)
        as [sigma2|] eqn:h2.
      * exact (Matching.valid_of_instance h2
          (Equation.valid_symm (hall pattern (or_introl eq_refl)))).
      * simpl in hknown.
        apply IH.
        -- exact hknown.
        -- intros e he. exact (hall e (or_intror he)).
Qed.

Theorem known_sound {A : Type} {op : A -> A -> A}
    {eqs : list Equation} {target : Equation}
    (hknown : known eqs target = true)
    (hall : AllValid op eqs) :
    Equation.Valid op target.
Proof.
  unfold known in hknown.
  destruct (term_eq_dec (lhs target) (rhs target)) as [heq|hne].
  - intro env. now rewrite heq.
  - exact (knownFrom_sound hknown hall).
Qed.

Record Step : Type := {
  source : Equation;
  ruleEq : Equation;
  pos : Equation.Pos;
  target : Equation
}.

Definition step_eq_dec (x y : Step) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply equation_eq_dec.
  - apply Equation.pos_eq_dec.
  - apply equation_eq_dec.
  - apply equation_eq_dec.
Defined.

Definition checkStep (eqs : list Equation) (step : Step) : bool :=
  if known eqs (source step) then
    match Equation.subterm (source step) (pos step),
          Equation.subterm (target step) (pos step) with
    | Some old, Some replacement =>
        match Matching.instanceSubst (ruleEq step)
          {| lhs := old; rhs := replacement |} with
        | Some _ =>
            if equation_eq_dec
                (option_rect (fun _ => Equation) (fun e => e) (source step)
                   (Equation.replace (source step) (pos step) replacement))
                (target step)
            then known eqs (ruleEq step)
            else false
        | None => false
        end
    | _, _ => false
    end
  else false.

(* A cleaner boolean form of [Equation.replace source pos replacement = Some target]. *)
Definition replacedBy (source : Equation) (pos : Equation.Pos)
    (replacement : Term) (target : Equation) : bool :=
  match Equation.replace source pos replacement with
  | Some target' => if equation_eq_dec target' target then true else false
  | None => false
  end.

Definition checkStep' (eqs : list Equation) (step : Step) : bool :=
  known eqs (source step) &&
    match Equation.subterm (source step) (pos step),
          Equation.subterm (target step) (pos step) with
    | Some old, Some replacement =>
        match Matching.instanceSubst (ruleEq step)
          {| lhs := old; rhs := replacement |} with
        | Some _ =>
            replacedBy (source step) (pos step) replacement (target step) &&
              known eqs (ruleEq step)
        | None => false
        end
    | _, _ => false
    end.

Theorem checkStep_sound {A : Type} {op : A -> A -> A}
    {eqs : list Equation} {step : Step}
    (hcheck : checkStep' eqs step = true)
    (hall : AllValid op eqs) :
    Equation.Valid op (target step).
Proof.
  unfold checkStep' in hcheck.
  apply andb_true_iff in hcheck as [hsourceKnown hrest].
  destruct (Equation.subterm (source step) (pos step)) as [old|] eqn:hold;
    try discriminate.
  destruct (Equation.subterm (target step) (pos step)) as [replacement|] eqn:hnew;
    try discriminate.
  destruct (Matching.instanceSubst (ruleEq step)
      {| lhs := old; rhs := replacement |}) as [sigma|] eqn:hinst;
    try discriminate.
  apply andb_true_iff in hrest as [hrepBool hruleKnown].
  unfold replacedBy in hrepBool.
  destruct (Equation.replace (source step) (pos step) replacement)
    as [target'|] eqn:hrep; try discriminate.
  destruct (equation_eq_dec target' (target step)) as [heq|hne];
    try discriminate.
  subst target'.
  eapply Equation.replace_valid.
  - exact hrep.
  - exact hold.
  - exact (known_sound hsourceKnown hall).
  - exact (Matching.valid_of_instance hinst (known_sound hruleKnown hall)).
Qed.

Inductive Item : Type :=
| Add : Equation -> Item
| Rewrite : Step -> Item.

Definition item_eq_dec (x y : Item) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply equation_eq_dec.
  - apply step_eq_dec.
Defined.

Definition itemTarget (item : Item) : Equation :=
  match item with
  | Add e => e
  | Rewrite step => target step
  end.

Definition checkItem (eqs : list Equation) (item : Item) : bool :=
  match item with
  | Add e => known eqs e
  | Rewrite step => checkStep' eqs step
  end.

Theorem checkItem_sound {A : Type} {op : A -> A -> A}
    {eqs : list Equation} {item : Item}
    (hcheck : checkItem eqs item = true)
    (hall : AllValid op eqs) :
    Equation.Valid op (itemTarget item).
Proof.
  destruct item as [e | step]; simpl in *.
  - exact (known_sound hcheck hall).
  - exact (checkStep_sound hcheck hall).
Qed.

Fixpoint runItems (eqs : list Equation) (items : list Item)
    : option (list Equation) :=
  match items with
  | [] => Some eqs
  | item :: rest =>
      if checkItem eqs item then
        runItems (itemTarget item :: eqs) rest
      else None
  end.

Theorem runItems_sound {A : Type} {op : A -> A -> A}
    {initial final : list Equation} {items : list Item}
    (hrun : runItems initial items = Some final)
    (hinitial : AllValid op initial) :
    AllValid op final.
Proof.
  revert initial hrun hinitial.
  induction items as [|item rest IH]; intros initial hrun hinitial; simpl in hrun.
  - inversion hrun; subst; exact hinitial.
  - destruct (checkItem initial item) eqn:hcheck; try discriminate.
    apply IH with (initial := itemTarget item :: initial).
    + exact hrun.
    + intros e he.
      destruct he as [heq | hmem].
      * subst e. exact (checkItem_sound hcheck hinitial).
      * exact (hinitial e hmem).
Qed.

End Certificate.

End EquationalLogic.
End LeanProofs.
