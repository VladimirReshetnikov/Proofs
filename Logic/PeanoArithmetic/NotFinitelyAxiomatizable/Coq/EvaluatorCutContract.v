(**
  The evaluator-independent proper-cut argument.

  A fixed arithmetic formula is assumed to enumerate the carrier by
  standard numeral codes, functionally at every standard code.  Together
  with the elementary order theory of an externally nonstandard seed, this
  defines the standard cut internally and yields a false genuine induction
  axiom.  No Peano axiom is assumed of the structure in this file.
*)

From Stdlib Require Import List Arith Lia Classical ClassicalChoice
  ClassicalDescription
  Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import FiniteBasisReduction
  HierarchyReduction
  FiniteSkolemHull CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.

Import ListNotations.
Import PAFiniteBasisReduction.
Import PAHierarchyReduction.
Import PAFiniteSkolemHull.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.

Module PAEvaluatorCutContract.

(** The fixed free-variable convention is output, code, seed. *)
Definition evalEnv (M : RawPAModel)
    (seed code output : M) : nat -> M :=
  fun i =>
    match i with
    | 0 => output
    | 1 => code
    | 2 => seed
    | _ => raw_zero M
    end.

Definition Evaluates (M : RawPAModel) (evalFormula : PA.formula)
    (seed code output : M) : Prop :=
  raw_formula_sat M (evalEnv M seed code output) evalFormula.

Definition IsStandard (M : RawPAModel) (x : M) : Prop :=
  exists n, x = rawNumeralValue M n.

Definition AboveAllNumerals (M : RawPAModel) (x : M) : Prop :=
  forall n, rawLt M (rawNumeralValue M n) x.

(** The exact semantic interface required from the eventual program trace. *)
Record EvaluatorContract (M : RawPAModel) (evalFormula : PA.formula)
    (seed : M) : Prop := {
  contract_standard_code_total :
    forall output : M, exists code : nat,
      Evaluates M evalFormula seed (rawNumeralValue M code) output;
  contract_standard_code_functional :
    forall (code : nat) (x y : M),
      Evaluates M evalFormula seed (rawNumeralValue M code) x ->
      Evaluates M evalFormula seed (rawNumeralValue M code) y ->
      x = y;
  contract_numeral_injective :
    forall m n, rawNumeralValue M m = rawNumeralValue M n -> m = n;
  contract_lt_numeral :
    forall (x : M) (bound : nat),
      rawLt M x (rawNumeralValue M bound) ->
      exists n, n < bound /\ x = rawNumeralValue M n;
  contract_standard_or_above :
    forall x : M, IsStandard M x \/ AboveAllNumerals M x;
  contract_seed_above : AboveAllNumerals M seed
}.

(** The sole formula whose elementarity is needed to transport the order
    facts used by the contract into a finite Skolem hull. *)
Definition hullLtFormula : PA.formula :=
  PA.Formula.ltTermAt (PA.tVar 0) (PA.tVar 1).

Definition hullBetaFormula : PA.formula :=
  PA.Formula.betaTermTermAt
    (PA.tVar 0) (PA.tVar 1) (PA.tVar 2) (PA.tVar 3).

Lemma skolemHull_rawNumeralValue_val : forall
    (M : RawPAModel) (seed : M) selectorRank selector n,
  skolemHullVal M seed selectorRank selector
    (rawNumeralValue
      (skolemHullRawModel M seed selectorRank selector) n) =
  rawNumeralValue M n.
Proof.
  intros M seed selectorRank selector n.
  induction n as [|n IH]; cbn [rawNumeralValue].
  - apply skolemHullVal_zero.
  - rewrite skolemHullVal_succ, IH. reflexivity.
Qed.

Lemma skolemHullVal_injective : forall
    (M : RawPAModel) (seed : M) selectorRank selector
    (x y : skolemHullRawModel M seed selectorRank selector),
  skolemHullVal M seed selectorRank selector x =
  skolemHullVal M seed selectorRank selector y -> x = y.
Proof.
  intros M seed selectorRank selector x y hxy.
  apply eq_sig_hprop.
  - intros value p q. apply proof_irrelevance.
  - exact hxy.
Qed.

Lemma skolemHull_rawLt_to_ambient : forall
    (M : RawPAModel) (seed : M) selectorRank selector
    (x y : skolemHullRawModel M seed selectorRank selector),
  rawLt (skolemHullRawModel M seed selectorRank selector) x y ->
  rawLt M
    (skolemHullVal M seed selectorRank selector x)
    (skolemHullVal M seed selectorRank selector y).
Proof.
  intros M seed selectorRank selector x y [gap hgap].
  exists (skolemHullVal M seed selectorRank selector gap).
  apply (f_equal (skolemHullVal M seed selectorRank selector)) in hgap.
  rewrite skolemHullVal_add, skolemHullVal_succ in hgap.
  exact hgap.
Qed.

Lemma skolemHull_rawLt_of_ambient : forall
    (M : RawPAModel) (seed : M) selectorRank selector,
  SelectorWitnesses M selector ->
  formula_rank hullLtFormula <= selectorRank ->
  forall (x y : skolemHullRawModel M seed selectorRank selector),
    rawLt M
      (skolemHullVal M seed selectorRank selector x)
      (skolemHullVal M seed selectorRank selector y) ->
    rawLt (skolemHullRawModel M seed selectorRank selector) x y.
Proof.
  intros M seed selectorRank selector hselector hLtRank x y hlt.
  set (K := skolemHullRawModel M seed selectorRank selector).
  set (tail := fun _ : nat => raw_zero K).
  set (e := scons K x (scons K y tail)).
  apply (proj1 (raw_sat_ltTermAt_iff K
    (PA.tVar 0) (PA.tVar 1) e)).
  cbn [raw_term_eval e scons].
  apply (proj2 (skolemHull_formula_elementary
    M seed selectorRank selector
    (formula_rank hullLtFormula) hullLtFormula
    hselector (Nat.le_refl _) hLtRank e)).
  apply (proj2 (raw_sat_ltTermAt_iff M
    (PA.tVar 0) (PA.tVar 1)
    (fun n => skolemHullVal M seed selectorRank selector (e n)))).
  cbn [raw_term_eval e scons].
  exact hlt.
Qed.

Lemma skolemHull_raw_order_trichotomy_of_ambient : forall
    (M : RawPAModel) (seed : M) selectorRank selector,
  SelectorWitnesses M selector ->
  formula_rank hullLtFormula <= selectorRank ->
  RawLtTrichotomy M ->
  forall (x y : skolemHullRawModel M seed selectorRank selector),
    x = y \/
    rawLt (skolemHullRawModel M seed selectorRank selector) x y \/
    rawLt (skolemHullRawModel M seed selectorRank selector) y x.
Proof.
  intros M seed selectorRank selector hselector hLtRank htri x y.
  destruct (htri
      (skolemHullVal M seed selectorRank selector x)
      (skolemHullVal M seed selectorRank selector y))
    as [heq | [hlt | hgt]].
  - left. exact (skolemHullVal_injective
      M seed selectorRank selector x y heq).
  - right. left.
    exact (skolemHull_rawLt_of_ambient M seed selectorRank selector
      hselector hLtRank x y hlt).
  - right. right.
    exact (skolemHull_rawLt_of_ambient M seed selectorRank selector
      hselector hLtRank y x hgt).
Qed.

(** Exact beta-entry transport for hull-resident parameters.  This is an
    elementarity statement for one fixed formula, not an appeal to PA in the
    hull. *)
Lemma skolemHull_rawBetaEntry_iff_ambient : forall
    (M : RawPAModel) (seed : M) selectorRank selector,
  SelectorWitnesses M selector ->
  formula_rank hullBetaFormula <= selectorRank ->
  forall (out code step idx :
      skolemHullRawModel M seed selectorRank selector),
    RawBetaEntry (skolemHullRawModel M seed selectorRank selector)
      out code step idx <->
    RawBetaEntry M
      (skolemHullVal M seed selectorRank selector out)
      (skolemHullVal M seed selectorRank selector code)
      (skolemHullVal M seed selectorRank selector step)
      (skolemHullVal M seed selectorRank selector idx).
Proof.
  intros M seed selectorRank selector hselector hBetaRank
    out code step idx.
  set (K := skolemHullRawModel M seed selectorRank selector).
  set (tail := fun _ : nat => raw_zero K).
  set (e := scons K out
    (scons K code (scons K step (scons K idx tail)))).
  pose proof (skolemHull_formula_elementary
    M seed selectorRank selector
    (formula_rank hullBetaFormula) hullBetaFormula
    hselector (Nat.le_refl _) hBetaRank e) as helem.
  change
    (raw_formula_sat K e
      (PA.Formula.betaTermTermAt
        (PA.tVar 0) (PA.tVar 1) (PA.tVar 2) (PA.tVar 3)) <->
     raw_formula_sat M
      (fun n => skolemHullVal M seed selectorRank selector (e n))
      (PA.Formula.betaTermTermAt
        (PA.tVar 0) (PA.tVar 1) (PA.tVar 2) (PA.tVar 3))) in helem.
  rewrite (raw_sat_betaTermTermAt_iff K
    (PA.tVar 0) (PA.tVar 1) (PA.tVar 2) (PA.tVar 3) e) in helem.
  rewrite (raw_sat_betaTermTermAt_iff M
    (PA.tVar 0) (PA.tVar 1) (PA.tVar 2) (PA.tVar 3)
    (fun n => skolemHullVal M seed selectorRank selector (e n))) in helem.
  cbn [raw_term_eval e scons] in helem.
  exact helem.
Qed.

Lemma skolemHull_rawBetaEntry_functional : forall
    (M : RawPAModel) (seed : M) selectorRank selector,
  SelectorWitnesses M selector ->
  formula_rank hullBetaFormula <= selectorRank ->
  RawPASatisfies M ->
  forall (x y code step idx :
      skolemHullRawModel M seed selectorRank selector),
    RawBetaEntry (skolemHullRawModel M seed selectorRank selector)
      x code step idx ->
    RawBetaEntry (skolemHullRawModel M seed selectorRank selector)
      y code step idx ->
    x = y.
Proof.
  intros M seed selectorRank selector hselector hBetaRank hPA
    x y code step idx hx hy.
  apply (skolemHullVal_injective M seed selectorRank selector).
  apply (rawBetaEntry_functional M hPA
    (skolemHullVal M seed selectorRank selector x)
    (skolemHullVal M seed selectorRank selector y)
    (skolemHullVal M seed selectorRank selector code)
    (skolemHullVal M seed selectorRank selector step)
    (skolemHullVal M seed selectorRank selector idx)).
  - apply (proj1 (skolemHull_rawBetaEntry_iff_ambient
      M seed selectorRank selector hselector hBetaRank x code step idx)).
    exact hx.
  - apply (proj1 (skolemHull_rawBetaEntry_iff_ambient
      M seed selectorRank selector hselector hBetaRank y code step idx)).
    exact hy.
Qed.

Lemma skolemHull_canonicalSelectorFormula_functional : forall
    (M : RawPAModel) (seed : M) selectorRank selector,
  SelectorWitnesses M selector ->
  formula_rank hullLtFormula <= selectorRank ->
  RawLtTrichotomy M ->
  forall body env
    (x y : skolemHullRawModel M seed selectorRank selector),
    raw_formula_sat (skolemHullRawModel M seed selectorRank selector)
      (scons _ x env) (canonicalSelectorFormula body) ->
    raw_formula_sat (skolemHullRawModel M seed selectorRank selector)
      (scons _ y env) (canonicalSelectorFormula body) ->
    x = y.
Proof.
  intros M seed selectorRank selector hselector hLtRank htri
    body env x y hx hy.
  apply (rawCanonicalSelectorGraph_functional
    (skolemHullRawModel M seed selectorRank selector)
    (skolemHull_raw_order_trichotomy_of_ambient
      M seed selectorRank selector hselector hLtRank htri)
    body env x y).
  - apply (proj1 (raw_canonicalSelectorFormula _ body env x)). exact hx.
  - apply (proj1 (raw_canonicalSelectorFormula _ body env y)). exact hy.
Qed.

Lemma skolemHull_formula_elementary_scons : forall
    (M : RawPAModel) (seed : M) selectorRank selector,
  SelectorWitnesses M selector ->
  forall body,
  formula_rank body <= selectorRank ->
  forall (env : nat -> skolemHullRawModel M seed selectorRank selector)
    (out : skolemHullRawModel M seed selectorRank selector),
    raw_formula_sat (skolemHullRawModel M seed selectorRank selector)
      (scons _ out env) body <->
    raw_formula_sat M
      (scons M (skolemHullVal M seed selectorRank selector out)
        (fun n => skolemHullVal M seed selectorRank selector (env n)))
      body.
Proof.
  intros M seed selectorRank selector hselector body hBodyRank env out.
  eapply iff_trans.
  - apply (skolemHull_formula_elementary
      M seed selectorRank selector (formula_rank body) body
      hselector (Nat.le_refl _) hBodyRank (scons _ out env)).
  - apply raw_formula_sat_ext.
    intros [|n]; reflexivity.
Qed.

(** Transport only the body truth and strict-order witnesses of an ambient
    canonical-selector graph.  The larger selector formula itself need not
    lie below the hull's elementarity rank. *)
Lemma skolemHull_canonicalSelectorFormula_of_ambient_graph : forall
    (M : RawPAModel) (seed : M) selectorRank selector,
  SelectorWitnesses M selector ->
  formula_rank hullLtFormula <= selectorRank ->
  forall body,
  formula_rank body <= selectorRank ->
  forall (env : nat -> skolemHullRawModel M seed selectorRank selector)
    (out : skolemHullRawModel M seed selectorRank selector),
  rawCanonicalSelectorGraph M body
    (fun n => skolemHullVal M seed selectorRank selector (env n))
    (skolemHullVal M seed selectorRank selector out) ->
  raw_formula_sat (skolemHullRawModel M seed selectorRank selector)
    (scons _ out env) (canonicalSelectorFormula body).
Proof.
  intros M seed selectorRank selector hselector hLtRank
    body hBodyRank env out hgraph.
  apply (proj2 (raw_canonicalSelectorFormula
    (skolemHullRawModel M seed selectorRank selector) body env out)).
  destruct hgraph as [[hbody hminimal] | [hnone hzero]].
  - left. split.
    + apply (proj2 (skolemHull_formula_elementary_scons
        M seed selectorRank selector hselector body hBodyRank env out)).
      exact hbody.
    + intros y hy hybody.
      apply (hminimal
        (skolemHullVal M seed selectorRank selector y)).
      * exact (skolemHull_rawLt_to_ambient
          M seed selectorRank selector y out hy).
      * apply (proj1 (skolemHull_formula_elementary_scons
          M seed selectorRank selector hselector body hBodyRank env y)).
        exact hybody.
  - right. split.
    + intros [y hy]. apply hnone.
      exists (skolemHullVal M seed selectorRank selector y).
      apply (proj1 (skolemHull_formula_elementary_scons
        M seed selectorRank selector hselector body hBodyRank env y)).
      exact hy.
    + apply (skolemHullVal_injective M seed selectorRank selector).
      rewrite skolemHullVal_zero.
      exact hzero.
Qed.

Corollary skolemHull_canonicalSelectorFormula_of_rawCanonicalSelector :
  forall (M : RawPAModel) (seed : M) selectorRank selector,
  SelectorWitnesses M selector ->
  RawPASatisfies M ->
  formula_rank hullLtFormula <= selectorRank ->
  forall body,
  formula_rank body <= selectorRank ->
  forall (env : nat -> skolemHullRawModel M seed selectorRank selector)
    (out : skolemHullRawModel M seed selectorRank selector),
  skolemHullVal M seed selectorRank selector out =
    rawCanonicalSelector M body
      (fun n => skolemHullVal M seed selectorRank selector (env n)) ->
  raw_formula_sat (skolemHullRawModel M seed selectorRank selector)
    (scons _ out env) (canonicalSelectorFormula body).
Proof.
  intros M seed selectorRank selector hselector hPA hLtRank
    body hBodyRank env out hout.
  apply (skolemHull_canonicalSelectorFormula_of_ambient_graph
    M seed selectorRank selector hselector hLtRank body hBodyRank env out).
  rewrite hout.
  apply rawCanonicalSelector_graph.
  exact (raw_definable_least_number_of_pa M hPA).
Qed.

(** Concrete hull representatives for ambient Skolem programs and their
    linked argument lists. *)
Definition skolemHullProgramValue (M : RawPAModel) (seed : M)
    selectorRank selector (p : SkolemProgram) :
    skolemHullRawModel M seed selectorRank selector :=
  exist _ (skolemProgramEval M seed selectorRank selector p)
    (ex_intro _ p eq_refl).

Lemma skolemHullProgramValue_val : forall
    (M : RawPAModel) (seed : M) selectorRank selector p,
  skolemHullVal M seed selectorRank selector
    (skolemHullProgramValue M seed selectorRank selector p) =
  skolemProgramEval M seed selectorRank selector p.
Proof. reflexivity. Qed.

Lemma skolemHullProgramValue_seed : forall
    (M : RawPAModel) (seed : M) selectorRank selector,
  skolemHullProgramValue M seed selectorRank selector spSeed =
  skolemHullSeed M seed selectorRank selector.
Proof.
  intros. apply skolemHullVal_injective. reflexivity.
Qed.

Lemma skolemHullProgramValue_zero : forall
    (M : RawPAModel) (seed : M) selectorRank selector,
  skolemHullProgramValue M seed selectorRank selector spZero =
  raw_zero (skolemHullRawModel M seed selectorRank selector).
Proof.
  intros. apply skolemHullVal_injective. reflexivity.
Qed.

Lemma skolemHullProgramValue_succ : forall
    (M : RawPAModel) (seed : M) selectorRank selector p,
  skolemHullProgramValue M seed selectorRank selector (spSucc p) =
  raw_succ (skolemHullRawModel M seed selectorRank selector)
    (skolemHullProgramValue M seed selectorRank selector p).
Proof.
  intros. apply skolemHullVal_injective. reflexivity.
Qed.

Lemma skolemHullProgramValue_add : forall
    (M : RawPAModel) (seed : M) selectorRank selector p q,
  skolemHullProgramValue M seed selectorRank selector (spAdd p q) =
  raw_add (skolemHullRawModel M seed selectorRank selector)
    (skolemHullProgramValue M seed selectorRank selector p)
    (skolemHullProgramValue M seed selectorRank selector q).
Proof.
  intros. apply skolemHullVal_injective. reflexivity.
Qed.

Lemma skolemHullProgramValue_mul : forall
    (M : RawPAModel) (seed : M) selectorRank selector p q,
  skolemHullProgramValue M seed selectorRank selector (spMul p q) =
  raw_mul (skolemHullRawModel M seed selectorRank selector)
    (skolemHullProgramValue M seed selectorRank selector p)
    (skolemHullProgramValue M seed selectorRank selector q).
Proof.
  intros. apply skolemHullVal_injective. reflexivity.
Qed.

Fixpoint skolemHullProgramArgsEnv (M : RawPAModel) (seed : M)
    selectorRank selector (args : SkolemProgramArgs) (n : nat) :
    skolemHullRawModel M seed selectorRank selector :=
  match args, n with
  | spaNil, _ => skolemHullProgramValue M seed selectorRank selector spZero
  | spaCons p _, 0 =>
      skolemHullProgramValue M seed selectorRank selector p
  | spaCons _ rest, S k =>
      skolemHullProgramArgsEnv M seed selectorRank selector rest k
  end.

Lemma skolemHullProgramArgsEnv_val : forall
    (M : RawPAModel) (seed : M) selectorRank selector args n,
  skolemHullVal M seed selectorRank selector
    (skolemHullProgramArgsEnv M seed selectorRank selector args n) =
  skolemProgramArgsEval M seed selectorRank selector args n.
Proof.
  intros M seed selectorRank selector args.
  induction args as [|p rest IH]; intros [|n]; simpl; try reflexivity.
  apply IH.
Qed.

(** A chooser program at the hull's own syntax rank satisfies the exact
    canonical-selector branch used by the fixed trace evaluator. *)
Corollary skolemHullProgramValue_choose_graph : forall
    (M : RawPAModel) (seed : M) rank,
  RawPASatisfies M ->
  formula_rank hullLtFormula <= rank ->
  forall i args,
  formula_rank (selectorBody rank i) <= rank ->
  raw_formula_sat
    (skolemHullRawModel M seed rank (rawCanonicalSelector M))
    (scons _
      (skolemHullProgramValue M seed rank (rawCanonicalSelector M)
        (spChoose i args))
      (skolemHullProgramArgsEnv M seed rank
        (rawCanonicalSelector M) args))
    (canonicalSelectorFormula (selectorBody rank i)).
Proof.
  intros M seed rank hPA hLtRank i args hBodyRank.
  apply (skolemHull_canonicalSelectorFormula_of_rawCanonicalSelector
    M seed rank (rawCanonicalSelector M)).
  - apply rawCanonicalSelector_witnesses.
    exact (raw_definable_least_number_of_pa M hPA).
  - exact hPA.
  - exact hLtRank.
  - exact hBodyRank.
  - rewrite skolemHullProgramValue_val.
    cbn [skolemProgramEval].
    f_equal.
    apply functional_extensionality. intro n.
    symmetry. apply skolemHullProgramArgsEnv_val.
Qed.

(** The six ambient PA/order facts used by the cut transport to the bounded
    Skolem hull without assuming that the hull itself is a PA model. *)
Section HullContract.

Context (M : RawPAModel) (seed : M) (selectorRank : nat)
  (selector : PA.formula -> (nat -> M) -> M).

Let K : RawPAModel :=
  skolemHullRawModel M seed selectorRank selector.
Let seedK : K := skolemHullSeed M seed selectorRank selector.

Variable hselector : SelectorWitnesses M selector.
Variable hPA : RawPASatisfies M.
Variable hLtRank : formula_rank hullLtFormula <= selectorRank.
Variable hseedAbove : AboveAllNumerals M seed.
Variable evalFormula : PA.formula.

Variable hTotal : forall output : K, exists code : nat,
  Evaluates K evalFormula seedK (rawNumeralValue K code) output.
Variable hFunctional : forall (code : nat) (x y : K),
  Evaluates K evalFormula seedK (rawNumeralValue K code) x ->
  Evaluates K evalFormula seedK (rawNumeralValue K code) y ->
  x = y.

Theorem skolemHull_evaluator_contract_of_ambient_pa :
  EvaluatorContract K evalFormula seedK.
Proof.
  refine {| contract_standard_code_total := hTotal;
            contract_standard_code_functional := hFunctional |}.
  - intros m n hmn.
    apply (rawNumeralValue_injective M hPA m n).
    apply (f_equal (skolemHullVal M seed selectorRank selector)) in hmn.
    rewrite !skolemHull_rawNumeralValue_val in hmn.
    exact hmn.
  - intros x bound hlt.
    pose proof (skolemHull_rawLt_to_ambient M seed selectorRank selector
      x (rawNumeralValue K bound) hlt) as hambient.
    rewrite skolemHull_rawNumeralValue_val in hambient.
    destruct (raw_lt_numeralValue_cases M hPA
      (skolemHullVal M seed selectorRank selector x) bound hambient)
      as [n [hn hx]].
    exists n. split; [exact hn |].
    apply (skolemHullVal_injective M seed selectorRank selector).
    rewrite skolemHull_rawNumeralValue_val.
    exact hx.
  - intro x.
    destruct (raw_standard_or_above M hPA
      (skolemHullVal M seed selectorRank selector x))
      as [[n hx] | habove].
    + left. exists n.
      apply (skolemHullVal_injective M seed selectorRank selector).
      rewrite skolemHull_rawNumeralValue_val.
      exact hx.
    + right. intro n.
      apply (skolemHull_rawLt_of_ambient M seed selectorRank selector
        hselector hLtRank).
      rewrite skolemHull_rawNumeralValue_val.
      exact (habove n).
  - intro n.
    apply (skolemHull_rawLt_of_ambient M seed selectorRank selector
      hselector hLtRank).
    rewrite skolemHull_rawNumeralValue_val.
    exact (hseedAbove n).
Qed.

End HullContract.

(** Under the two binders of [coverAt], substitute output [#1], code [#0],
    and seed [#3] into the evaluator formula. *)
Definition evalInCoverSubst (i : nat) : PA.term :=
  match i with
  | 0 => PA.tVar 1
  | 1 => PA.tVar 0
  | 2 => PA.tVar 3
  | _ => PA.tZero
  end.

Definition coverAt (evalFormula : PA.formula) : PA.formula :=
  PA.pAll (PA.pEx (PA.pAnd
    (PA.Formula.ltTermAt (PA.tVar 0) (PA.tVar 2))
    (PA.Formula.subst evalInCoverSubst evalFormula))).

Definition cutAt (evalFormula : PA.formula) : PA.formula :=
  PA.pImp (coverAt evalFormula) PA.pBot.

Definition Covers (M : RawPAModel) (evalFormula : PA.formula)
    (seed bound : M) : Prop :=
  forall output : M, exists code : M,
    rawLt M code bound /\ Evaluates M evalFormula seed code output.

Lemma raw_sat_evalInCoverSubst : forall (M : RawPAModel)
    evalFormula seed bound output code tail,
  raw_formula_sat M
    (scons M code
      (scons M output (scons M bound (scons M seed tail))))
    (PA.Formula.subst evalInCoverSubst evalFormula) <->
  Evaluates M evalFormula seed code output.
Proof.
  intros M evalFormula seed bound output code tail.
  unfold Evaluates.
  rewrite raw_formula_sat_subst.
  apply raw_formula_sat_ext.
  intros [|[|[|i]]]; reflexivity.
Qed.

Lemma raw_sat_coverAt_iff : forall (M : RawPAModel)
    evalFormula seed bound tail,
  raw_formula_sat M (scons M bound (scons M seed tail))
    (coverAt evalFormula) <->
  Covers M evalFormula seed bound.
Proof.
  intros M evalFormula seed bound tail.
  unfold coverAt, Covers.
  cbn [raw_formula_sat].
  split.
  - intros hall output.
    destruct (hall output) as [code [hlt heval]].
    exists code. split.
    + apply (proj1 (raw_sat_ltTermAt_iff M _ _ _)) in hlt.
      cbn [raw_term_eval scons] in hlt. exact hlt.
    + apply (proj1 (raw_sat_evalInCoverSubst
        M evalFormula seed bound output code tail)).
      exact heval.
  - intros hcover output.
    destruct (hcover output) as [code [hlt heval]].
    exists code. split.
    + apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      cbn [raw_term_eval scons]. exact hlt.
    + apply (proj2 (raw_sat_evalInCoverSubst
        M evalFormula seed bound output code tail)).
      exact heval.
Qed.

Lemma raw_sat_cutAt_iff : forall (M : RawPAModel)
    evalFormula seed bound tail,
  raw_formula_sat M (scons M bound (scons M seed tail))
    (cutAt evalFormula) <->
  ~ Covers M evalFormula seed bound.
Proof.
  intros M evalFormula seed bound tail.
  unfold cutAt. cbn [raw_formula_sat].
  rewrite raw_sat_coverAt_iff. tauto.
Qed.

(** A small list form of finite pigeonhole, parameterized by injectivity only
    on the displayed finite domain. *)
Lemma NoDup_map_of_injective_on : forall (A B : Type)
    (f : A -> B) (xs : list A),
  NoDup xs ->
  (forall x y, In x xs -> In y xs -> f x = f y -> x = y) ->
  NoDup (map f xs).
Proof.
  intros A B f xs hnodup.
  induction hnodup as [|x xs hx hxs IH]; intro hinjective; simpl.
  - constructor.
  - constructor.
    + intro hmem.
      apply in_map_iff in hmem.
      destruct hmem as [y [heq hy]].
      apply hx.
      assert (hxy : x = y).
      {
        apply hinjective.
        - now left.
        - now right.
        - symmetry. exact heq.
      }
      now subst y.
    + apply IH.
      intros y z hy hz heq.
      apply hinjective; try (now right); exact heq.
Qed.

Lemma covers_of_above_all_numerals : forall (M : RawPAModel)
    evalFormula seed bound,
  EvaluatorContract M evalFormula seed ->
  AboveAllNumerals M bound ->
  Covers M evalFormula seed bound.
Proof.
  intros M evalFormula seed bound hcontract habove output.
  destruct (contract_standard_code_total M evalFormula seed hcontract output)
    as [code heval].
  exists (rawNumeralValue M code). split.
  - exact (habove code).
  - exact heval.
Qed.

(** No standard numeral bound covers the carrier.  Otherwise the first
    [S bound] standard outputs would inject into its [bound] possible
    standard predecessor codes. *)
Theorem not_covers_numeral : forall (M : RawPAModel)
    evalFormula seed,
  EvaluatorContract M evalFormula seed ->
  forall bound,
    ~ Covers M evalFormula seed (rawNumeralValue M bound).
Proof.
  intros M evalFormula seed hcontract bound hcover.
  assert (hex : forall i : nat, exists code : nat,
      i <= bound ->
      code < bound /\
      Evaluates M evalFormula seed (rawNumeralValue M code)
        (rawNumeralValue M i)).
  {
    intro i.
    destruct (le_dec i bound) as [hi | hi].
    - destruct (hcover (rawNumeralValue M i))
        as [codeValue [hlt heval]].
      destruct (contract_lt_numeral M evalFormula seed hcontract
          codeValue bound hlt) as [code [hcodeLt hcodeValue]].
      exists code. intros _.
      split.
      + exact hcodeLt.
      + rewrite <- hcodeValue. exact heval.
    - exists 0. intro hle. contradiction.
  }
  destruct (@choice nat nat
      (fun i code => i <= bound ->
        code < bound /\
        Evaluates M evalFormula seed (rawNumeralValue M code)
          (rawNumeralValue M i)) hex) as [codeOf hcodeOf].
  set (domain := seq 0 (S bound)).
  assert (hdomain : NoDup domain).
  { unfold domain. apply seq_NoDup. }
  assert (hcodeInjective : forall i j,
      In i domain -> In j domain -> codeOf i = codeOf j -> i = j).
  {
    intros i j hi hj hcode.
    assert (hibound : i <= bound).
    { unfold domain in hi. apply in_seq in hi. lia. }
    assert (hjbound : j <= bound).
    { unfold domain in hj. apply in_seq in hj. lia. }
    destruct (hcodeOf i hibound) as [hiCode hiEval].
    destruct (hcodeOf j hjbound) as [hjCode hjEval].
    assert (houtputs : rawNumeralValue M i = rawNumeralValue M j).
    {
      apply (contract_standard_code_functional M evalFormula seed
        hcontract (codeOf i)).
      - exact hiEval.
      - rewrite hcode. exact hjEval.
    }
    exact (contract_numeral_injective M evalFormula seed hcontract
      i j houtputs).
  }
  assert (hmapNoDup : NoDup (map codeOf domain)).
  {
    apply NoDup_map_of_injective_on.
    - exact hdomain.
    - exact hcodeInjective.
  }
  assert (hincl : incl (map codeOf domain) (seq 0 bound)).
  {
    intros code hcode.
    apply in_map_iff in hcode.
    destruct hcode as [i [hcode hi]]. subst code.
    apply in_seq.
    assert (hibound : i <= bound).
    { unfold domain in hi. apply in_seq in hi. lia. }
    destruct (hcodeOf i hibound) as [hlt _]. lia.
  }
  pose proof (NoDup_incl_length hmapNoDup hincl) as hlength.
  unfold domain in hlength.
  rewrite length_map, !length_seq in hlength.
  lia.
Qed.

(** The internally definable cut contains exactly the externally standard
    elements of the carrier. *)
Theorem raw_sat_cutAt_iff_standard : forall (M : RawPAModel)
    evalFormula seed,
  EvaluatorContract M evalFormula seed ->
  forall tail x,
    raw_formula_sat M (scons M x (scons M seed tail))
      (cutAt evalFormula) <->
    IsStandard M x.
Proof.
  intros M evalFormula seed hcontract tail x.
  rewrite raw_sat_cutAt_iff.
  split.
  - intro hnotcover.
    destruct (contract_standard_or_above M evalFormula seed hcontract x)
      as [hstandard | habove].
    + exact hstandard.
    + exfalso. apply hnotcover.
      exact (covers_of_above_all_numerals M evalFormula seed x
        hcontract habove).
  - intros [n hx]. subst x.
    exact (not_covers_numeral M evalFormula seed hcontract n).
Qed.

Lemma raw_sat_cutAt_zero : forall (M : RawPAModel)
    evalFormula seed,
  EvaluatorContract M evalFormula seed ->
  forall tail,
    raw_formula_sat M
      (scons M (raw_zero M) (scons M seed tail))
      (cutAt evalFormula).
Proof.
  intros M evalFormula seed hcontract tail.
  apply (proj2 (raw_sat_cutAt_iff_standard
    M evalFormula seed hcontract tail (raw_zero M))).
  exists 0. reflexivity.
Qed.

Lemma raw_sat_cutAt_succ : forall (M : RawPAModel)
    evalFormula seed,
  EvaluatorContract M evalFormula seed ->
  forall tail x,
    raw_formula_sat M (scons M x (scons M seed tail))
      (cutAt evalFormula) ->
    raw_formula_sat M
      (scons M (raw_succ M x) (scons M seed tail))
      (cutAt evalFormula).
Proof.
  intros M evalFormula seed hcontract tail x hx.
  apply (proj2 (raw_sat_cutAt_iff_standard
    M evalFormula seed hcontract tail (raw_succ M x))).
  apply (proj1 (raw_sat_cutAt_iff_standard
    M evalFormula seed hcontract tail x)) in hx.
  destruct hx as [n hx]. subst x.
  exists (S n). reflexivity.
Qed.

Lemma raw_not_sat_cutAt_seed : forall (M : RawPAModel)
    evalFormula seed,
  EvaluatorContract M evalFormula seed ->
  forall tail,
    ~ raw_formula_sat M (scons M seed (scons M seed tail))
      (cutAt evalFormula).
Proof.
  intros M evalFormula seed hcontract tail hcut.
  apply (proj1 (raw_sat_cutAt_iff
    M evalFormula seed seed tail)) in hcut.
  apply hcut.
  exact (covers_of_above_all_numerals M evalFormula seed seed
    hcontract
    (contract_seed_above M evalFormula seed hcontract)).
Qed.

(** Zero lies in the cut, the cut is successor closed, and the distinguished
    seed lies outside it; hence its unsealed induction instance is false. *)
Theorem raw_not_sat_cutAt_induction : forall (M : RawPAModel)
    evalFormula seed,
  EvaluatorContract M evalFormula seed ->
  forall tail,
    ~ raw_formula_sat M (scons M seed tail)
      (PA.Formula.inductionForm (cutAt evalFormula)).
Proof.
  intros M evalFormula seed hcontract tail hind.
  assert (hantecedent :
      raw_formula_sat M (scons M seed tail)
        (PA.pAnd
          (PA.Formula.subst PA.Formula.substZero (cutAt evalFormula))
          (PA.pAll
            (PA.pImp (cutAt evalFormula)
              (PA.Formula.subst PA.Formula.substSuccVar
                (cutAt evalFormula)))))).
  {
    split.
    - apply (proj2 (raw_sat_substZero M
        (cutAt evalFormula) (scons M seed tail))).
      exact (raw_sat_cutAt_zero M evalFormula seed hcontract tail).
    - intros x hx.
      apply (proj2 (raw_sat_substSuccVar M
        (cutAt evalFormula) (scons M seed tail) x)).
      exact (raw_sat_cutAt_succ M evalFormula seed hcontract tail x hx).
  }
  unfold PA.Formula.inductionForm in hind.
  cbn [raw_formula_sat] in hind.
  specialize (hind hantecedent seed).
  exact (raw_not_sat_cutAt_seed M evalFormula seed hcontract tail hind).
Qed.

(** The genuine sealed PA induction axiom for the cut is false. *)
Theorem raw_not_sat_sealed_cutAt_induction : forall (M : RawPAModel)
    evalFormula seed,
  EvaluatorContract M evalFormula seed ->
  forall e,
    ~ raw_formula_sat M e
      (PA.Formula.sealPA
        (PA.Formula.inductionForm (cutAt evalFormula))).
Proof.
  intros M evalFormula seed hcontract e hsealed.
  set (induction := PA.Formula.inductionForm (cutAt evalFormula)).
  assert (hallSealed : forall e' : nat -> M,
      raw_formula_sat M e' (PA.Formula.sealPA induction)).
  {
    intro e'.
    assert (henv : forall n,
        PA.Formula.Free n (PA.Formula.sealPA induction) -> e n = e' n).
    {
      intros n hfree.
      exfalso.
      exact (PA.Formula.sealPA_sentence induction n hfree).
    }
    apply (proj1 (raw_formula_sat_ext_free M
      (PA.Formula.sealPA induction) e e' henv)).
    exact hsealed.
  }
  pose proof (raw_sealPA_valid_inv M induction hallSealed
    (scons M seed (fun _ => raw_zero M))) as hind.
  exact (raw_not_sat_cutAt_induction M evalFormula seed hcontract
    (fun _ => raw_zero M) hind).
Qed.

Lemma sealed_cutAt_induction_is_PA_axiom : forall evalFormula,
  PA.Formula.Ax_s
    (PA.Formula.sealPA
      (PA.Formula.inductionForm (cutAt evalFormula))).
Proof.
  intro evalFormula.
  exact (PA.Formula.Ax_s_induction (cutAt evalFormula)).
Qed.

(** The remaining trace-realization boundary: one contract countermodel for
    every canonical syntax-rank fragment. *)
Definition ContractCountermodels : Prop :=
  forall n : nat,
    exists (M : RawPAModel) (evalFormula : PA.formula) (seed : M),
      EvaluatorContract M evalFormula seed /\
      RawModelSatisfies M (PARankFragment n).

Theorem rank_fragment_raw_countermodels_of_contracts :
  ContractCountermodels -> PARankFragmentRawCountermodelStrictness.
Proof.
  intros hmodels n.
  destruct (hmodels n) as
    [M [evalFormula [seed [hcontract hfragment]]]].
  exists M, (cutAt evalFormula). split.
  - exact hfragment.
  - unfold RawModelFalsifies.
    exists (fun _ => raw_zero M).
    exact (raw_not_sat_sealed_cutAt_induction
      M evalFormula seed hcontract (fun _ => raw_zero M)).
Qed.

Theorem peano_arithmetic_not_finitely_axiomatizable_of_contracts :
  ContractCountermodels ->
  ~ DeductivelyFinitelyAxiomatizable PA.Formula.Ax_s.
Proof.
  intro hmodels.
  apply peano_arithmetic_not_finitely_axiomatizable_of_rank_fragment_strictness.
  apply rank_fragment_strictness_of_raw_countermodels.
  exact (rank_fragment_raw_countermodels_of_contracts hmodels).
Qed.

End PAEvaluatorCutContract.
