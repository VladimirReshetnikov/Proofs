(**
  A fixed first-order beta-table evaluator for finite Skolem programs.

  The formula below never interprets a Goedel code for PA syntax.  Its only
  selector dispatch is the externally finite list [formula_rank_enum rank].
  Every recursive row contains, in addition to the child lookup, an explicit
  assertion that the child code is strictly smaller than the parent code.
  Consequently the semantic recursion is well founded directly on the
  standard polynomial program code.
*)

From Stdlib Require Import List Arith Lia Bool
  Logic.FunctionalExtensionality.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction
  FiniteSkolemHull CanonicalSelector CanonicalSelectorPA
  SkolemProgramCode FiniteBetaCoding.

Import ListNotations.
Import PAHierarchyReduction.
Import PAFiniteSkolemHull.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PASkolemProgramCode.
Import PAFiniteBetaCoding.

Module PAProgramTrace.

(** Object-language counterparts of the external polynomial coding. *)
Definition pairTerm (a b : PA.term) : PA.term :=
  PA.tAdd (PA.tMul (PA.tAdd a b) (PA.tAdd a b)) a.

Definition nodeTerm (tag payload : PA.term) : PA.term :=
  PA.tSucc (pairTerm tag payload).

Lemma raw_term_eval_pairTerm : forall (M : RawPAModel)
    (e : nat -> M) a b,
  raw_term_eval M e (pairTerm a b) =
  raw_add M
    (raw_mul M
      (raw_add M (raw_term_eval M e a) (raw_term_eval M e b))
      (raw_add M (raw_term_eval M e a) (raw_term_eval M e b)))
    (raw_term_eval M e a).
Proof. reflexivity. Qed.

Lemma raw_term_eval_nodeTerm : forall (M : RawPAModel)
    (e : nat -> M) tag payload,
  raw_term_eval M e (nodeTerm tag payload) =
  raw_succ M
    (raw_add M
      (raw_mul M
        (raw_add M (raw_term_eval M e tag)
          (raw_term_eval M e payload))
        (raw_add M (raw_term_eval M e tag)
          (raw_term_eval M e payload)))
      (raw_term_eval M e tag)).
Proof. reflexivity. Qed.

(** Finite logical folds and simultaneous witness blocks. *)
Fixpoint conjunction (fs : list PA.formula) : PA.formula :=
  match fs with
  | [] => PA.pEq PA.tZero PA.tZero
  | f :: rest => PA.pAnd f (conjunction rest)
  end.

Fixpoint disjunction (fs : list PA.formula) : PA.formula :=
  match fs with
  | [] => PA.pBot
  | f :: rest => PA.pOr f (disjunction rest)
  end.

Fixpoint existsN (n : nat) (f : PA.formula) : PA.formula :=
  match n with
  | 0 => f
  | S k => PA.pEx (existsN k f)
  end.

Lemma raw_sat_conjunction : forall (M : RawPAModel)
    (e : nat -> M) fs,
  raw_formula_sat M e (conjunction fs) <->
  forall f, In f fs -> raw_formula_sat M e f.
Proof.
  intros M e fs. induction fs as [|f fs IH]; simpl.
  - split.
    + intros _ f hf. contradiction.
    + intros _. reflexivity.
  - rewrite IH. split.
    + intros [hf hrest] g [hg | hg].
      * now subst g.
      * exact (hrest g hg).
    + intro hall. split.
      * apply (hall f). now left.
      * intros g hg. apply (hall g). now right.
Qed.

Lemma raw_sat_disjunction : forall (M : RawPAModel)
    (e : nat -> M) fs,
  raw_formula_sat M e (disjunction fs) <->
  exists f, In f fs /\ raw_formula_sat M e f.
Proof.
  intros M e fs. induction fs as [|f fs IH]; simpl.
  - split; [contradiction | intros [g [[] _]]].
  - rewrite IH. split.
    + intros [hf | hrest].
      * exists f. split; [now left | exact hf].
      * destruct hrest as [g [hg hsat]].
        exists g. split; [now right | exact hsat].
    + intros [g [[hg | hg] hsat]].
      * left. now subst g.
      * right. exists g. split; assumption.
Qed.

(** The first [n] variables are simultaneous witness slots; [slots] is a
    total function only to avoid dependent-vector bookkeeping. *)
Definition slotEnv (M : RawPAModel) (n : nat)
    (slots e : nat -> M) (i : nat) : M :=
  if i <? n then slots i else e (i - n).

Lemma slotEnv_of_lt : forall (M : RawPAModel) n slots e i,
  i < n -> slotEnv M n slots e i = slots i.
Proof.
  intros M n slots e i hi. unfold slotEnv.
  assert (h : (i <? n) = true) by (apply Nat.ltb_lt; exact hi).
  now rewrite h.
Qed.

Lemma slotEnv_of_ge : forall (M : RawPAModel) n slots e i,
  n <= i -> slotEnv M n slots e i = e (i - n).
Proof.
  intros M n slots e i hi. unfold slotEnv.
  assert (h : (i <? n) = false) by (apply Nat.ltb_ge; exact hi).
  now rewrite h.
Qed.

Lemma slotEnv_succ : forall (M : RawPAModel) n slots e,
  slotEnv M n slots (scons M (slots n) e) =
  slotEnv M (S n) slots e.
Proof.
  intros M n slots e. apply functional_extensionality. intro i.
  destruct (Nat.lt_trichotomy i n) as [hlt | [heq | hgt]].
  - rewrite !slotEnv_of_lt by lia. reflexivity.
  - subst i.
    rewrite slotEnv_of_ge by lia.
    rewrite slotEnv_of_lt by lia.
    rewrite Nat.sub_diag. reflexivity.
  - rewrite !slotEnv_of_ge by lia.
    replace (i - n) with (S (i - S n)) by lia.
    reflexivity.
Qed.

Lemma raw_sat_existsN_of_slots : forall (M : RawPAModel) n f slots e,
  raw_formula_sat M (slotEnv M n slots e) f ->
  raw_formula_sat M e (existsN n f).
Proof.
  intros M n. induction n as [|n IH]; intros f slots e h.
  - simpl in *.
    apply (proj1 (raw_formula_sat_ext M f
      (slotEnv M 0 slots e) e
      (fun i => eq_trans (slotEnv_of_ge M 0 slots e i (Nat.le_0_l i))
        (f_equal e (Nat.sub_0_r i))))).
    exact h.
  - simpl. exists (slots n).
    apply (IH f slots (scons M (slots n) e)).
    rewrite slotEnv_succ. exact h.
Qed.

(** Semantic inversion for a simultaneous witness block.  Slots are kept as
    a total function; only the first [n] entries are observed. *)
Lemma raw_sat_existsN_iff_slots : forall (M : RawPAModel) n f e,
  raw_formula_sat M e (existsN n f) <->
  exists slots : nat -> M,
    raw_formula_sat M (slotEnv M n slots e) f.
Proof.
  intros M n. induction n as [|n IH]; intros f e.
  - simpl. split; intro h.
    + exists (fun _ => raw_zero M).
      apply (proj1 (raw_formula_sat_ext M f e
        (slotEnv M 0 (fun _ => raw_zero M) e)
        (fun i => eq_sym (eq_trans
          (slotEnv_of_ge M 0 (fun _ => raw_zero M) e i (Nat.le_0_l i))
          (f_equal e (Nat.sub_0_r i)))))).
      exact h.
    + destruct h as [slots h].
      apply (proj1 (raw_formula_sat_ext M f
        (slotEnv M 0 slots e) e
        (fun i => eq_trans
          (slotEnv_of_ge M 0 slots e i (Nat.le_0_l i))
          (f_equal e (Nat.sub_0_r i))))).
      exact h.
  - simpl. split.
    + intros [last hlast].
      destruct (proj1 (IH f (scons M last e)) hlast)
        as [slots hslots].
      set (extended := fun i => if i <? n then slots i else last).
      exists extended.
      assert (henv : forall i,
        slotEnv M n slots (scons M last e) i =
        slotEnv M (S n) extended e i).
      { intro i. destruct (Nat.lt_trichotomy i n)
          as [hi | [hi | hi]].
        - rewrite !slotEnv_of_lt by lia.
          unfold extended.
          assert (hb : (i <? n) = true) by (apply Nat.ltb_lt; exact hi).
          now rewrite hb.
        - subst i. rewrite slotEnv_of_ge by lia.
          rewrite slotEnv_of_lt by lia.
          unfold extended.
          assert (hb : (n <? n) = false) by (apply Nat.ltb_ge; lia).
          rewrite hb, Nat.sub_diag. reflexivity.
        - rewrite !slotEnv_of_ge by lia.
          replace (i - n) with (S (i - S n)) by lia.
          reflexivity. }
      apply (proj1 (raw_formula_sat_ext M f
        (slotEnv M n slots (scons M last e))
        (slotEnv M (S n) extended e) henv)).
      exact hslots.
    + intros [slots hslots].
      exact (raw_sat_existsN_of_slots M (S n) f slots e hslots).
Qed.

(** Lift an ambient term across a finite witness block. *)
Definition liftTerm (n : nat) (t : PA.term) : PA.term :=
  PA.Term.rename (fun i => i + n) t.

Lemma raw_term_eval_liftTerm_slotEnv : forall (M : RawPAModel)
    n slots e t,
  raw_term_eval M (slotEnv M n slots e) (liftTerm n t) =
  raw_term_eval M e t.
Proof.
  intros M n slots e t. unfold liftTerm.
  rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro i.
  rewrite slotEnv_of_ge by lia.
  replace (i + n - n) with i by lia. reflexivity.
Qed.

Lemma raw_term_eval_liftTerm_two_scons : forall (M : RawPAModel)
    x y e t,
  raw_term_eval M (scons M x (scons M y e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M x y e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 2) with (S (S i)) by lia. reflexivity.
Qed.

Lemma raw_term_eval_liftTerm_three_scons : forall (M : RawPAModel)
    x y z e t,
  raw_term_eval M (scons M x (scons M y (scons M z e)))
      (liftTerm 3 t) =
  raw_term_eval M e t.
Proof.
  intros M x y z e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 3) with (S (S (S i))) by lia. reflexivity.
Qed.

Lemma raw_term_eval_liftTerm_four_scons : forall (M : RawPAModel)
    w x y z e t,
  raw_term_eval M
      (scons M w (scons M x (scons M y (scons M z e))))
      (liftTerm 4 t) =
  raw_term_eval M e t.
Proof.
  intros M w x y z e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 4) with (S (S (S (S i)))) by lia. reflexivity.
Qed.

Lemma raw_sat_leTermAt_iff : forall (M : RawPAModel)
    (a b : PA.term) (e : nat -> M),
  raw_formula_sat M e (PA.Formula.leTermAt a b) <->
  rawLe M (raw_term_eval M e a) (raw_term_eval M e b).
Proof.
  intros M a b e.
  unfold PA.Formula.leTermAt, rawLe.
  cbn [raw_formula_sat raw_term_eval].
  split.
  - intros [d h]. exists d.
    repeat rewrite raw_term_eval_rename_succ in h.
    cbn [raw_term_eval scons] in h. exact h.
  - intros [d h]. exists d.
    repeat rewrite raw_term_eval_rename_succ.
    cbn [raw_term_eval scons]. exact h.
Qed.

(** In a selector branch slot [2*i] is child [i]'s value and slot
    [2*i+1] is its program code. *)
Definition argumentValueTerm (i : nat) : PA.term := PA.tVar (2 * i).
Definition argumentCodeTerm (i : nat) : PA.term := PA.tVar (2 * i + 1).

Fixpoint argumentSlots {A : Type}
    (values codes : nat -> A) (j : nat) : A :=
  match j with
  | 0 => values 0
  | 1 => codes 0
  | S (S k) =>
      argumentSlots (fun i => values (S i))
        (fun i => codes (S i)) k
  end.

Lemma argumentSlots_value : forall (A : Type)
    (values codes : nat -> A) i,
  argumentSlots values codes (2 * i) = values i.
Proof.
  intros A values codes i. revert values codes.
  induction i as [|i IH]; intros values codes.
  - reflexivity.
  - replace (2 * S i) with (S (S (2 * i))) by lia.
    simpl. apply IH.
Qed.

Lemma argumentSlots_code : forall (A : Type)
    (values codes : nat -> A) i,
  argumentSlots values codes (2 * i + 1) = codes i.
Proof.
  intros A values codes i. revert values codes.
  induction i as [|i IH]; intros values codes.
  - reflexivity.
  - replace (2 * S i + 1) with (S (S (2 * i + 1))) by lia.
    simpl. apply IH.
Qed.

Lemma raw_eval_argumentValueTerm_slots : forall (M : RawPAModel)
    rank values codes e i,
  i < rank ->
  raw_term_eval M
    (slotEnv M (2 * rank) (argumentSlots values codes) e)
    (argumentValueTerm i) = values i.
Proof.
  intros M rank values codes e i hi.
  unfold argumentValueTerm. simpl.
  rewrite slotEnv_of_lt by lia.
  apply argumentSlots_value.
Qed.

Lemma raw_eval_argumentCodeTerm_slots : forall (M : RawPAModel)
    rank values codes e i,
  i < rank ->
  raw_term_eval M
    (slotEnv M (2 * rank) (argumentSlots values codes) e)
    (argumentCodeTerm i) = codes i.
Proof.
  intros M rank values codes e i hi.
  unfold argumentCodeTerm. simpl.
  rewrite slotEnv_of_lt by lia.
  apply argumentSlots_code.
Qed.

(** Fixed-length linked-list argument-code term, assembled from the odd
    child-code slots. *)
Fixpoint argumentVectorTermFrom (start count : nat) : PA.term :=
  match count with
  | 0 => nodeTerm (PA.Term.numeral tagArgsNil) (PA.Term.numeral 0)
  | S k => nodeTerm (PA.Term.numeral tagArgsCons)
      (pairTerm (argumentCodeTerm start)
        (argumentVectorTermFrom (S start) k))
  end.

Definition argumentVectorTerm (rank : nat) : PA.term :=
  argumentVectorTermFrom 0 rank.

Fixpoint argumentVectorOfTermsFrom
    (terms : nat -> PA.term) (start count : nat) : PA.term :=
  match count with
  | 0 => nodeTerm (PA.Term.numeral tagArgsNil) (PA.Term.numeral 0)
  | S k => nodeTerm (PA.Term.numeral tagArgsCons)
      (pairTerm (terms start)
        (argumentVectorOfTermsFrom terms (S start) k))
  end.

Definition argumentVectorOfTerms (rank : nat)
    (terms : nat -> PA.term) : PA.term :=
  argumentVectorOfTermsFrom terms 0 rank.

Lemma raw_eval_argumentVectorTermFrom_slots :
  forall (M : RawPAModel) rank start count values codes e terms,
  start + count <= rank ->
  (forall i, start <= i < start + count ->
    codes i = raw_term_eval M e (terms i)) ->
  raw_term_eval M
      (slotEnv M (2 * rank) (argumentSlots values codes) e)
      (argumentVectorTermFrom start count) =
  raw_term_eval M e
      (argumentVectorOfTermsFrom terms start count).
Proof.
  intros M rank start count. revert start.
  induction count as [|count IH]; intros start values codes e terms
      hrank hcodes.
  - reflexivity.
  - cbn [argumentVectorTermFrom argumentVectorOfTermsFrom].
    repeat rewrite raw_term_eval_nodeTerm.
    repeat rewrite raw_term_eval_pairTerm.
    rewrite (raw_eval_argumentCodeTerm_slots M rank values codes e start)
      by lia.
    rewrite hcodes by lia.
    assert (hrank' : S start + count <= rank) by lia.
    assert (hcodes' : forall i,
        S start <= i < S start + count ->
        codes i = raw_term_eval M e (terms i)).
    { intros i hi. apply hcodes. lia. }
    rewrite (IH (S start) values codes e terms hrank' hcodes').
    reflexivity.
Qed.

Corollary raw_eval_argumentVectorTerm_slots :
  forall (M : RawPAModel) rank values e terms,
  raw_term_eval M
      (slotEnv M (2 * rank)
        (argumentSlots values (fun i => raw_term_eval M e (terms i))) e)
      (argumentVectorTerm rank) =
  raw_term_eval M e (argumentVectorOfTerms rank terms).
Proof.
  intros M rank values e terms.
  apply raw_eval_argumentVectorTermFrom_slots; [lia |].
  intros i _. reflexivity.
Qed.

(** Instantiate a selector graph by an output and a fixed argument vector.
    Irrelevant tail parameters are zero. *)
Definition graphSubst (rank : nat) (out : PA.term)
    (args : nat -> PA.term) (n : nat) : PA.term :=
  match n with
  | 0 => out
  | S i => if i <? rank then args i else PA.tZero
  end.

Definition graphAt (rank : nat) (graph : PA.formula)
    (out : PA.term) (args : nat -> PA.term) : PA.formula :=
  PA.Formula.subst (graphSubst rank out args) graph.

Definition boundedEnv (M : RawPAModel) (rank : nat)
    (values : nat -> M) (i : nat) : M :=
  if i <? rank then values i else raw_zero M.

Lemma raw_sat_graphAt : forall (M : RawPAModel) rank graph out args e,
  raw_formula_sat M e (graphAt rank graph out args) <->
  raw_formula_sat M
    (scons M (raw_term_eval M e out)
      (boundedEnv M rank (fun i => raw_term_eval M e (args i))))
    graph.
Proof.
  intros M rank graph out args e.
  unfold graphAt. rewrite raw_formula_sat_subst.
  apply raw_formula_sat_ext. intros [|i]; simpl; [reflexivity |].
  unfold graphSubst, boundedEnv.
  destruct (i <? rank); reflexivity.
Qed.

(** The genuine row cases. *)
Definition seedCase (code value seed : PA.term) : PA.formula :=
  PA.pAnd
    (PA.pEq code
      (nodeTerm (PA.Term.numeral tagSeed) (PA.Term.numeral 0)))
    (PA.pEq value seed).

Definition zeroCase (code value : PA.term) : PA.formula :=
  PA.pAnd
    (PA.pEq code
      (nodeTerm (PA.Term.numeral tagZero) (PA.Term.numeral 0)))
    (PA.pEq value PA.tZero).

Definition succCase (code value betaCode betaStep : PA.term) : PA.formula :=
  existsN 2 (conjunction
    [PA.pEq (liftTerm 2 code)
       (nodeTerm (PA.Term.numeral tagSucc) (argumentCodeTerm 0));
     PA.Formula.ltTermAt (argumentCodeTerm 0) (liftTerm 2 code);
     PA.Formula.betaTermTermAt (argumentValueTerm 0)
       (liftTerm 2 betaCode) (liftTerm 2 betaStep)
       (argumentCodeTerm 0);
     PA.pEq (liftTerm 2 value)
       (PA.tSucc (argumentValueTerm 0))]).

Definition binaryCase (tag : nat)
    (op : PA.term -> PA.term -> PA.term)
    (code value betaCode betaStep : PA.term) : PA.formula :=
  existsN 4 (conjunction
    [PA.pEq (liftTerm 4 code)
       (nodeTerm (PA.Term.numeral tag)
         (pairTerm (argumentCodeTerm 0) (argumentCodeTerm 1)));
     PA.Formula.ltTermAt (argumentCodeTerm 0) (liftTerm 4 code);
     PA.Formula.ltTermAt (argumentCodeTerm 1) (liftTerm 4 code);
     PA.Formula.betaTermTermAt (argumentValueTerm 0)
       (liftTerm 4 betaCode) (liftTerm 4 betaStep)
       (argumentCodeTerm 0);
     PA.Formula.betaTermTermAt (argumentValueTerm 1)
       (liftTerm 4 betaCode) (liftTerm 4 betaStep)
       (argumentCodeTerm 1);
     PA.pEq (liftTerm 4 value)
       (op (argumentValueTerm 0) (argumentValueTerm 1))]).

Definition selectorBranch (rank formulaIndex : nat)
    (graph : PA.formula)
    (code value betaCode betaStep : PA.term) : PA.formula :=
  let width := 2 * rank in
  existsN width (conjunction
    [PA.pEq (liftTerm width code)
       (nodeTerm (PA.Term.numeral tagChoose)
         (pairTerm (PA.Term.numeral formulaIndex)
           (argumentVectorTerm rank)));
     conjunction (map (fun i =>
       PA.Formula.ltTermAt (argumentCodeTerm i)
         (liftTerm width code)) (seq 0 rank));
     conjunction (map (fun i =>
       PA.Formula.betaTermTermAt (argumentValueTerm i)
         (liftTerm width betaCode) (liftTerm width betaStep)
         (argumentCodeTerm i)) (seq 0 rank));
     graphAt rank graph (liftTerm width value)
       argumentValueTerm]).

Definition selectorCase (rank : nat)
    (code value betaCode betaStep : PA.term) : PA.formula :=
  disjunction (map (fun i =>
    selectorBranch rank i
      (canonicalSelectorFormula (selectorBody rank i))
      code value betaCode betaStep)
    (seq 0 (length (formula_rank_enum rank)))).

Definition programCases (rank : nat)
    (code value betaCode betaStep seed : PA.term) : PA.formula :=
  disjunction
    [seedCase code value seed;
     zeroCase code value;
     succCase code value betaCode betaStep;
     binaryCase tagAdd PA.tAdd code value betaCode betaStep;
     binaryCase tagMul PA.tMul code value betaCode betaStep;
     selectorCase rank code value betaCode betaStep].

(** The default guard is deliberately output-independent: it states that no
    proposed value satisfies any genuine constructor case at this code. *)
Definition noProgramCase (rank : nat)
    (code betaCode betaStep seed : PA.term) : PA.formula :=
  PA.pImp
    (PA.pEx
      (programCases rank (liftTerm 1 code) (PA.tVar 0)
        (liftTerm 1 betaCode) (liftTerm 1 betaStep)
        (liftTerm 1 seed)))
    PA.pBot.

Lemma raw_sat_noProgramCase_iff : forall (M : RawPAModel) rank
    code betaCode betaStep seed e,
  raw_formula_sat M e
      (noProgramCase rank code betaCode betaStep seed) <->
  ~ exists value : M,
      raw_formula_sat M (scons M value e)
        (programCases rank (liftTerm 1 code) (PA.tVar 0)
          (liftTerm 1 betaCode) (liftTerm 1 betaStep)
          (liftTerm 1 seed)).
Proof. reflexivity. Qed.

Definition programStep (rank : nat)
    (code value betaCode betaStep seed : PA.term) : PA.formula :=
  PA.pOr (programCases rank code value betaCode betaStep seed)
    (PA.pAnd (noProgramCase rank code betaCode betaStep seed)
      (PA.pEq value PA.tZero)).

Lemma raw_sat_programStep_iff : forall (M : RawPAModel) rank
    code value betaCode betaStep seed e,
  raw_formula_sat M e
      (programStep rank code value betaCode betaStep seed) <->
  raw_formula_sat M e
      (programCases rank code value betaCode betaStep seed) \/
  (raw_formula_sat M e
      (noProgramCase rank code betaCode betaStep seed) /\
   raw_term_eval M e value = raw_zero M).
Proof. reflexivity. Qed.

(** Semantic constructors for genuine recursive rows. *)
Theorem raw_sat_succCase_of : forall (M : RawPAModel)
    code value betaCode betaStep childTerm childValue e,
  raw_term_eval M e code =
    raw_term_eval M e
      (nodeTerm (PA.Term.numeral tagSucc) childTerm) ->
  rawLt M (raw_term_eval M e childTerm)
    (raw_term_eval M e code) ->
  RawBetaEntry M childValue
    (raw_term_eval M e betaCode) (raw_term_eval M e betaStep)
    (raw_term_eval M e childTerm) ->
  raw_term_eval M e value = raw_succ M childValue ->
  raw_formula_sat M e (succCase code value betaCode betaStep).
Proof.
  intros M code value betaCode betaStep childTerm childValue e
    hcode hbound hlookup hvalue.
  set (slots := argumentSlots (fun _ => childValue)
    (fun _ => raw_term_eval M e childTerm)).
  assert (hslotValue :
    raw_term_eval M (slotEnv M 2 slots e) (argumentValueTerm 0) =
    childValue) by reflexivity.
  assert (hslotCode :
    raw_term_eval M (slotEnv M 2 slots e) (argumentCodeTerm 0) =
    raw_term_eval M e childTerm) by reflexivity.
  unfold succCase.
  apply (raw_sat_existsN_of_slots M 2 _ slots e).
  apply (proj2 (raw_sat_conjunction M (slotEnv M 2 slots e) _)).
  intros f hf.
  cbn [In] in hf.
  destruct hf as [<- | [<- | [<- | [<- | []]]]].
  - change (raw_term_eval M (slotEnv M 2 slots e) (liftTerm 2 code) =
      raw_term_eval M (slotEnv M 2 slots e)
        (nodeTerm (PA.Term.numeral tagSucc) (argumentCodeTerm 0))).
    rewrite raw_term_eval_liftTerm_slotEnv.
    rewrite !raw_term_eval_nodeTerm, !raw_term_eval_numeral, hslotCode.
    rewrite raw_term_eval_nodeTerm, raw_term_eval_numeral in hcode.
    exact hcode.
  - apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
    rewrite raw_term_eval_liftTerm_slotEnv, hslotCode.
    exact hbound.
  - apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
    rewrite !raw_term_eval_liftTerm_slotEnv, hslotValue, hslotCode.
    exact hlookup.
  - change (raw_term_eval M (slotEnv M 2 slots e) (liftTerm 2 value) =
      raw_succ M (raw_term_eval M (slotEnv M 2 slots e)
        (argumentValueTerm 0))).
    rewrite raw_term_eval_liftTerm_slotEnv, hslotValue.
    exact hvalue.
Qed.

Theorem raw_sat_binaryCase_of : forall (M : RawPAModel)
    tag op opValue code value betaCode betaStep
    leftTerm rightTerm leftValue rightValue e,
  (forall e' a b,
    raw_term_eval M e' (op a b) =
    opValue (raw_term_eval M e' a) (raw_term_eval M e' b)) ->
  raw_term_eval M e code =
    raw_term_eval M e
      (nodeTerm (PA.Term.numeral tag)
        (pairTerm leftTerm rightTerm)) ->
  rawLt M (raw_term_eval M e leftTerm)
    (raw_term_eval M e code) ->
  rawLt M (raw_term_eval M e rightTerm)
    (raw_term_eval M e code) ->
  RawBetaEntry M leftValue
    (raw_term_eval M e betaCode) (raw_term_eval M e betaStep)
    (raw_term_eval M e leftTerm) ->
  RawBetaEntry M rightValue
    (raw_term_eval M e betaCode) (raw_term_eval M e betaStep)
    (raw_term_eval M e rightTerm) ->
  raw_term_eval M e value = opValue leftValue rightValue ->
  raw_formula_sat M e
    (binaryCase tag op code value betaCode betaStep).
Proof.
  intros M tag op opValue code value betaCode betaStep
    leftTerm rightTerm leftValue rightValue e hop hcode
    hleftBound hrightBound hleft hright hvalue.
  set (values := fun i => match i with 0 => leftValue | _ => rightValue end).
  set (codes := fun i => match i with
    | 0 => raw_term_eval M e leftTerm
    | _ => raw_term_eval M e rightTerm
    end).
  set (slots := argumentSlots values codes).
  assert (hslotValue0 :
    raw_term_eval M (slotEnv M 4 slots e) (argumentValueTerm 0) =
    leftValue) by reflexivity.
  assert (hslotCode0 :
    raw_term_eval M (slotEnv M 4 slots e) (argumentCodeTerm 0) =
    raw_term_eval M e leftTerm) by reflexivity.
  assert (hslotValue1 :
    raw_term_eval M (slotEnv M 4 slots e) (argumentValueTerm 1) =
    rightValue) by reflexivity.
  assert (hslotCode1 :
    raw_term_eval M (slotEnv M 4 slots e) (argumentCodeTerm 1) =
    raw_term_eval M e rightTerm) by reflexivity.
  unfold binaryCase.
  apply (raw_sat_existsN_of_slots M 4 _ slots e).
  apply (proj2 (raw_sat_conjunction M (slotEnv M 4 slots e) _)).
  intros f hf. cbn [In] in hf.
  destruct hf as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]].
  - change (raw_term_eval M (slotEnv M 4 slots e) (liftTerm 4 code) =
      raw_term_eval M (slotEnv M 4 slots e)
        (nodeTerm (PA.Term.numeral tag)
          (pairTerm (argumentCodeTerm 0) (argumentCodeTerm 1)))).
    rewrite raw_term_eval_liftTerm_slotEnv.
    rewrite !raw_term_eval_nodeTerm, !raw_term_eval_pairTerm,
      !raw_term_eval_numeral, hslotCode0, hslotCode1.
    rewrite raw_term_eval_nodeTerm, raw_term_eval_pairTerm,
      raw_term_eval_numeral in hcode.
    exact hcode.
  - apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
    rewrite raw_term_eval_liftTerm_slotEnv, hslotCode0.
    exact hleftBound.
  - apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
    rewrite raw_term_eval_liftTerm_slotEnv, hslotCode1.
    exact hrightBound.
  - apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
    rewrite !raw_term_eval_liftTerm_slotEnv, hslotValue0, hslotCode0.
    exact hleft.
  - apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
    rewrite !raw_term_eval_liftTerm_slotEnv, hslotValue1, hslotCode1.
    exact hright.
  - change (raw_term_eval M (slotEnv M 4 slots e) (liftTerm 4 value) =
      raw_term_eval M (slotEnv M 4 slots e)
        (op (argumentValueTerm 0) (argumentValueTerm 1))).
    rewrite hop.
    rewrite raw_term_eval_liftTerm_slotEnv, hslotValue0, hslotValue1.
    exact hvalue.
Qed.

Theorem raw_sat_selectorBranch_of_slots : forall (M : RawPAModel)
    rank formulaIndex graph code value betaCode betaStep e values terms,
  raw_term_eval M e code =
    raw_term_eval M e
      (nodeTerm (PA.Term.numeral tagChoose)
        (pairTerm (PA.Term.numeral formulaIndex)
          (argumentVectorOfTerms rank terms))) ->
  (forall i, i < rank ->
    rawLt M (raw_term_eval M e (terms i))
      (raw_term_eval M e code)) ->
  (forall i, i < rank ->
    RawBetaEntry M (values i)
      (raw_term_eval M e betaCode) (raw_term_eval M e betaStep)
      (raw_term_eval M e (terms i))) ->
  raw_formula_sat M
    (scons M (raw_term_eval M e value)
      (boundedEnv M rank values)) graph ->
  raw_formula_sat M e
    (selectorBranch rank formulaIndex graph
      code value betaCode betaStep).
Proof.
  intros M rank formulaIndex graph code value betaCode betaStep e
    values terms hcode hbounds hlookup hgraph.
  set (slots := argumentSlots values
    (fun i => raw_term_eval M e (terms i))).
  unfold selectorBranch.
  apply (raw_sat_existsN_of_slots M (2 * rank) _ slots e).
  apply (proj2 (raw_sat_conjunction M
    (slotEnv M (2 * rank) slots e) _)).
  intros f hf. cbn [In] in hf.
  destruct hf as [<- | [<- | [<- | [<- | []]]]].
  - change (raw_term_eval M (slotEnv M (2 * rank) slots e)
      (liftTerm (2 * rank) code) =
      raw_term_eval M (slotEnv M (2 * rank) slots e)
        (nodeTerm (PA.Term.numeral tagChoose)
          (pairTerm (PA.Term.numeral formulaIndex)
            (argumentVectorTerm rank)))).
    rewrite raw_term_eval_liftTerm_slotEnv.
    rewrite !raw_term_eval_nodeTerm, !raw_term_eval_pairTerm,
      !raw_term_eval_numeral.
    unfold slots.
    rewrite raw_eval_argumentVectorTerm_slots.
    rewrite raw_term_eval_nodeTerm, raw_term_eval_pairTerm,
      !raw_term_eval_numeral in hcode.
    exact hcode.
  - apply (proj2 (raw_sat_conjunction M
      (slotEnv M (2 * rank) slots e) _)).
    intros entry hentry.
    apply in_map_iff in hentry.
    destruct hentry as [i [<- hi]].
    apply in_seq in hi. destruct hi as [_ hi].
    apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
    rewrite raw_term_eval_liftTerm_slotEnv.
    unfold slots.
    rewrite raw_eval_argumentCodeTerm_slots by exact hi.
    apply hbounds. exact hi.
  - apply (proj2 (raw_sat_conjunction M
      (slotEnv M (2 * rank) slots e) _)).
    intros entry hentry.
    apply in_map_iff in hentry.
    destruct hentry as [i [<- hi]].
    apply in_seq in hi. destruct hi as [_ hi].
    apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
    rewrite !raw_term_eval_liftTerm_slotEnv.
    unfold slots.
    rewrite raw_eval_argumentValueTerm_slots by exact hi.
    rewrite raw_eval_argumentCodeTerm_slots by exact hi.
    apply hlookup. exact hi.
  - apply (proj2 (raw_sat_graphAt M rank graph
      (liftTerm (2 * rank) value) argumentValueTerm
      (slotEnv M (2 * rank) slots e))).
    rewrite raw_term_eval_liftTerm_slotEnv.
    assert (henv : forall n,
      scons M (raw_term_eval M e value)
        (boundedEnv M rank values) n =
      scons M (raw_term_eval M e value)
        (boundedEnv M rank
          (fun i => raw_term_eval M
            (slotEnv M (2 * rank) slots e)
            (argumentValueTerm i))) n).
    { intros [|i]; [reflexivity |].
      cbn [scons].
      unfold boundedEnv.
      destruct (i <? rank) eqn:hi; [|reflexivity].
      apply Nat.ltb_lt in hi.
      unfold slots.
      rewrite raw_eval_argumentValueTerm_slots by exact hi.
      reflexivity. }
    exact (proj1 (raw_formula_sat_ext M graph _ _ henv) hgraph).
Qed.

Corollary raw_sat_selectorCase_of : forall (M : RawPAModel)
    rank formulaIndex code value betaCode betaStep e values terms,
  formulaIndex < length (formula_rank_enum rank) ->
  raw_term_eval M e code =
    raw_term_eval M e
      (nodeTerm (PA.Term.numeral tagChoose)
        (pairTerm (PA.Term.numeral formulaIndex)
          (argumentVectorOfTerms rank terms))) ->
  (forall i, i < rank ->
    rawLt M (raw_term_eval M e (terms i))
      (raw_term_eval M e code)) ->
  (forall i, i < rank ->
    RawBetaEntry M (values i)
      (raw_term_eval M e betaCode) (raw_term_eval M e betaStep)
      (raw_term_eval M e (terms i))) ->
  raw_formula_sat M
    (scons M (raw_term_eval M e value)
      (boundedEnv M rank values))
    (canonicalSelectorFormula (selectorBody rank formulaIndex)) ->
  raw_formula_sat M e
    (selectorCase rank code value betaCode betaStep).
Proof.
  intros M rank formulaIndex code value betaCode betaStep e values terms
    hindex hcode hbounds hlookup hgraph.
  unfold selectorCase.
  apply (proj2 (raw_sat_disjunction M e _)).
  exists (selectorBranch rank formulaIndex
    (canonicalSelectorFormula (selectorBody rank formulaIndex))
    code value betaCode betaStep).
  split.
  - apply in_map_iff. exists formulaIndex. split; [reflexivity |].
    apply in_seq. lia.
  - apply raw_sat_selectorBranch_of_slots with (values := values)
      (terms := terms); assumption.
Qed.

(** A beta table evaluates the target code and validates every row through
    it against the fixed program-step relation. *)
Definition evaluator (rank : nat)
    (code value seed : PA.term) : PA.formula :=
  PA.pEx (PA.pEx
    (PA.pAnd
      (PA.Formula.betaTermTermAt
        (liftTerm 2 value) (PA.tVar 1) (PA.tVar 0)
        (liftTerm 2 code))
      (PA.pAll
        (PA.pImp
          (PA.Formula.leTermAt (PA.tVar 0) (liftTerm 3 code))
          (PA.pEx
            (PA.pAnd
              (PA.Formula.betaTermTermAt
                (PA.tVar 0) (PA.tVar 3) (PA.tVar 2)
                (PA.tVar 1))
              (programStep rank (PA.tVar 1) (PA.tVar 0)
                (PA.tVar 3) (PA.tVar 2)
                (liftTerm 4 seed)))))))).

Definition evaluatorRowEnv (M : RawPAModel)
    (rowValue rowCode betaStep betaCode : M)
    (tail : nat -> M) : nat -> M :=
  scons M rowValue
    (scons M rowCode (scons M betaStep (scons M betaCode tail))).

(** Exact semantic normal form of the fixed evaluator. *)
Theorem raw_sat_evaluator_iff : forall (M : RawPAModel) rank
    code value seed e,
  raw_formula_sat M e (evaluator rank code value seed) <->
  exists betaCode betaStep : M,
    RawBetaEntry M (raw_term_eval M e value)
      betaCode betaStep (raw_term_eval M e code) /\
    forall rowCode : M,
      rawLe M rowCode (raw_term_eval M e code) ->
      exists rowValue : M,
        RawBetaEntry M rowValue betaCode betaStep rowCode /\
        raw_formula_sat M
          (evaluatorRowEnv M rowValue rowCode betaStep betaCode e)
          (programStep rank (PA.tVar 1) (PA.tVar 0)
            (PA.tVar 3) (PA.tVar 2) (liftTerm 4 seed)).
Proof.
  intros M rank code value seed e.
  unfold evaluator. cbn [raw_formula_sat].
  split.
  - intros [betaCode [betaStep [htarget hrows]]].
    exists betaCode, betaStep. split.
    + apply (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)) in htarget.
      rewrite raw_term_eval_liftTerm_two_scons in htarget.
      cbn [raw_term_eval scons] in htarget.
      rewrite raw_term_eval_liftTerm_two_scons in htarget.
      exact htarget.
    + intros rowCode hle.
      assert (hleSat : raw_formula_sat M
        (scons M rowCode (scons M betaStep (scons M betaCode e)))
        (PA.Formula.leTermAt (PA.tVar 0) (liftTerm 3 code))).
      {
        apply (proj2 (raw_sat_leTermAt_iff M _ _ _)).
        cbn [raw_term_eval scons].
        rewrite raw_term_eval_liftTerm_three_scons.
        exact hle.
      }
      destruct (hrows rowCode hleSat) as [rowValue [hentry hstep]].
      exists rowValue. split.
      * apply (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)) in hentry.
        cbn [raw_term_eval scons] in hentry.
        exact hentry.
      * exact hstep.
  - intros [betaCode [betaStep [htarget hrows]]].
    exists betaCode, betaStep. split.
    + apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
      rewrite raw_term_eval_liftTerm_two_scons.
      cbn [raw_term_eval scons].
      rewrite raw_term_eval_liftTerm_two_scons.
      exact htarget.
    + intros rowCode hleSat.
      apply (proj1 (raw_sat_leTermAt_iff M _ _ _)) in hleSat.
      cbn [raw_term_eval scons] in hleSat.
      rewrite raw_term_eval_liftTerm_three_scons in hleSat.
      destruct (hrows rowCode hleSat) as [rowValue [hentry hstep]].
      exists rowValue. split.
      * apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
        cbn [raw_term_eval scons]. exact hentry.
      * exact hstep.
Qed.

(** Assemble evaluator satisfaction from an externally finite standard
    table. *)
Theorem raw_sat_evaluator_of_standard_table :
  forall (M : RawPAModel) rank target code value seed e
    betaCode betaStep (rowValue : nat -> M),
  raw_term_eval M e code = rawNumeralValue M target ->
  raw_term_eval M e value = rowValue target ->
  (forall rowCode,
    rawLe M rowCode (rawNumeralValue M target) ->
    exists k, k <= target /\ rowCode = rawNumeralValue M k) ->
  (forall k, k <= target ->
    RawBetaEntry M (rowValue k) betaCode betaStep
      (rawNumeralValue M k)) ->
  (forall k, k <= target ->
    raw_formula_sat M
      (evaluatorRowEnv M (rowValue k) (rawNumeralValue M k)
        betaStep betaCode e)
      (programStep rank (PA.tVar 1) (PA.tVar 0)
        (PA.tVar 3) (PA.tVar 2) (liftTerm 4 seed))) ->
  raw_formula_sat M e (evaluator rank code value seed).
Proof.
  intros M rank target code value seed e betaCode betaStep rowValue
    hcode hvalue hbounded hentry hstep.
  apply (proj2 (raw_sat_evaluator_iff M rank code value seed e)).
  exists betaCode, betaStep. split.
  - rewrite hcode, hvalue. apply hentry. lia.
  - intros rowCode hle.
    rewrite hcode in hle.
    destruct (hbounded rowCode hle) as [k [hk ->]].
    exists (rowValue k). split; [apply hentry | apply hstep]; exact hk.
Qed.

End PAProgramTrace.
