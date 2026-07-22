(**
  Natural-number codes for the PA syntax used by bounded consistency.

  This file is an arithmetization milestone, not yet the internal reflection
  theorem.  It fixes one concrete, canonical coding of PA terms and formulae
  using [PAListCode.listCode], supplies total fuelled decoders, and proves the
  two round-trip laws needed to move safely between typed syntax and natural
  codes.  The same representation also transports the phase-one
  quantifier-group calculation to codes.

  Constructor codes are lists whose first entry is a tag.  Recursive children
  occupy the remaining entries.  For example,

    code(x + y)       = listCode [3; code(x); code(y)]
    code(A -> B)      = listCode [2; code(A); code(B)].

  The canonical list code strictly dominates each entry.  Consequently every
  recursive child has a smaller code than its parent.  [decodeTermFuel] and
  [decodeFormulaFuel] spend one unit of fuel at each constructor; choosing
  [S code] as fuel is therefore sufficient for every genuine code while
  malformed numbers deterministically decode to [None].
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From BoundedPAConsistency Require Import BoundedConsistency.

Import ListNotations.

Module PABoundedCodedSyntax.

Import PA.
Import PABoundedConsistency.

(** Small consequences of the polynomial list coding.  They are stated here
    because the syntax decoders repeatedly need the fact that the second and
    third entries of a constructor code are strictly smaller than the whole
    code. *)
Lemma listCode_head_lt : forall x xs,
  x < PAListCode.listCode (x :: xs).
Proof.
  intros x xs. simpl.
  pose proof (PAListCode.polynomialPair_left_le
    x (PAListCode.listCode xs)).
  lia.
Qed.

Lemma listCode_second_lt : forall tag child rest,
  child < PAListCode.listCode (tag :: child :: rest).
Proof.
  intros tag child rest.
  eapply Nat.lt_trans.
  - apply listCode_head_lt.
  - apply PAListCode.listCode_tail_lt.
Qed.

Lemma listCode_third_lt : forall tag left right rest,
  right < PAListCode.listCode (tag :: left :: right :: rest).
Proof.
  intros tag left right rest.
  eapply Nat.lt_trans.
  - apply listCode_head_lt.
  - eapply Nat.lt_trans.
    + apply PAListCode.listCode_tail_lt.
    + apply PAListCode.listCode_tail_lt.
Qed.

(** Tags zero through four are used for terms; tags zero through six are used
    independently for formulae.  Because a decoder always knows which syntax
    category it is reading, the two tag spaces need not be disjoint. *)
Fixpoint termCode (t : term) : nat :=
  match t with
  | tVar n => PAListCode.listCode [0; n]
  | tZero => PAListCode.listCode [1]
  | tSucc a => PAListCode.listCode [2; termCode a]
  | tAdd a b => PAListCode.listCode [3; termCode a; termCode b]
  | tMul a b => PAListCode.listCode [4; termCode a; termCode b]
  end.

Fixpoint formulaCode (phi : formula) : nat :=
  match phi with
  | pEq a b => PAListCode.listCode [0; termCode a; termCode b]
  | pBot => PAListCode.listCode [1]
  | pImp a b => PAListCode.listCode [2; formulaCode a; formulaCode b]
  | pAnd a b => PAListCode.listCode [3; formulaCode a; formulaCode b]
  | pOr a b => PAListCode.listCode [4; formulaCode a; formulaCode b]
  | pAll a => PAListCode.listCode [5; formulaCode a]
  | pEx a => PAListCode.listCode [6; formulaCode a]
  end.

(** Every immediate recursive code is smaller than its constructor code.
    Besides documenting well-foundedness, these lemmas are the arithmetic
    reason why [S code] units of decoding fuel always suffice. *)
Lemma termCode_succ_child_lt : forall a,
  termCode a < termCode (tSucc a).
Proof.
  intro a.
  change (termCode a < PAListCode.listCode [2; termCode a]).
  apply listCode_second_lt.
Qed.

Lemma termCode_add_left_lt : forall a b,
  termCode a < termCode (tAdd a b).
Proof.
  intros a b.
  change (termCode a < PAListCode.listCode [3; termCode a; termCode b]).
  apply listCode_second_lt.
Qed.

Lemma termCode_add_right_lt : forall a b,
  termCode b < termCode (tAdd a b).
Proof.
  intros a b.
  change (termCode b < PAListCode.listCode [3; termCode a; termCode b]).
  apply listCode_third_lt.
Qed.

Lemma termCode_mul_left_lt : forall a b,
  termCode a < termCode (tMul a b).
Proof.
  intros a b.
  change (termCode a < PAListCode.listCode [4; termCode a; termCode b]).
  apply listCode_second_lt.
Qed.

Lemma termCode_mul_right_lt : forall a b,
  termCode b < termCode (tMul a b).
Proof.
  intros a b.
  change (termCode b < PAListCode.listCode [4; termCode a; termCode b]).
  apply listCode_third_lt.
Qed.

Lemma formulaCode_eq_left_lt : forall a b,
  termCode a < formulaCode (pEq a b).
Proof.
  intros a b.
  change (termCode a < PAListCode.listCode [0; termCode a; termCode b]).
  apply listCode_second_lt.
Qed.

Lemma formulaCode_eq_right_lt : forall a b,
  termCode b < formulaCode (pEq a b).
Proof.
  intros a b.
  change (termCode b < PAListCode.listCode [0; termCode a; termCode b]).
  apply listCode_third_lt.
Qed.

Lemma formulaCode_imp_left_lt : forall a b,
  formulaCode a < formulaCode (pImp a b).
Proof.
  intros a b.
  change (formulaCode a <
    PAListCode.listCode [2; formulaCode a; formulaCode b]).
  apply listCode_second_lt.
Qed.

Lemma formulaCode_imp_right_lt : forall a b,
  formulaCode b < formulaCode (pImp a b).
Proof.
  intros a b.
  change (formulaCode b <
    PAListCode.listCode [2; formulaCode a; formulaCode b]).
  apply listCode_third_lt.
Qed.

Lemma formulaCode_and_left_lt : forall a b,
  formulaCode a < formulaCode (pAnd a b).
Proof.
  intros a b.
  change (formulaCode a <
    PAListCode.listCode [3; formulaCode a; formulaCode b]).
  apply listCode_second_lt.
Qed.

Lemma formulaCode_and_right_lt : forall a b,
  formulaCode b < formulaCode (pAnd a b).
Proof.
  intros a b.
  change (formulaCode b <
    PAListCode.listCode [3; formulaCode a; formulaCode b]).
  apply listCode_third_lt.
Qed.

Lemma formulaCode_or_left_lt : forall a b,
  formulaCode a < formulaCode (pOr a b).
Proof.
  intros a b.
  change (formulaCode a <
    PAListCode.listCode [4; formulaCode a; formulaCode b]).
  apply listCode_second_lt.
Qed.

Lemma formulaCode_or_right_lt : forall a b,
  formulaCode b < formulaCode (pOr a b).
Proof.
  intros a b.
  change (formulaCode b <
    PAListCode.listCode [4; formulaCode a; formulaCode b]).
  apply listCode_third_lt.
Qed.

Lemma formulaCode_all_child_lt : forall a,
  formulaCode a < formulaCode (pAll a).
Proof.
  intro a.
  change (formulaCode a < PAListCode.listCode [5; formulaCode a]).
  apply listCode_second_lt.
Qed.

Lemma formulaCode_ex_child_lt : forall a,
  formulaCode a < formulaCode (pEx a).
Proof.
  intro a.
  change (formulaCode a < PAListCode.listCode [6; formulaCode a]).
  apply listCode_second_lt.
Qed.

(** Total decoders.  Fuel is structurally decreasing even on malformed input;
    genuine constructor children are decoded with the predecessor fuel. *)
Fixpoint decodeTermFuel (fuel p : nat) : option term :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match PAListCode.decode p with
      | Some [0; n] => Some (tVar n)
      | Some [1] => Some tZero
      | Some [2; a] =>
          match decodeTermFuel fuel' a with
          | Some a' => Some (tSucc a')
          | None => None
          end
      | Some [3; a; b] =>
          match decodeTermFuel fuel' a, decodeTermFuel fuel' b with
          | Some a', Some b' => Some (tAdd a' b')
          | _, _ => None
          end
      | Some [4; a; b] =>
          match decodeTermFuel fuel' a, decodeTermFuel fuel' b with
          | Some a', Some b' => Some (tMul a' b')
          | _, _ => None
          end
      | _ => None
      end
  end.

Definition decodeTerm (p : nat) : option term :=
  decodeTermFuel (S p) p.

Fixpoint decodeFormulaFuel (fuel p : nat) : option formula :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match PAListCode.decode p with
      | Some [0; a; b] =>
          match decodeTermFuel fuel' a, decodeTermFuel fuel' b with
          | Some a', Some b' => Some (pEq a' b')
          | _, _ => None
          end
      | Some [1] => Some pBot
      | Some [2; a; b] =>
          match decodeFormulaFuel fuel' a, decodeFormulaFuel fuel' b with
          | Some a', Some b' => Some (pImp a' b')
          | _, _ => None
          end
      | Some [3; a; b] =>
          match decodeFormulaFuel fuel' a, decodeFormulaFuel fuel' b with
          | Some a', Some b' => Some (pAnd a' b')
          | _, _ => None
          end
      | Some [4; a; b] =>
          match decodeFormulaFuel fuel' a, decodeFormulaFuel fuel' b with
          | Some a', Some b' => Some (pOr a' b')
          | _, _ => None
          end
      | Some [5; a] =>
          match decodeFormulaFuel fuel' a with
          | Some a' => Some (pAll a')
          | None => None
          end
      | Some [6; a] =>
          match decodeFormulaFuel fuel' a with
          | Some a' => Some (pEx a')
          | None => None
          end
      | _ => None
      end
  end.

Definition decodeFormula (p : nat) : option formula :=
  decodeFormulaFuel (S p) p.

(** The round-trip proof is parameterized by arbitrary sufficient fuel.  This
    form is stronger than the public decoder theorem and is what later coded
    syntax algorithms can reuse for recursive calls. *)
Lemma decodeTermFuel_termCode : forall t fuel,
  termCode t < fuel ->
  decodeTermFuel fuel (termCode t) = Some t.
Proof.
  induction t as [n | | a IHa | a IHa b IHb | a IHa b IHb];
    intros [|fuel] h; try lia.
  - cbn [termCode decodeTermFuel].
    rewrite PAListCode.decode_listCode. reflexivity.
  - cbn [termCode decodeTermFuel].
    rewrite PAListCode.decode_listCode. reflexivity.
  - cbn [termCode decodeTermFuel].
    rewrite PAListCode.decode_listCode.
    rewrite IHa.
    + reflexivity.
    + pose proof (termCode_succ_child_lt a). lia.
  - cbn [termCode decodeTermFuel].
    rewrite PAListCode.decode_listCode.
    rewrite IHa, IHb.
    + reflexivity.
    + pose proof (termCode_add_right_lt a b). lia.
    + pose proof (termCode_add_left_lt a b). lia.
  - cbn [termCode decodeTermFuel].
    rewrite PAListCode.decode_listCode.
    rewrite IHa, IHb.
    + reflexivity.
    + pose proof (termCode_mul_right_lt a b). lia.
    + pose proof (termCode_mul_left_lt a b). lia.
Qed.

Theorem decodeTerm_termCode : forall t,
  decodeTerm (termCode t) = Some t.
Proof.
  intro t. unfold decodeTerm.
  apply decodeTermFuel_termCode. lia.
Qed.

Lemma decodeFormulaFuel_formulaCode : forall phi fuel,
  formulaCode phi < fuel ->
  decodeFormulaFuel fuel (formulaCode phi) = Some phi.
Proof.
  induction phi as [a b | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa]; intros [|fuel] h; try lia.
  - cbn [formulaCode decodeFormulaFuel].
    rewrite PAListCode.decode_listCode.
    rewrite !decodeTermFuel_termCode.
    + reflexivity.
    + pose proof (formulaCode_eq_right_lt a b). lia.
    + pose proof (formulaCode_eq_left_lt a b). lia.
  - cbn [formulaCode decodeFormulaFuel].
    rewrite PAListCode.decode_listCode. reflexivity.
  - cbn [formulaCode decodeFormulaFuel].
    rewrite PAListCode.decode_listCode.
    rewrite IHa, IHb.
    + reflexivity.
    + pose proof (formulaCode_imp_right_lt a b). lia.
    + pose proof (formulaCode_imp_left_lt a b). lia.
  - cbn [formulaCode decodeFormulaFuel].
    rewrite PAListCode.decode_listCode.
    rewrite IHa, IHb.
    + reflexivity.
    + pose proof (formulaCode_and_right_lt a b). lia.
    + pose proof (formulaCode_and_left_lt a b). lia.
  - cbn [formulaCode decodeFormulaFuel].
    rewrite PAListCode.decode_listCode.
    rewrite IHa, IHb.
    + reflexivity.
    + pose proof (formulaCode_or_right_lt a b). lia.
    + pose proof (formulaCode_or_left_lt a b). lia.
  - cbn [formulaCode decodeFormulaFuel].
    rewrite PAListCode.decode_listCode.
    rewrite IHa.
    + reflexivity.
    + pose proof (formulaCode_all_child_lt a). lia.
  - cbn [formulaCode decodeFormulaFuel].
    rewrite PAListCode.decode_listCode.
    rewrite IHa.
    + reflexivity.
    + pose proof (formulaCode_ex_child_lt a). lia.
Qed.

Theorem decodeFormula_formulaCode : forall phi,
  decodeFormula (formulaCode phi) = Some phi.
Proof.
  intro phi. unfold decodeFormula.
  apply decodeFormulaFuel_formulaCode. lia.
Qed.

(** Quotation is injective because a common natural code has a unique result
    under each deterministic decoder. *)
Theorem termCode_injective : forall a b,
  termCode a = termCode b -> a = b.
Proof.
  intros a b h.
  pose proof (decodeTerm_termCode a) as ha.
  pose proof (decodeTerm_termCode b) as hb.
  rewrite h in ha. rewrite ha in hb. now inversion hb.
Qed.

Theorem formulaCode_injective : forall a b,
  formulaCode a = formulaCode b -> a = b.
Proof.
  intros a b h.
  pose proof (decodeFormula_formulaCode a) as ha.
  pose proof (decodeFormula_formulaCode b) as hb.
  rewrite h in ha. rewrite ha in hb. now inversion hb.
Qed.

(** Validity and hierarchy rank as total predicates/functions on arbitrary
    natural numbers.  Returning an option for the rank prevents a malformed
    number from being confused with a genuine quantifier-free formula. *)
Definition ValidTermCode (p : nat) : Prop :=
  exists t, decodeTerm p = Some t.

Definition ValidFormulaCode (p : nat) : Prop :=
  exists phi, decodeFormula p = Some phi.

Definition validTermCodeb (p : nat) : bool :=
  match decodeTerm p with
  | Some _ => true
  | None => false
  end.

Definition validFormulaCodeb (p : nat) : bool :=
  match decodeFormula p with
  | Some _ => true
  | None => false
  end.

Lemma validTermCodeb_spec : forall p,
  validTermCodeb p = true <-> ValidTermCode p.
Proof.
  intro p. unfold validTermCodeb, ValidTermCode.
  destruct (decodeTerm p) as [t|] eqn:h; split; intro h'.
  - now exists t.
  - reflexivity.
  - discriminate.
  - destruct h' as [t ht]. discriminate.
Qed.

Lemma validFormulaCodeb_spec : forall p,
  validFormulaCodeb p = true <-> ValidFormulaCode p.
Proof.
  intro p. unfold validFormulaCodeb, ValidFormulaCode.
  destruct (decodeFormula p) as [phi|] eqn:h; split; intro h'.
  - now exists phi.
  - reflexivity.
  - discriminate.
  - destruct h' as [phi hphi]. discriminate.
Qed.

Definition codedQuantifierGroups (p : nat) : option nat :=
  match decodeFormula p with
  | Some phi => Some (quantifierGroups phi)
  | None => None
  end.

Theorem codedQuantifierGroups_formulaCode : forall phi,
  codedQuantifierGroups (formulaCode phi) =
    Some (quantifierGroups phi).
Proof.
  intro phi. unfold codedQuantifierGroups.
  now rewrite decodeFormula_formulaCode.
Qed.

Definition CodeQuantifierBounded (n p : nat) : Prop :=
  exists rank, codedQuantifierGroups p = Some rank /\ rank <= n.

Theorem CodeQuantifierBounded_formulaCode_iff : forall n phi,
  CodeQuantifierBounded n (formulaCode phi) <->
  QuantifierBounded n phi.
Proof.
  intros n phi.
  unfold CodeQuantifierBounded, QuantifierBounded.
  rewrite codedQuantifierGroups_formulaCode.
  split.
  - intros [rank [h hrank]]. inversion h; subst rank. exact hrank.
  - intro h. exists (quantifierGroups phi). split; [reflexivity | exact h].
Qed.

(** Code-level presentations of the syntactic operations used by quantifier
    rules.  They are deliberately partial on malformed natural numbers. *)
Definition codedRename (r : nat -> nat) (p : nat) : option nat :=
  match decodeFormula p with
  | Some phi => Some (formulaCode (Formula.rename r phi))
  | None => None
  end.

Definition codedInstantiate (termNumber formulaNumber : nat) : option nat :=
  match decodeTerm termNumber, decodeFormula formulaNumber with
  | Some t, Some phi =>
      Some (formulaCode (Formula.subst (Formula.instTerm t) phi))
  | _, _ => None
  end.

Theorem codedRename_formulaCode : forall r phi,
  codedRename r (formulaCode phi) =
    Some (formulaCode (Formula.rename r phi)).
Proof.
  intros r phi. unfold codedRename.
  now rewrite decodeFormula_formulaCode.
Qed.

Theorem codedInstantiate_formulaCode : forall t phi,
  codedInstantiate (termCode t) (formulaCode phi) =
    Some (formulaCode (Formula.subst (Formula.instTerm t) phi)).
Proof.
  intros t phi. unfold codedInstantiate.
  now rewrite decodeTerm_termCode, decodeFormula_formulaCode.
Qed.

(** The coded hierarchy level is invariant under both operations on genuine
    codes.  This is the code-level interface needed when checking the
    universal/existential and equality-elimination rules of a future coded
    proof predicate. *)
Theorem codedQuantifierGroups_rename : forall r phi renamed,
  codedRename r (formulaCode phi) = Some renamed ->
  codedQuantifierGroups renamed = Some (quantifierGroups phi).
Proof.
  intros r phi renamed h.
  rewrite codedRename_formulaCode in h. inversion h; subst renamed.
  rewrite codedQuantifierGroups_formulaCode.
  now rewrite quantifierGroups_rename.
Qed.

Theorem codedQuantifierGroups_instantiate : forall t phi instantiated,
  codedInstantiate (termCode t) (formulaCode phi) = Some instantiated ->
  codedQuantifierGroups instantiated = Some (quantifierGroups phi).
Proof.
  intros t phi instantiated h.
  rewrite codedInstantiate_formulaCode in h. inversion h; subst instantiated.
  rewrite codedQuantifierGroups_formulaCode.
  now rewrite quantifierGroups_subst.
Qed.

End PABoundedCodedSyntax.
