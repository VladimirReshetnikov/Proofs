(**
  Hereditary Cantor-normal-form notations below epsilon zero.

  This file is the semantic, executable half of the Rocq development.  A
  later companion file exposes the predicates below by genuine first-order
  formulae of PA.  The numeric representation deliberately agrees with the
  Lean/Foundation representation, rather than with the polynomial list code:

      pair a b = if a < b then b^2 + a else a^2 + a + b

      code 0                 = 0
      code (omega^e*(c+1)+r) = 1 + pair (code e) (pair c (code r)).

  Storing the predecessor [c] makes every coefficient positive without an
  extra tag.  The outer successor reserves zero for the zero notation and
  makes both recursive child codes strictly smaller than their parent.
*)

From Stdlib Require Import List Arith Lia Bool PeanoNat.

Module PAEpsilonZero.

(** * The square-shell pairing bijection *)

Definition squarePair (a b : nat) : nat :=
  if a <? b then b * b + a else a * a + a + b.

Lemma squarePair_left_le : forall a b, a <= squarePair a b.
Proof.
  intros a b. unfold squarePair.
  destruct (a <? b); nia.
Qed.

Lemma squarePair_right_le : forall a b, b <= squarePair a b.
Proof.
  intros a b. unfold squarePair.
  destruct (a <? b) eqn:hab.
  - apply Nat.ltb_lt in hab. nia.
  - apply Nat.ltb_ge in hab. nia.
Qed.

(** The shell number is the larger coordinate. *)
Lemma sqrt_eq_of_square_bounds : forall n s,
  s * s <= n -> n < S s * S s -> Nat.sqrt n = s.
Proof.
  intros n s hlo hhi.
  pose proof (Nat.sqrt_specif n) as hsqrt.
  nia.
Qed.

Lemma sqrt_squarePair : forall a b,
  Nat.sqrt (squarePair a b) = Nat.max a b.
Proof.
  intros a b. unfold squarePair.
  destruct (a <? b) eqn:hab.
  - apply Nat.ltb_lt in hab.
    rewrite Nat.max_r by lia.
    apply sqrt_eq_of_square_bounds; nia.
  - apply Nat.ltb_ge in hab.
    rewrite Nat.max_l by lia.
    apply sqrt_eq_of_square_bounds; nia.
Qed.

(** This is the same inverse used by Foundation: subtract the lower square,
    then decide on which half of the shell the input lies. *)
Definition squareUnpair (n : nat) : nat * nat :=
  let s := Nat.sqrt n in
  let r := n - s * s in
  if r <? s then (r, s) else (s, r - s).

Theorem squareUnpair_pair : forall a b,
  squareUnpair (squarePair a b) = (a, b).
Proof.
  intros a b. unfold squareUnpair.
  rewrite sqrt_squarePair.
  unfold squarePair.
  destruct (a <? b) eqn:hab.
  - pose proof hab as habb. apply Nat.ltb_lt in hab.
    rewrite Nat.max_r by lia.
    replace (b * b + a - b * b) with a by nia.
    rewrite habb.
    reflexivity.
  - pose proof hab as habb. apply Nat.ltb_ge in hab.
    rewrite Nat.max_l by lia.
    replace (a * a + a + b - a * a) with (a + b) by nia.
    assert (hinner : (a + b <? a) = false).
    { apply Nat.ltb_ge. lia. }
    rewrite hinner.
    replace (a + b - a) with b by nia.
    reflexivity.
Qed.

Theorem squarePair_injective : forall a b c d,
  squarePair a b = squarePair c d -> a = c /\ b = d.
Proof.
  intros a b c d h.
  assert (hu : squareUnpair (squarePair a b) =
      squareUnpair (squarePair c d)) by now rewrite h.
  rewrite !squareUnpair_pair in hu.
  inversion hu. now split.
Qed.

Theorem squarePair_unpair : forall n,
  squarePair (fst (squareUnpair n)) (snd (squareUnpair n)) = n.
Proof.
  intro n. unfold squareUnpair.
  set (s := Nat.sqrt n).
  set (r := n - s * s).
  pose proof (Nat.sqrt_specif n) as hsqrt.
  assert (hsquare : s * s <= n).
  { unfold s. exact (proj1 hsqrt). }
  assert (hn : n = s * s + r).
  { unfold r. nia. }
  assert (hr : r < S s * S s - s * s).
  { nia. }
  destruct (r <? s) eqn:hrs.
  - pose proof hrs as hrsb. apply Nat.ltb_lt in hrs. simpl.
    unfold squarePair. rewrite hrsb. nia.
  - apply Nat.ltb_ge in hrs. simpl.
    assert (hrupper : r - s <= s) by nia.
    assert (hinner : (s <? r - s) = false).
    { apply Nat.ltb_ge. exact hrupper. }
    unfold squarePair. rewrite hinner. nia.
Qed.

(** * Raw hereditary CNF syntax *)

(** [oadd e c r] represents [omega^e * (c+1) + r].  The constructor stores
    the predecessor of the positive coefficient. *)
Inductive ONote : Type :=
| ozero : ONote
| oadd : ONote -> nat -> ONote -> ONote.

Definition coefficient (cPred : nat) : nat := S cPred.

Fixpoint onoteEqb (a b : ONote) : bool :=
  match a, b with
  | ozero, ozero => true
  | oadd ae ac ar, oadd be bc br =>
      onoteEqb ae be && Nat.eqb ac bc && onoteEqb ar br
  | _, _ => false
  end.

Lemma onoteEqb_spec : forall a b, onoteEqb a b = true <-> a = b.
Proof.
  induction a as [|ae IHe ac ar IHr]; intros [|be bc br]; simpl;
    try (split; [discriminate | congruence]).
  - tauto.
  - rewrite Bool.andb_true_iff, Bool.andb_true_iff,
      IHe, IHr, Nat.eqb_eq.
    split.
    + intros [[he hc] hr]. now subst.
    + intro h. inversion h. repeat split; reflexivity.
Qed.

(** Structural lexicographic comparison of hereditary CNFs. *)
Fixpoint onoteCompare (a b : ONote) : comparison :=
  match a, b with
  | ozero, ozero => Eq
  | ozero, oadd _ _ _ => Lt
  | oadd _ _ _, ozero => Gt
  | oadd ae ac ar, oadd be bc br =>
      match onoteCompare ae be with
      | Eq =>
          match Nat.compare ac bc with
          | Eq => onoteCompare ar br
          | cmp => cmp
          end
      | cmp => cmp
      end
  end.

Lemma onoteCompare_refl : forall a, onoteCompare a a = Eq.
Proof.
  induction a as [|e IHe c r IHr]; simpl.
  - reflexivity.
  - now rewrite IHe, Nat.compare_refl.
Qed.

Lemma onoteCompare_eq : forall a b,
  onoteCompare a b = Eq -> a = b.
Proof.
  induction a as [|ae IHe ac ar IHr]; intros [|be bc br] h;
    simpl in h; try discriminate; [reflexivity |].
  destruct (onoteCompare ae be) eqn:he; try discriminate.
  destruct (Nat.compare ac bc) eqn:hc; try discriminate.
  apply IHe in he. apply Nat.compare_eq in hc. apply IHr in h.
  now subst.
Qed.

Lemma onoteCompare_eq_iff : forall a b,
  onoteCompare a b = Eq <-> a = b.
Proof.
  intros a b. split.
  - apply onoteCompare_eq.
  - intro h. subst. apply onoteCompare_refl.
Qed.

Lemma onoteCompare_antisym : forall a b,
  onoteCompare b a = CompOpp (onoteCompare a b).
Proof.
  induction a as [|ae IHe ac ar IHr]; intros [|be bc br]; simpl;
    try reflexivity.
  rewrite IHe, IHr, Nat.compare_antisym.
  destruct (onoteCompare ae be), (Nat.compare ac bc); reflexivity.
Qed.

Lemma onoteCompare_gt_reverse : forall a b,
  onoteCompare a b = Gt -> onoteCompare b a = Lt.
Proof.
  intros a b h. rewrite onoteCompare_antisym, h. reflexivity.
Qed.

Lemma onoteCompare_lt_reverse : forall a b,
  onoteCompare a b = Lt -> onoteCompare b a = Gt.
Proof.
  intros a b h. rewrite onoteCompare_antisym, h. reflexivity.
Qed.

(** A raw note is in hereditary Cantor normal form when both recursive pieces
    are normal and, if the remainder is nonzero, its leading exponent is
    strictly smaller than the displayed exponent.  Positivity of the
    coefficient is automatic from predecessor storage. *)
Fixpoint NF (a : ONote) : Prop :=
  match a with
  | ozero => True
  | oadd e _ r =>
      NF e /\ NF r /\
      match r with
      | ozero => True
      | oadd e' _ _ => onoteCompare e' e = Lt
      end
  end.

Lemma NF_zero : NF ozero.
Proof. exact I. Qed.

Lemma NF_oadd_inv : forall e c r,
  NF (oadd e c r) ->
  NF e /\ NF r /\
  match r with
  | ozero => True
  | oadd e' _ _ => onoteCompare e' e = Lt
  end.
Proof. intros e c r h. exact h. Qed.

(** * The natural-number coding bijection *)

Fixpoint encode (a : ONote) : nat :=
  match a with
  | ozero => 0
  | oadd e c r =>
      S (squarePair (encode e) (squarePair c (encode r)))
  end.

Lemma encode_exp_lt : forall e c r,
  encode e < encode (oadd e c r).
Proof.
  intros e c r. simpl.
  pose proof (squarePair_left_le (encode e)
    (squarePair c (encode r))). lia.
Qed.

Lemma encode_rest_lt : forall e c r,
  encode r < encode (oadd e c r).
Proof.
  intros e c r. simpl.
  pose proof (squarePair_right_le c (encode r)) as hinner.
  pose proof (squarePair_right_le (encode e)
    (squarePair c (encode r))) as houter. lia.
Qed.

(** Fuel follows the two strictly smaller child codes.  On insufficient fuel
    the arbitrary default is zero; [decode] always supplies enough fuel. *)
Fixpoint decodeFuel (fuel code : nat) : ONote :=
  match fuel with
  | 0 => ozero
  | S fuel' =>
      match code with
      | 0 => ozero
      | S shell =>
          let outer := squareUnpair shell in
          let inner := squareUnpair (snd outer) in
          oadd (decodeFuel fuel' (fst outer))
            (fst inner) (decodeFuel fuel' (snd inner))
      end
  end.

Definition decode (code : nat) : ONote := decodeFuel (S code) code.

Lemma decodeFuel_encode : forall a fuel,
  encode a < fuel -> decodeFuel fuel (encode a) = a.
Proof.
  induction a as [|e IHe c r IHr]; intros fuel h.
  - destruct fuel; reflexivity.
  - destruct fuel as [|fuel]; [simpl in h; lia |].
    cbn [encode] in h.
    assert (houter :
      squarePair (encode e) (squarePair c (encode r)) < fuel) by lia.
    assert (he : encode e < fuel).
    {
      eapply Nat.le_lt_trans.
      - apply squarePair_left_le.
      - exact houter.
    }
    assert (hr : encode r < fuel).
    {
      eapply Nat.le_lt_trans.
      - eapply Nat.le_trans.
        + apply squarePair_right_le.
        + apply squarePair_right_le.
      - exact houter.
    }
    cbn [encode decodeFuel].
    rewrite squareUnpair_pair. cbn.
    rewrite squareUnpair_pair. cbn.
    now rewrite (IHe fuel he), (IHr fuel hr).
Qed.

Theorem decode_encode : forall a, decode (encode a) = a.
Proof.
  intro a. unfold decode. apply decodeFuel_encode. lia.
Qed.

(** The converse direction is proved directly for every sufficiently fueled
    call.  This avoids a fragile appeal to fuel irrelevance. *)
Lemma encode_decodeFuel : forall fuel code,
  code < fuel -> encode (decodeFuel fuel code) = code.
Proof.
  induction fuel as [|fuel IH]; intros code h; [lia |].
  destruct code as [|shell]; [reflexivity |].
  simpl.
  remember (squareUnpair shell) as outer eqn:houter.
  destruct outer as [ecode packed].
  remember (squareUnpair packed) as inner eqn:hinner.
  destruct inner as [c rcode]. simpl.
  pose proof (squarePair_unpair shell) as hshell.
  pose proof (squarePair_unpair packed) as hpacked.
  rewrite <- houter in hshell. simpl in hshell.
  rewrite <- hinner in hpacked. simpl in hpacked.
  assert (he : ecode < fuel).
  {
    pose proof (squarePair_left_le ecode packed) as hleft.
    lia.
  }
  assert (hr : rcode < fuel).
  {
    pose proof (squarePair_right_le c rcode) as hinnerBound.
    pose proof (squarePair_right_le ecode packed) as houterBound.
    lia.
  }
  rewrite <- hinner. simpl.
  rewrite IH by exact he. rewrite IH by exact hr.
  now rewrite hpacked, hshell.
Qed.

Theorem encode_decode : forall code, encode (decode code) = code.
Proof.
  intro code. unfold decode. apply encode_decodeFuel. lia.
Qed.

Theorem encode_injective : forall a b, encode a = encode b -> a = b.
Proof.
  intros a b h.
  pose proof (f_equal decode h) as hd.
  now rewrite !decode_encode in hd.
Qed.

Theorem decode_injective : forall a b, decode a = decode b -> a = b.
Proof.
  intros a b h.
  pose proof (f_equal encode h) as he.
  now rewrite !encode_decode in he.
Qed.

Definition ValidOrdinalCode (code : nat) : Prop := NF (decode code).

Lemma valid_encode_iff : forall a,
  ValidOrdinalCode (encode a) <-> NF a.
Proof.
  intro a. unfold ValidOrdinalCode. now rewrite decode_encode.
Qed.

(** * Arithmetic on raw notations

    These definitions port Mathlib's [ONote] algorithms.  They are total on
    raw syntax, but their intended ordinal meaning and their normal-form
    preservation statements require normal inputs. *)

Definition onoteOne : ONote := oadd ozero 0 ozero.

Definition onoteOmega : ONote := oadd onoteOne 0 ozero.

Definition onoteAddAux (e : ONote) (c : nat) (o : ONote) : ONote :=
  match o with
  | ozero => oadd e c ozero
  | oadd e' c' r' as o' =>
      match onoteCompare e e' with
      | Lt => o'
      | Eq => oadd e (S (c + c')) r'
      | Gt => oadd e c o'
      end
  end.

(** Ordinal addition scans the left summand from the right until its final
    surviving term can be merged with, or placed before, the right summand. *)
Fixpoint onoteAdd (a b : ONote) : ONote :=
  match a with
  | ozero => b
  | oadd e c r => onoteAddAux e c (onoteAdd r b)
  end.

Lemma onoteAdd_zero_l : forall a, onoteAdd ozero a = a.
Proof. reflexivity. Qed.

Lemma onoteAdd_oadd : forall e c r b,
  onoteAdd (oadd e c r) b = onoteAddAux e c (onoteAdd r b).
Proof. reflexivity. Qed.

Lemma onoteAddAux_nf : forall e c o,
  NF e -> NF o -> NF (onoteAddAux e c o).
Proof.
  intros e c [|e' c' r'] he ho; simpl in *.
  - now repeat split.
  - destruct ho as [he' [hr' hbelow]].
    unfold onoteAddAux.
    destruct (onoteCompare e e') eqn:hcmp.
    + apply onoteCompare_eq in hcmp. subst e'.
      now repeat split.
    + exact (conj he' (conj hr' hbelow)).
    + repeat split; try assumption.
      now apply onoteCompare_gt_reverse.
Qed.

Theorem onoteAdd_nf : forall a b,
  NF a -> NF b -> NF (onoteAdd a b).
Proof.
  induction a as [|e IHe c r IHr]; intros b ha hb; simpl in *.
  - exact hb.
  - destruct ha as [he [hr _]].
    apply onoteAddAux_nf; [exact he |].
    exact (IHr b hr hb).
Qed.

(** Truncated ordinal subtraction is needed only by the finite/omega split
    used in exponentiation. *)
Fixpoint onoteSub (a b : ONote) : ONote :=
  match a, b with
  | ozero, _ => ozero
  | a', ozero => a'
  | oadd ae ac ar as a', oadd be bc br =>
      match onoteCompare ae be with
      | Lt => ozero
      | Gt => a'
      | Eq =>
          match ac - bc with
          | 0 => if Nat.eqb ac bc then onoteSub ar br else ozero
          | S k => oadd ae k ar
          end
      end
  end.

(** Multiplying positive coefficients [(ac+1)(bc+1)] stores predecessor
    [ac*bc+ac+bc]. *)
Definition coefficientProductPred (ac bc : nat) : nat :=
  ac * bc + ac + bc.

Lemma coefficientProductPred_spec : forall ac bc,
  S (coefficientProductPred ac bc) = S ac * S bc.
Proof. intros ac bc. unfold coefficientProductPred. nia. Qed.

(** Ordinal multiplication follows the CNF of the right operand.  A finite
    right operand scales the leading coefficient of the left operand; a
    positive leading exponent creates a new leading monomial and recurses on
    the right remainder. *)
Fixpoint onoteMul (a b : ONote) : ONote :=
  match a, b with
  | ozero, _ => ozero
  | _, ozero => ozero
  | oadd ae ac ar as a', oadd be bc br =>
      match be with
      | ozero => oadd ae (coefficientProductPred ac bc) ar
      | _ => oadd (onoteAdd ae be) bc (onoteMul a' br)
      end
  end.

Lemma onoteMul_zero_l : forall a, onoteMul ozero a = ozero.
Proof. destruct a; reflexivity. Qed.

Lemma onoteMul_zero_r : forall a, onoteMul a ozero = ozero.
Proof. destruct a; reflexivity. Qed.

(** Split [o] as [omega*q + n]. *)
Fixpoint onoteSplit' (o : ONote) : ONote * nat :=
  match o with
  | ozero => (ozero, 0)
  | oadd e c r =>
      match e with
      | ozero => (ozero, S c)
      | _ =>
          let qr := onoteSplit' r in
          (oadd (onoteSub e onoteOne) c (fst qr), snd qr)
      end
  end.

(** Split [o] as [q + n], where the (possibly zero) [q] is divisible by
    omega and [n] is an ordinary natural number. *)
Fixpoint onoteSplit (o : ONote) : ONote * nat :=
  match o with
  | ozero => (ozero, 0)
  | oadd e c r =>
      match e with
      | ozero => (ozero, S c)
      | _ =>
          let qr := onoteSplit r in
          (oadd e c (fst qr), snd qr)
      end
  end.

(** [onoteScale x o] represents [omega^x * o]. *)
Fixpoint onoteScale (x o : ONote) : ONote :=
  match o with
  | ozero => ozero
  | oadd e c r => oadd (onoteAdd x e) c (onoteScale x r)
  end.

(** Right multiplication by an ordinary natural. *)
Definition onoteMulNat (o : ONote) (n : nat) : ONote :=
  match o, n with
  | ozero, _ => ozero
  | _, 0 => ozero
  | oadd e c r, S k =>
      oadd e (coefficientProductPred c k) r
  end.

(** Auxiliary finite part of ordinal exponentiation.  Its two natural
    arguments are deliberately separate: this is the terminating recurrence
    used by Mathlib's verified normalizer. *)
Fixpoint onotePowAux (e a0 a : ONote) (k m : nat) : ONote :=
  match m with
  | 0 => ozero
  | S m' =>
      match k with
      | 0 => oadd e m' ozero
      | S k' =>
          onoteAdd
            (onoteScale (onoteAdd e (onoteMulNat a0 k')) a)
            (onotePowAux e a0 a k' (S m'))
      end
  end.

(** Exponentiation after the base has been split into its omega-divisible
    and finite parts. *)
Definition onotePowAux2 (exponent : ONote)
    (baseSplit : ONote * nat) : ONote :=
  match baseSplit with
  | (ozero, 0) =>
      match exponent with
      | ozero => onoteOne
      | _ => ozero
      end
  | (ozero, 1) => onoteOne
  | (ozero, S m) =>
      let qk := onoteSplit' exponent in
      (* This branch is reached for finite base [S m >= 2]; the preceding
         pattern has already consumed [m=0]. *)
      oadd (fst qk) (Nat.pred (Nat.pow (S m) (snd qk))) ozero
  | (oadd a0 ac ar as a, m) =>
      let bk := onoteSplit exponent in
      match snd bk with
      | 0 => oadd (onoteMul a0 (fst bk)) 0 ozero
      | S k =>
          let eb := onoteMul a0 (fst bk) in
          onoteAdd
            (onoteScale (onoteAdd eb (onoteMulNat a0 k)) a)
            (onotePowAux eb a0 (onoteMulNat a m) k m)
      end
  end.

Definition onotePow (base exponent : ONote) : ONote :=
  onotePowAux2 exponent (onoteSplit base).

(** Result-first graph predicates are convenient both for formula
    correctness statements and for functionality theorems. *)
Definition OrdinalLT (a b : nat) : Prop :=
  ValidOrdinalCode a /\ ValidOrdinalCode b /\
  onoteCompare (decode a) (decode b) = Lt.

Definition addCode (a b : nat) : nat :=
  encode (onoteAdd (decode a) (decode b)).

Definition mulCode (a b : nat) : nat :=
  encode (onoteMul (decode a) (decode b)).

Definition powCode (a b : nat) : nat :=
  encode (onotePow (decode a) (decode b)).

Definition OrdinalAdd (z a b : nat) : Prop :=
  ValidOrdinalCode a /\ ValidOrdinalCode b /\ z = addCode a b.

Definition OrdinalMul (z a b : nat) : Prop :=
  ValidOrdinalCode a /\ ValidOrdinalCode b /\ z = mulCode a b.

Definition OrdinalPow (z a b : nat) : Prop :=
  ValidOrdinalCode a /\ ValidOrdinalCode b /\ z = powCode a b.

Lemma decode_addCode : forall a b,
  decode (addCode a b) = onoteAdd (decode a) (decode b).
Proof. intros a b. unfold addCode. apply decode_encode. Qed.

Lemma decode_mulCode : forall a b,
  decode (mulCode a b) = onoteMul (decode a) (decode b).
Proof. intros a b. unfold mulCode. apply decode_encode. Qed.

Lemma decode_powCode : forall a b,
  decode (powCode a b) = onotePow (decode a) (decode b).
Proof. intros a b. unfold powCode. apply decode_encode. Qed.

Theorem ordinalAdd_functional : forall z z' a b,
  OrdinalAdd z a b -> OrdinalAdd z' a b -> z = z'.
Proof. intros z z' a b [_ [_ hz]] [_ [_ hz']]. congruence. Qed.

Theorem ordinalMul_functional : forall z z' a b,
  OrdinalMul z a b -> OrdinalMul z' a b -> z = z'.
Proof. intros z z' a b [_ [_ hz]] [_ [_ hz']]. congruence. Qed.

Theorem ordinalPow_functional : forall z z' a b,
  OrdinalPow z a b -> OrdinalPow z' a b -> z = z'.
Proof. intros z z' a b [_ [_ hz]] [_ [_ hz']]. congruence. Qed.

Theorem ordinalAdd_exists_unique : forall a b,
  ValidOrdinalCode a -> ValidOrdinalCode b ->
  exists! z, OrdinalAdd z a b.
Proof.
  intros a b ha hb. exists (addCode a b). split.
  - now repeat split.
  - intros z [_ [_ hz]]. symmetry. exact hz.
Qed.

Theorem ordinalMul_exists_unique : forall a b,
  ValidOrdinalCode a -> ValidOrdinalCode b ->
  exists! z, OrdinalMul z a b.
Proof.
  intros a b ha hb. exists (mulCode a b). split.
  - now repeat split.
  - intros z [_ [_ hz]]. symmetry. exact hz.
Qed.

Theorem ordinalPow_exists_unique : forall a b,
  ValidOrdinalCode a -> ValidOrdinalCode b ->
  exists! z, OrdinalPow z a b.
Proof.
  intros a b ha hb. exists (powCode a b). split.
  - now repeat split.
  - intros z [_ [_ hz]]. symmetry. exact hz.
Qed.

End PAEpsilonZero.
