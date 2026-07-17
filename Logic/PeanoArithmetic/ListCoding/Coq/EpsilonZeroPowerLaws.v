(**
  Structural exponentiation laws for the epsilon-zero notation normalizer.

  The executable power algorithm is organized around [onoteSplit] and
  [onoteSplit'].  This companion module first records the small algebra of
  those decompositions.  Keeping it separate from [EpsilonZeroLaws] lets the
  already-audited closure and elementary-identity layer remain stable while
  the longer power proofs are developed incrementally.
*)

From Stdlib Require Import Arith Lia Bool PeanoNat.
From PAListCoding Require Import EpsilonZero EpsilonZeroLaws.

Module PAEpsilonZeroPowerLaws.

Import PAEpsilonZero PAEpsilonZeroLaws.

(** * Canonical finite notations *)

Lemma onoteSplit_onoteNat : forall n,
  onoteSplit (onoteNat n) = (ozero, n).
Proof. intros [|n]; reflexivity. Qed.

Lemma onoteSplit'_onoteNat : forall n,
  onoteSplit' (onoteNat n) = (ozero, n).
Proof. intros [|n]; reflexivity. Qed.

Lemma onoteAdd_onoteNat : forall m n,
  onoteAdd (onoteNat m) (onoteNat n) = onoteNat (m + n).
Proof.
  intros [|m] [|n].
  - reflexivity.
  - reflexivity.
  - cbn [onoteNat onoteAdd onoteAddAux].
    now rewrite Nat.add_0_r.
  - cbn [onoteNat onoteAdd]. unfold onoteAddAux.
    rewrite onoteCompare_refl. cbn.
    replace (m + S n) with (S (m + n)) by lia.
    reflexivity.
Qed.

Lemma onoteMul_onoteNat : forall o n,
  onoteMul o (onoteNat n) = onoteMulNat o n.
Proof. intros [|e c r] [|n]; reflexivity. Qed.

Lemma onoteNat_add_one : forall n,
  onoteNat (S n) = onoteAdd (onoteNat n) onoteOne.
Proof.
  intro n. change (onoteNat (S n) =
    onoteAdd (onoteNat n) (onoteNat 1)).
  rewrite onoteAdd_onoteNat, Nat.add_1_r. reflexivity.
Qed.

(** * Stable omega-divisible parts *)

(** Splitting an already extracted omega-divisible part is idempotent.  This
    is a raw structural fact; normality is needed only for reconstruction. *)
Lemma onoteSplit_output_fixed : forall o q n,
  onoteSplit o = (q, n) -> onoteSplit q = (q, 0).
Proof.
  induction o as [|e IHe c r IHr]; intros q n hsplit.
  - cbn [onoteSplit] in hsplit. inversion hsplit. reflexivity.
  - destruct e as [|ee ec er].
    + cbn [onoteSplit] in hsplit. inversion hsplit. reflexivity.
    + cbn [onoteSplit] in hsplit.
      destruct (onoteSplit r) as [r' k] eqn:hr.
      inversion hsplit; subst q n.
      cbn [onoteSplit].
      rewrite (IHr r' k eq_refl). reflexivity.
Qed.

(** The comparison of two exponents is unchanged after prefixing both by the
    same normal ordinal.  The strict cases use the monotonicity theorem from
    [EpsilonZeroLaws]; equality uses the raw associativity scanner. *)
Lemma onoteCompare_add_left : forall prefix a b,
  NF prefix -> NF a -> NF b ->
  onoteCompare (onoteAdd prefix a) (onoteAdd prefix b) =
  onoteCompare a b.
Proof.
  intros prefix a b hp ha hb.
  destruct (onoteCompare a b) eqn:hab.
  - apply onoteCompare_eq in hab. subst b.
    apply onoteCompare_refl.
  - now apply onoteAdd_strict_right.
  - apply onoteCompare_gt_reverse in hab.
    pose proof (onoteAdd_strict_right prefix b a hab) as hrev.
    apply onoteCompare_lt_reverse in hrev. exact hrev.
Qed.

(** Scaling by zero is already available as [onoteScale_zero].  Composition
    is the other basic identity needed to reason about omega-divisible
    prefixes. *)
Lemma onoteScale_compose : forall x y o,
  onoteScale x (onoteScale y o) =
  onoteScale (onoteAdd x y) o.
Proof.
  intros x y o. induction o as [|e IHe c r IHr]; [reflexivity |].
  cbn [onoteScale]. rewrite onoteAdd_assoc, IHr. reflexivity.
Qed.

Definition onoteHead (o : ONote) : ONote :=
  match o with
  | ozero => ozero
  | oadd e _ _ => e
  end.

(** Right multiplication by an omega-divisible notation depends only on the
    leading exponent of the nonzero left factor.  This equation is exactly
    the branch used by the power algorithm at limit exponents. *)
Lemma onoteMul_split_fixed : forall p q,
  p <> ozero -> onoteSplit q = (q, 0) ->
  onoteMul p q = onoteScale (onoteHead p) q.
Proof.
  intros p q. revert p.
  induction q as [|e IHe c r IHr]; intros p hp hfixed.
  - destruct p; reflexivity.
  - destruct e as [|ee ec er].
    + cbn [onoteSplit] in hfixed. discriminate.
    + cbn [onoteSplit] in hfixed.
      destruct (onoteSplit r) as [r' n] eqn:hr.
      inversion hfixed; subst r' n.
      destruct p as [|pe pc pr]; [contradiction |].
      cbn [onoteMul onoteScale onoteHead].
      rewrite (IHr (oadd pe pc pr)); [reflexivity | discriminate |].
      reflexivity.
Qed.

(** Appending a finite tail changes only the natural remainder of a stable
    omega-divisible prefix.  The normality hypothesis ensures that the
    addition scanner really rebuilds each preserved CNF node. *)
Lemma onoteSplit_add_nat_fixed : forall q n,
  NF q -> onoteSplit q = (q, 0) ->
  onoteSplit (onoteAdd q (onoteNat n)) = (q, n).
Proof.
  induction q as [|e IHe c r IHr]; intros n hq hfixed.
  - cbn [onoteAdd]. apply onoteSplit_onoteNat.
  - pose proof hq as hqFull.
    destruct hq as [he [hr htop]].
    destruct e as [|ee ec er].
    + cbn [onoteSplit] in hfixed. discriminate.
    + cbn [onoteSplit] in hfixed.
      destruct (onoteSplit r) as [r' k] eqn:hsplitR.
      inversion hfixed; subst r' k.
      assert (hnfTail : NF (onoteAdd r (onoteNat n))).
      { apply onoteAdd_nf; [exact hr | apply onoteNat_nf]. }
      assert (htopNat : TopBelow (oadd ee ec er) (onoteNat n)).
      { destruct n; [exact I | reflexivity]. }
      assert (htopTail :
        TopBelow (oadd ee ec er) (onoteAdd r (onoteNat n))).
      {
        apply onoteAdd_topBelow.
        - exact hr.
        - apply onoteNat_nf.
        - exact htop.
        - exact htopNat.
      }
      assert (hrebuilt : NF (oadd (oadd ee ec er) c
        (onoteAdd r (onoteNat n)))).
      { exact (conj he (conj hnfTail htopTail)). }
      cbn [onoteAdd].
      rewrite (onoteAddAux_reconstruct_nf _ _ _ hrebuilt).
      cbn [onoteSplit].
      rewrite (IHr n hr eq_refl). reflexivity.
Qed.

Lemma onoteSplit_add_nat : forall a q k n,
  NF a -> onoteSplit a = (q, k) ->
  onoteSplit (onoteAdd a (onoteNat n)) = (q, k + n).
Proof.
  intros a q k n ha hsplit.
  pose proof (onoteSplit_nf a q k ha hsplit) as hq.
  pose proof (onoteSplit_output_fixed a q k hsplit) as hfixed.
  rewrite (onoteSplit_reconstruct a q k ha hsplit).
  rewrite onoteAdd_assoc, onoteAdd_onoteNat.
  now apply onoteSplit_add_nat_fixed.
Qed.

(** The omega-quotient split has the same finite-tail behavior.  Unlike
    [onoteSplit], its first component need not itself be split-fixed, so this
    version is proved directly along the source notation. *)
Lemma onoteSplit'_add_nat : forall a q k n,
  NF a -> onoteSplit' a = (q, k) ->
  onoteSplit' (onoteAdd a (onoteNat n)) = (q, k + n).
Proof.
  induction a as [|e IHe c r IHr]; intros q k n ha hsplit.
  - cbn [onoteSplit'] in hsplit. inversion hsplit; subst q k.
    rewrite onoteAdd_zero_l, onoteSplit'_onoteNat. reflexivity.
  - pose proof ha as haFull.
    destruct ha as [he [hr htop]].
    destruct e as [|ee ec er].
    + assert (hr0 : r = ozero).
      { now apply NF_zero_exponent_tail with (c := c). }
      subst r. cbn [onoteSplit'] in hsplit.
      inversion hsplit; subst q k.
      change (onoteSplit'
        (onoteAdd (onoteNat (S c)) (onoteNat n)) =
        (ozero, S c + n)).
      rewrite onoteAdd_onoteNat, onoteSplit'_onoteNat. reflexivity.
    + cbn [onoteSplit'] in hsplit.
      destruct (onoteSplit' r) as [r' j] eqn:hsplitR.
      inversion hsplit; subst q k.
      assert (hnfTail : NF (onoteAdd r (onoteNat n))).
      { apply onoteAdd_nf; [exact hr | apply onoteNat_nf]. }
      assert (htopNat : TopBelow (oadd ee ec er) (onoteNat n)).
      { destruct n; [exact I | reflexivity]. }
      assert (htopTail :
        TopBelow (oadd ee ec er) (onoteAdd r (onoteNat n))).
      {
        apply onoteAdd_topBelow.
        - exact hr.
        - apply onoteNat_nf.
        - exact htop.
        - exact htopNat.
      }
      assert (hrebuilt : NF (oadd (oadd ee ec er) c
        (onoteAdd r (onoteNat n)))).
      { exact (conj he (conj hnfTail htopTail)). }
      cbn [onoteAdd].
      rewrite (onoteAddAux_reconstruct_nf _ _ _ hrebuilt).
      cbn [onoteSplit'].
      rewrite (IHr r' j n hr eq_refl). reflexivity.
Qed.

(** * Successor exponent: finite bases *)

Lemma natPow_positive : forall base exponent,
  0 < base -> 0 < Nat.pow base exponent.
Proof.
  intros base exponent hbase. induction exponent as [|exponent IH].
  - cbn [Nat.pow]. lia.
  - cbn [Nat.pow]. nia.
Qed.

(** Multiplying predecessor-stored positive coefficients stores the
    predecessor of their ordinary product. *)
Lemma coefficientProductPred_pred : forall x y,
  0 < x -> 0 < y ->
  coefficientProductPred (Nat.pred x) (Nat.pred y) =
  Nat.pred (x * y).
Proof.
  intros [|x] [|y] hx hy.
  - lia.
  - lia.
  - lia.
  - cbn [Nat.pred]. unfold coefficientProductPred.
    replace (S x * S y) with (S (x * y + x + y)) by nia.
    reflexivity.
Qed.

Lemma onotePow_succ_finite : forall exponent base,
  NF exponent -> 2 <= base ->
  onotePow (onoteNat base) (onoteAdd exponent onoteOne) =
  onoteMul (onotePow (onoteNat base) exponent) (onoteNat base).
Proof.
  intros exponent [|[|base]] hexponent hbase; try lia.
  remember (onoteSplit' exponent) as exponentSplit eqn:hsplit.
  destruct exponentSplit as [q k].
  symmetry in hsplit.
  assert (hsplitSucc :
    onoteSplit' (onoteAdd exponent onoteOne) = (q, S k)).
  {
    change onoteOne with (onoteNat 1).
    pose proof (onoteSplit'_add_nat exponent q k 1
      hexponent hsplit) as h.
    now rewrite Nat.add_1_r in h.
  }
  unfold onotePow.
  rewrite !onoteSplit_onoteNat.
  cbn [onotePowAux2].
  rewrite hsplitSucc, hsplit.
  cbn [onoteMul onoteNat]. cbn.
  change (oadd q (Nat.pred (Nat.pow (S (S base)) (S k))) ozero =
    oadd q
      (coefficientProductPred
        (Nat.pred (Nat.pow (S (S base)) k))
        (Nat.pred (S (S base)))) ozero).
  rewrite coefficientProductPred_pred.
  - rewrite Nat.pow_succ_r by lia.
    f_equal. now rewrite Nat.mul_comm.
  - apply natPow_positive. lia.
  - lia.
Qed.

(** * Successor exponent: zero, one, and the finite-multiple helper *)

Lemma onotePow_zero_base_nonzero : forall exponent,
  exponent <> ozero -> onotePow ozero exponent = ozero.
Proof. intros [|e c r] h; [contradiction | reflexivity]. Qed.

Lemma onotePow_one_base : forall exponent,
  onotePow onoteOne exponent = onoteOne.
Proof. intro exponent. reflexivity. Qed.

Lemma onoteAdd_one_nonzero_nf : forall exponent,
  NF exponent -> onoteAdd exponent onoteOne <> ozero.
Proof.
  intros exponent hexponent hzero.
  pose proof (onoteCompare_add_nonzero_right exponent onoteOne
    hexponent ltac:(discriminate)) as hstrict.
  rewrite hzero in hstrict. destruct exponent; discriminate.
Qed.

Lemma onotePow_succ_zero : forall exponent,
  NF exponent ->
  onotePow ozero (onoteAdd exponent onoteOne) =
  onoteMul (onotePow ozero exponent) ozero.
Proof.
  intros exponent hexponent.
  rewrite onotePow_zero_base_nonzero.
  - rewrite onoteMul_zero_r. reflexivity.
  - now apply onoteAdd_one_nonzero_nf.
Qed.

Lemma onotePow_succ_one : forall exponent,
  onotePow onoteOne (onoteAdd exponent onoteOne) =
  onoteMul (onotePow onoteOne exponent) onoteOne.
Proof.
  intro exponent. rewrite !onotePow_one_base, onoteMul_one_r.
  reflexivity.
Qed.

Lemma onoteMulNat_succ_nf : forall o n,
  NF o ->
  onoteMulNat o (S n) =
  onoteAdd (onoteMulNat o n) o.
Proof.
  intros [|e c r] [|n] ho.
  - reflexivity.
  - reflexivity.
  - cbn [onoteMulNat onoteAdd].
    now rewrite coefficientProductPred_zero_r.
  -
  pose proof ho as hoFull.
  assert (hmul : NF (onoteMulNat (oadd e c r) (S n))).
  { now apply onoteMulNat_nf. }
  cbn [onoteMulNat].
  rewrite (onoteAdd_nodes e (coefficientProductPred c n) r
    e c r hmul hoFull), onoteCompare_refl.
  replace (coefficientProductPred c (S n)) with
    (S (coefficientProductPred c n + c)) by
    (unfold coefficientProductPred; nia).
  reflexivity.
Qed.

Lemma onoteMulNat_scale : forall x o n,
  onoteMulNat (onoteScale x o) n =
  onoteScale x (onoteMulNat o n).
Proof. intros x [|e c r] [|n]; reflexivity. Qed.

(** A finite right multiple changes only the leading coefficient of a normal
    sum whose right summand lies below the scaled left summand.  This is the
    syntactic counterpart of `(P + r) * n = P * n + r` for such CNFs. *)
Lemma onoteMulNat_scale_add : forall x a0 ac ar r m,
  NF x -> NF (oadd a0 ac ar) -> NF r ->
  TopBelow (onoteAdd x a0) r ->
  onoteMulNat
    (onoteAdd (onoteScale x (oadd a0 ac ar)) r) (S m) =
  onoteAdd
    (onoteScale x
      (onoteMulNat (oadd a0 ac ar) (S m))) r.
Proof.
  intros x a0 ac ar [|re rc rr] m hx ha hr hbelow.
  - assert (hscale : NF (onoteScale x (oadd a0 ac ar))).
    { apply onoteScale_nf; assumption. }
    assert (hmulA : NF (onoteMulNat (oadd a0 ac ar) (S m))).
    { now apply onoteMulNat_nf. }
    assert (hscaleMul :
      NF (onoteScale x (onoteMulNat (oadd a0 ac ar) (S m)))).
    { apply onoteScale_nf; assumption. }
    rewrite (onoteAdd_zero_r_nf _ hscale),
      (onoteAdd_zero_r_nf _ hscaleMul).
    apply onoteMulNat_scale.
  - assert (hscale : NF (onoteScale x (oadd a0 ac ar))).
    { apply onoteScale_nf; assumption. }
    assert (hmulA : NF (onoteMulNat (oadd a0 ac ar) (S m))).
    { now apply onoteMulNat_nf. }
    assert (hscaleMul :
      NF (onoteScale x (onoteMulNat (oadd a0 ac ar) (S m)))).
    { apply onoteScale_nf; assumption. }
    cbn [TopBelow] in hbelow.
    apply onoteCompare_lt_reverse in hbelow.
    cbn [onoteScale].
    rewrite (onoteAdd_nodes (onoteAdd x a0) ac (onoteScale x ar)
      re rc rr hscale hr), hbelow.
    cbn [onoteMulNat].
    cbn [onoteScale].
    rewrite (onoteAdd_nodes (onoteAdd x a0)
      (coefficientProductPred ac m) (onoteScale x ar)
      re rc rr hscaleMul hr), hbelow.
    reflexivity.
Qed.

(** The recursive finite-power tail has a predictable leading exponent.
    This strengthened invariant is what the closure proof alone does not
    expose: each successor step inserts one strictly larger scaled block. *)
Lemma onotePowAux_head : forall e a0 ac ar k m,
  NF e -> NF (oadd a0 ac ar) -> a0 <> ozero ->
  exists c r,
    onotePowAux e a0 (oadd a0 ac ar) k (S m) =
    oadd (onoteAdd e (onoteMulNat a0 k)) c r.
Proof.
  intros e a0 ac ar k. induction k as [|k IH];
    intros m he ha ha0.
  - cbn [onotePowAux].
    rewrite onoteMulNat_zero_r, onoteAdd_zero_r_nf by exact he.
    now exists m, ozero.
  - pose proof ha as haFull.
    destruct ha as [ha0NF [har htopA]].
    destruct (IH m he haFull ha0) as [c [r haux]].
    cbn [onotePowAux]. rewrite haux.
    set (x := onoteAdd e (onoteMulNat a0 k)).
    assert (hx : NF x).
    {
      unfold x. apply onoteAdd_nf; [exact he |].
      now apply onoteMulNat_nf.
    }
    assert (hscale : NF (onoteScale x (oadd a0 ac ar))).
    { apply onoteScale_nf; [exact hx | exact haFull]. }
    assert (hauxNF : NF (oadd x c r)).
    {
      unfold x. rewrite <- haux. apply onotePowAux_nf.
      - exact he.
      - exact ha0NF.
      - exact haFull.
    }
    assert (hstrict : onoteCompare x (onoteAdd x a0) = Lt).
    { now apply onoteCompare_add_nonzero_right. }
    apply onoteCompare_lt_reverse in hstrict.
    cbn [onoteScale].
    rewrite (onoteAdd_nodes (onoteAdd x a0) ac (onoteScale x ar)
      x c r hscale hauxNF), hstrict.
    rewrite (onoteMulNat_succ_nf a0 k ha0NF), <- onoteAdd_assoc.
    unfold x. now exists ac, (onoteAdd (onoteScale x ar) (oadd x c r)).
Qed.

Lemma onotePowAux_m_zero : forall e a0 a k,
  onotePowAux e a0 a k 0 = ozero.
Proof. intros e a0 a [|k]; reflexivity. Qed.

(** The whole positive finite-exponent branch has the next expected head.
    The `m=0` case has no auxiliary tail; for `m>0`, [onotePowAux_head]
    supplies the smaller head that is retained beneath the scaled block. *)
Lemma onotePow_branch_head : forall e a0 ac ar k m,
  NF e -> NF (oadd a0 ac ar) -> a0 <> ozero ->
  exists c r,
    onoteAdd
      (onoteScale (onoteAdd e (onoteMulNat a0 k))
        (oadd a0 ac ar))
      (onotePowAux e a0
        (onoteMulNat (oadd a0 ac ar) m) k m) =
    oadd (onoteAdd e (onoteMulNat a0 (S k))) c r.
Proof.
  intros e a0 ac ar k [|m] he ha ha0.
  - cbn [onoteMulNat]. rewrite onotePowAux_m_zero.
    rewrite onoteAdd_zero_r_nf.
    + cbn [onoteScale].
      rewrite (onoteMulNat_succ_nf a0 k (proj1 ha)),
        <- onoteAdd_assoc.
      now exists ac, (onoteScale
        (onoteAdd e (onoteMulNat a0 k)) ar).
    + apply onoteScale_nf.
      * apply onoteAdd_nf; [exact he |].
        apply onoteMulNat_nf. exact (proj1 ha).
      * exact ha.
  - pose proof ha as haFull.
    destruct ha as [ha0NF [har htopA]].
    cbn [onoteMulNat].
    destruct (onotePowAux_head e a0
      (coefficientProductPred ac m) ar k m he
      haFull ha0) as [c [r haux]].
    rewrite haux.
    set (x := onoteAdd e (onoteMulNat a0 k)).
    assert (hx : NF x).
    {
      unfold x. apply onoteAdd_nf; [exact he |].
      now apply onoteMulNat_nf.
    }
    assert (hscale : NF (onoteScale x (oadd a0 ac ar))).
    { apply onoteScale_nf; [exact hx | exact haFull]. }
    assert (hauxNF : NF (oadd x c r)).
    {
      unfold x. rewrite <- haux. apply onotePowAux_nf.
      - exact he.
      - exact ha0NF.
      - exact haFull.
    }
    assert (hstrict : onoteCompare x (onoteAdd x a0) = Lt).
    { now apply onoteCompare_add_nonzero_right. }
    apply onoteCompare_lt_reverse in hstrict.
    cbn [onoteScale].
    rewrite (onoteAdd_nodes (onoteAdd x a0) ac (onoteScale x ar)
      x c r hscale hauxNF), hstrict.
    rewrite (onoteMulNat_succ_nf a0 k ha0NF), <- onoteAdd_assoc.
    unfold x. now exists ac, (onoteAdd (onoteScale x ar) (oadd x c r)).
Qed.

(** Finite multiplication of the current positive branch is literally the
    next [onotePowAux] branch.  Its proof is the reason for isolating
    [onoteMulNat_scale_add]. *)
Lemma onoteMulNat_pow_branch : forall e a0 ac ar k m,
  NF e -> NF (oadd a0 ac ar) -> a0 <> ozero ->
  onoteMulNat
    (onoteAdd
      (onoteScale (onoteAdd e (onoteMulNat a0 k))
        (oadd a0 ac ar))
      (onotePowAux e a0
        (onoteMulNat (oadd a0 ac ar) m) k m)) m =
  onotePowAux e a0
    (onoteMulNat (oadd a0 ac ar) m) (S k) m.
Proof.
  intros e a0 ac ar k [|m] he ha ha0.
  - rewrite !onotePowAux_m_zero. apply onoteMulNat_zero_r.
  -
  set (x := onoteAdd e (onoteMulNat a0 k)).
  set (tail := onotePowAux e a0
    (onoteMulNat (oadd a0 ac ar) (S m)) k (S m)).
  assert (hx : NF x).
  {
    unfold x. apply onoteAdd_nf; [exact he |].
    now apply onoteMulNat_nf; exact (proj1 ha).
  }
  assert (htail : NF tail).
  {
    unfold tail. apply onotePowAux_nf.
    - exact he.
    - exact (proj1 ha).
    - now apply onoteMulNat_nf.
  }
  assert (htop : TopBelow (onoteAdd x a0) tail).
  {
    unfold tail.
    cbn [onoteMulNat].
    destruct (onotePowAux_head e a0
      (coefficientProductPred ac m) ar k m he
      ha ha0) as [c [r haux]].
    rewrite haux. cbn [TopBelow].
    unfold x. now apply onoteCompare_add_nonzero_right.
  }
  change (onoteMulNat
    (onoteAdd (onoteScale x (oadd a0 ac ar)) tail) (S m) =
    onotePowAux e a0
      (onoteMulNat (oadd a0 ac ar) (S m)) (S k) (S m)).
  rewrite (onoteMulNat_scale_add x a0 ac ar tail m
    hx ha htail htop).
  reflexivity.
Qed.

(** * Successor exponent: infinite bases *)

Theorem onotePow_succ_infinite_nf :
  forall base exponent a0 ac ar m,
    NF base -> NF exponent ->
    onoteSplit base = (oadd a0 ac ar, m) ->
    onotePow base (onoteAdd exponent onoteOne) =
    onoteMul (onotePow base exponent) base.
Proof.
  intros base exponent a0 ac ar m hbase hexponent hbaseSplit.
  pose proof (onoteSplit_nf base (oadd a0 ac ar) m
    hbase hbaseSplit) as homega.
  pose proof (onoteSplit_output_fixed base (oadd a0 ac ar) m
    hbaseSplit) as hfixed.
  assert (ha0 : a0 <> ozero).
  {
    intro ha0. subst a0.
    cbn [onoteSplit] in hfixed. discriminate.
  }
  pose proof (onoteSplit_reconstruct base (oadd a0 ac ar) m
    hbase hbaseSplit) as hbaseReconstruct.
  remember (onoteSplit exponent) as exponentSplit eqn:hexponentSplit.
  destruct exponentSplit as [b k]. symmetry in hexponentSplit.
  pose proof (onoteSplit_nf exponent b k hexponent
    hexponentSplit) as hb.
  assert (hexponentSucc :
    onoteSplit (onoteAdd exponent onoteOne) = (b, S k)).
  {
    change onoteOne with (onoteNat 1).
    pose proof (onoteSplit_add_nat exponent b k 1
      hexponent hexponentSplit) as h.
    now rewrite Nat.add_1_r in h.
  }
  assert (heb : NF (onoteMul a0 b)).
  { apply onoteMul_nf; [exact (proj1 homega) | exact hb]. }
  pose proof (onotePow_nf base exponent hbase hexponent) as hpow.
  unfold onotePow in hpow.
  rewrite hbaseSplit in hpow.
  unfold onotePow.
  rewrite hbaseSplit, hbaseReconstruct.
  cbn [onotePowAux2].
  rewrite hexponentSucc, hexponentSplit.
  destruct k as [|k].
  - change (onoteAdd
      (onoteScale
        (onoteAdd (onoteMul a0 b) (onoteMulNat a0 0))
        (oadd a0 ac ar))
      (onotePowAux (onoteMul a0 b) a0
        (onoteMulNat (oadd a0 ac ar) m) 0 m) =
      onoteMul (oadd (onoteMul a0 b) 0 ozero)
        (onoteAdd (oadd a0 ac ar) (onoteNat m))).
    cbn [onotePowAux2] in hpow. rewrite hexponentSplit in hpow.
    change (NF (oadd (onoteMul a0 b) 0 ozero)) in hpow.
    rewrite onoteMulNat_zero_r, onoteAdd_zero_r_nf by exact heb.
    rewrite (onoteMul_add
      (oadd (onoteMul a0 b) 0 ozero)
      (oadd a0 ac ar) (onoteNat m)
      hpow homega (onoteNat_nf m)).
    rewrite (onoteMul_split_fixed
      (oadd (onoteMul a0 b) 0 ozero) (oadd a0 ac ar)
      ltac:(discriminate) hfixed).
    rewrite onoteMul_onoteNat, onotePowAux_k_zero.
    destruct m as [|m]; [reflexivity |].
    cbn [onoteMulNat].
    rewrite coefficientProductPred_zero_l. reflexivity.
  -
    cbn [onotePowAux2] in hpow. rewrite hexponentSplit in hpow.
    set (eb := onoteMul a0 b).
    set (current := onoteAdd
      (onoteScale (onoteAdd eb (onoteMulNat a0 k))
        (oadd a0 ac ar))
      (onotePowAux eb a0
        (onoteMulNat (oadd a0 ac ar) m) k m)).
    change (onoteAdd
      (onoteScale (onoteAdd eb (onoteMulNat a0 (S k)))
        (oadd a0 ac ar))
      (onotePowAux eb a0
        (onoteMulNat (oadd a0 ac ar) m) (S k) m) =
      onoteMul current
        (onoteAdd (oadd a0 ac ar) (onoteNat m))).
    change (NF current) in hpow.
    assert (hcurrent : NF current).
    { unfold current, eb in *. exact hpow. }
    rewrite (onoteMul_add current (oadd a0 ac ar) (onoteNat m)
      hcurrent homega (onoteNat_nf m)).
    assert (hcurrentHead : exists c r,
      current = oadd (onoteAdd eb (onoteMulNat a0 (S k))) c r).
    {
      unfold current. apply onotePow_branch_head.
      - unfold eb. exact heb.
      - exact homega.
      - exact ha0.
    }
    destruct hcurrentHead as [c [r hcurrentHead]].
    assert (hmulOmega :
      onoteMul current (oadd a0 ac ar) =
      onoteScale (onoteAdd eb (onoteMulNat a0 (S k)))
        (oadd a0 ac ar)).
    {
      rewrite hcurrentHead.
      apply onoteMul_split_fixed; [discriminate | exact hfixed].
    }
    rewrite hmulOmega, onoteMul_onoteNat.
    unfold current.
    rewrite (onoteMulNat_pow_branch eb a0 ac ar k m
      ltac:(unfold eb; exact heb) homega ha0).
    reflexivity.
Qed.

(** The four base classes used by [onotePowAux2] now agree on the ordinary
    successor equation. *)
Theorem onotePow_succ_nf : forall base exponent,
  NF base -> NF exponent ->
  onotePow base (onoteAdd exponent onoteOne) =
  onoteMul (onotePow base exponent) base.
Proof.
  intros base exponent hbase hexponent.
  remember (onoteSplit base) as baseSplit eqn:hbaseSplit.
  destruct baseSplit as [q n]. symmetry in hbaseSplit.
  pose proof (onoteSplit_reconstruct base q n hbase hbaseSplit)
    as hbaseReconstruct.
  destruct q as [|a0 ac ar].
  - rewrite onoteAdd_zero_l in hbaseReconstruct.
    subst base. destruct n as [|[|n]].
    + now apply onotePow_succ_zero.
    + apply onotePow_succ_one.
    + apply onotePow_succ_finite; [exact hexponent | lia].
  - now apply onotePow_succ_infinite_nf with
      (a0 := a0) (ac := ac) (ar := ar) (m := n).
Qed.

Theorem powCode_succCode : forall a b,
  ValidOrdinalCode a -> ValidOrdinalCode b ->
  powCode a (addCode b oneCode) =
  mulCode (powCode a b) a.
Proof.
  intros a b ha hb. apply decode_injective.
  rewrite decode_powCode, decode_addCode, decode_oneCode,
    decode_mulCode, decode_powCode.
  apply onotePow_succ_nf; assumption.
Qed.

(** * Split algebra for arbitrary right summands *)

(** An operationally omega-divisible notation has no finite-exponent term.
    This structural predicate is equivalent to being a fixed point of
    [onoteSplit], and is much easier to preserve through [onoteAdd]. *)
Fixpoint OmegaDivisible (o : ONote) : Prop :=
  match o with
  | ozero => True
  | oadd e _ r => e <> ozero /\ OmegaDivisible r
  end.

Lemma omegaDivisible_split_fixed : forall o,
  OmegaDivisible o -> onoteSplit o = (o, 0).
Proof.
  induction o as [|e IHe c r IHr]; intro hdiv; [reflexivity |].
  destruct hdiv as [he hr]. destruct e as [|ee ec er]; [contradiction |].
  cbn [onoteSplit]. rewrite (IHr hr). reflexivity.
Qed.

Lemma split_fixed_omegaDivisible : forall o,
  onoteSplit o = (o, 0) -> OmegaDivisible o.
Proof.
  induction o as [|e IHe c r IHr]; intro hfixed; [exact I |].
  destruct e as [|ee ec er].
  - cbn [onoteSplit] in hfixed. discriminate.
  - cbn [onoteSplit] in hfixed.
    destruct (onoteSplit r) as [r' n] eqn:hr.
    inversion hfixed; subst r' n.
    split; [discriminate |]. now apply IHr.
Qed.

Lemma omegaDivisible_add : forall a b,
  OmegaDivisible a -> OmegaDivisible b ->
  OmegaDivisible (onoteAdd a b).
Proof.
  induction a as [|e IHe c r IHr]; intros b ha hb.
  - exact hb.
  - destruct ha as [he hr]. cbn [onoteAdd].
    pose proof (IHr b hr hb) as htail.
    destruct (onoteAdd r b) as [|te tc tr] eqn:hsum.
    + cbn [onoteAddAux]. now split.
    + destruct htail as [hte htr]. unfold onoteAddAux.
      destruct (onoteCompare e te).
      * now split.
      * exact (conj hte htr).
      * exact (conj he (conj hte htr)).
Qed.

Lemma onoteSplit_add_fixed : forall a b,
  onoteSplit a = (a, 0) -> onoteSplit b = (b, 0) ->
  onoteSplit (onoteAdd a b) = (onoteAdd a b, 0).
Proof.
  intros a b ha hb. apply omegaDivisible_split_fixed.
  apply omegaDivisible_add.
  - now apply split_fixed_omegaDivisible.
  - now apply split_fixed_omegaDivisible.
Qed.

(** A genuinely omega-divisible normal form absorbs every finite prefix. *)
Lemma onoteAdd_nat_absorb_fixed : forall n q,
  NF q -> q <> ozero -> onoteSplit q = (q, 0) ->
  onoteAdd (onoteNat n) q = q.
Proof.
  intros n [|e c r] hq hq0 hfixed; [contradiction |].
  pose proof (split_fixed_omegaDivisible (oadd e c r) hfixed)
    as hdiv.
  destruct hdiv as [he _]. destruct e as [|ee ec er]; [contradiction |].
  apply onoteAdd_below_node.
  - apply onoteNat_nf.
  - destruct n; [exact I | reflexivity].
Qed.

(** Complete behavior of the finite split under addition.  If the right
    omega part is zero, natural remainders add.  Otherwise that omega part
    absorbs the left finite remainder and the two omega parts add. *)
Lemma onoteSplit_add : forall a b aq an bq bn,
  NF a -> NF b ->
  onoteSplit a = (aq, an) -> onoteSplit b = (bq, bn) ->
  onoteSplit (onoteAdd a b) =
  match bq with
  | ozero => (aq, an + bn)
  | oadd _ _ _ => (onoteAdd aq bq, bn)
  end.
Proof.
  intros a b aq an bq bn ha hb hsplitA hsplitB.
  pose proof (onoteSplit_nf a aq an ha hsplitA) as haq.
  pose proof (onoteSplit_nf b bq bn hb hsplitB) as hbq.
  pose proof (onoteSplit_output_fixed a aq an hsplitA) as hfixedA.
  pose proof (onoteSplit_output_fixed b bq bn hsplitB) as hfixedB.
  pose proof (onoteSplit_reconstruct a aq an ha hsplitA) as hreconstructA.
  pose proof (onoteSplit_reconstruct b bq bn hb hsplitB) as hreconstructB.
  destruct bq as [|be bc br].
  - rewrite onoteAdd_zero_l in hreconstructB. subst b.
    now apply onoteSplit_add_nat.
  - rewrite hreconstructA, hreconstructB.
    rewrite onoteAdd_assoc.
    rewrite <- (onoteAdd_assoc (onoteNat an)
      (oadd be bc br) (onoteNat bn)).
    rewrite (onoteAdd_nat_absorb_fixed an (oadd be bc br)
      hbq ltac:(discriminate) hfixedB).
    rewrite <- onoteAdd_assoc.
    apply onoteSplit_add_nat_fixed.
    + now apply onoteAdd_nf.
    + now apply onoteSplit_add_fixed.
Qed.

(** * Finite right increments of exponentiation *)

Lemma onotePow_add_nat_nf : forall base exponent n,
  NF base -> NF exponent ->
  onotePow base (onoteAdd exponent (onoteNat n)) =
  onoteMul (onotePow base exponent) (onotePow base (onoteNat n)).
Proof.
  intros base exponent n hbase hexponent.
  induction n as [|n IH].
  - cbn [onoteNat].
    rewrite onoteAdd_zero_r_nf by exact hexponent.
    rewrite onotePow_zero, onoteMul_one_r. reflexivity.
  - rewrite onoteNat_add_one, <- onoteAdd_assoc.
    assert (hsum : NF (onoteAdd exponent (onoteNat n))).
    { apply onoteAdd_nf; [exact hexponent | apply onoteNat_nf]. }
    rewrite (onotePow_succ_nf base
      (onoteAdd exponent (onoteNat n)) hbase hsum).
    rewrite IH.
    rewrite (onotePow_succ_nf base (onoteNat n)
      hbase (onoteNat_nf n)).
    apply onoteMul_assoc.
    + apply onotePow_nf; assumption.
    + apply onotePow_nf; [exact hbase | apply onoteNat_nf].
    + exact hbase.
Qed.

End PAEpsilonZeroPowerLaws.
