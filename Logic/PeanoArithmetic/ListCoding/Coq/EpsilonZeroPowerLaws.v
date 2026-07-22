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

(** * The omega quotient split *)

(** Left addition of one cancels the truncated subtraction used by
    [onoteSplit'] on every positive normal exponent.  Infinite exponents are
    unchanged by subtraction and absorb the finite prefix; finite exponents
    reduce to ordinary predecessor/successor arithmetic. *)
Lemma onoteAdd_one_sub_one_nf : forall e,
  NF e -> e <> ozero ->
  onoteAdd onoteOne (onoteSub e onoteOne) = e.
Proof.
  intros [|e c r] he he0; [contradiction |].
  pose proof he as heFull.
  destruct he as [heNF [hr htop]].
  destruct e as [|ee ec er].
  - assert (hr0 : r = ozero).
    { now apply NF_zero_exponent_tail with (c := c). }
    subst r. destruct c as [|c].
    + reflexivity.
    + cbn [onoteSub onoteOne onoteAdd onoteAddAux].
      rewrite onoteCompare_refl, Nat.sub_0_r.
      cbn [onoteAddAux]. rewrite onoteCompare_refl. reflexivity.
  - cbn [onoteSub onoteOne].
    apply onoteAdd_below_node.
    + exact NF_one.
    + reflexivity.
Qed.

(** The two split functions carry the same finite remainder.  The first
    component of [onoteSplit] is obtained by multiplying the quotient from
    [onoteSplit'] by omega, represented here by [onoteScale onoteOne]. *)
Lemma onoteSplit_eq_scale_split' : forall o q n,
  NF o -> onoteSplit' o = (q, n) ->
  onoteSplit o = (onoteScale onoteOne q, n).
Proof.
  induction o as [|e IHe c r IHr]; intros q n ho hsplit.
  - cbn [onoteSplit'] in hsplit. inversion hsplit; subst q n.
    reflexivity.
  - destruct ho as [he [hr htop]].
    destruct e as [|ee ec er].
    + cbn [onoteSplit'] in hsplit. inversion hsplit; subst q n.
      reflexivity.
    + cbn [onoteSplit'] in hsplit.
      destruct (onoteSplit' r) as [r' k] eqn:hsplitR.
      inversion hsplit; subst q n.
      change ((oadd (oadd ee ec er) c (fst (onoteSplit r)),
        snd (onoteSplit r)) =
        (oadd
          (onoteAdd onoteOne
            (onoteSub (oadd ee ec er) onoteOne)) c
          (onoteScale onoteOne r'), k)).
      rewrite (IHr r' k hr eq_refl).
      rewrite (onoteAdd_one_sub_one_nf (oadd ee ec er) he
        ltac:(discriminate)).
      reflexivity.
Qed.

(** Scaling is injective on normal forms.  Equality of node exponents is
    reflected through [onoteCompare_add_left], and the tails follow by the
    structural induction hypothesis. *)
Lemma onoteScale_injective_nf : forall x a b,
  NF x -> NF a -> NF b ->
  onoteScale x a = onoteScale x b -> a = b.
Proof.
  intros x a. revert x.
  induction a as [|ae IHe ac ar IHr]; intros x [|be bc br] hx ha hb hscale;
    try discriminate; [reflexivity |].
  destruct ha as [hae [har htopA]].
  destruct hb as [hbe [hbr htopB]].
  cbn [onoteScale] in hscale. inversion hscale as [[hexp hcoeff htail]].
  assert (hcmp :
    onoteCompare (onoteAdd x ae) (onoteAdd x be) = Eq).
  { rewrite hexp. apply onoteCompare_refl. }
  rewrite (onoteCompare_add_left x ae be hx hae hbe) in hcmp.
  apply onoteCompare_eq in hcmp. subst be bc.
  f_equal. now apply IHr with (x := x).
Qed.

(** A monomial [omega^x] acts on a normal notation exactly as [onoteScale]. *)
Lemma onoteMul_monomial_nf : forall x o,
  NF x -> NF o ->
  onoteMul (oadd x 0 ozero) o = onoteScale x o.
Proof.
  intros x o hx. induction o as [|e IHe c r IHr]; intro ho;
    [reflexivity |].
  destruct ho as [he [hr htop]]. destruct e as [|ee ec er].
  - assert (hr0 : r = ozero).
    { now apply NF_zero_exponent_tail with (c := c). }
    subst r. cbn [onoteMul onoteScale].
    rewrite coefficientProductPred_zero_l,
      onoteAdd_zero_r_nf by exact hx.
    reflexivity.
  - cbn [onoteMul onoteScale]. rewrite IHr by exact hr. reflexivity.
Qed.

Lemma onoteScale_add_nf : forall x a b,
  NF x -> NF a -> NF b ->
  onoteScale x (onoteAdd a b) =
  onoteAdd (onoteScale x a) (onoteScale x b).
Proof.
  intros x a b hx ha hb.
  rewrite <- (onoteMul_monomial_nf x (onoteAdd a b) hx
    ltac:(now apply onoteAdd_nf)).
  rewrite <- (onoteMul_monomial_nf x a hx ha),
    <- (onoteMul_monomial_nf x b hx hb).
  apply onoteMul_add.
  - exact (conj hx (conj NF_zero I)).
  - exact ha.
  - exact hb.
Qed.

(** Complete addition law for the quotient/remainder split. *)
Lemma onoteSplit'_add : forall a b aq an bq bn,
  NF a -> NF b ->
  onoteSplit' a = (aq, an) -> onoteSplit' b = (bq, bn) ->
  onoteSplit' (onoteAdd a b) =
  match bq with
  | ozero => (aq, an + bn)
  | oadd _ _ _ => (onoteAdd aq bq, bn)
  end.
Proof.
  intros a b aq an bq bn ha hb hsplitA' hsplitB'.
  pose proof (onoteSplit'_nf a aq an ha hsplitA') as haq.
  pose proof (onoteSplit'_nf b bq bn hb hsplitB') as hbq.
  pose proof (onoteSplit_eq_scale_split' a aq an ha hsplitA')
    as hsplitA.
  pose proof (onoteSplit_eq_scale_split' b bq bn hb hsplitB')
    as hsplitB.
  assert (hsumNF : NF (onoteAdd a b)).
  { now apply onoteAdd_nf. }
  remember (onoteSplit' (onoteAdd a b)) as result eqn:hresult.
  destruct result as [rq rn]. symmetry in hresult.
  pose proof (onoteSplit'_nf (onoteAdd a b) rq rn hsumNF hresult)
    as hrq.
  pose proof (onoteSplit_eq_scale_split' (onoteAdd a b) rq rn
    hsumNF hresult) as hresultScale.
  pose proof (onoteSplit_add a b
    (onoteScale onoteOne aq) an
    (onoteScale onoteOne bq) bn
    ha hb hsplitA hsplitB) as hsumSplit.
  destruct bq as [|be bc br].
  - cbn [onoteScale] in hsumSplit.
    rewrite hresultScale in hsumSplit. inversion hsumSplit; subst rn.
    assert (hrqEq : rq = aq).
    {
      apply onoteScale_injective_nf with (x := onoteOne).
      - exact NF_one.
      - exact hrq.
      - exact haq.
      - assumption.
    }
    subst rq. reflexivity.
  - assert (hscaleSum :
      onoteAdd (onoteScale onoteOne aq)
        (onoteScale onoteOne (oadd be bc br)) =
      onoteScale onoteOne (onoteAdd aq (oadd be bc br))).
    {
      symmetry. apply onoteScale_add_nf.
      - exact NF_one.
      - exact haq.
      - exact hbq.
    }
    rewrite hscaleSum in hsumSplit.
    rewrite hresultScale in hsumSplit. inversion hsumSplit; subst rn.
    assert (hrqEq : rq = onoteAdd aq (oadd be bc br)).
    {
      apply onoteScale_injective_nf with (x := onoteOne).
      - exact NF_one.
      - exact hrq.
      - now apply onoteAdd_nf.
      - assumption.
    }
    subst rq. reflexivity.
Qed.

(** * Power at omega-divisible exponents *)

Lemma onoteScale_nonzero : forall x o,
  o <> ozero -> onoteScale x o <> ozero.
Proof. intros x [|e c r] h; [contradiction | discriminate]. Qed.

Lemma onoteMul_nonzero_split_fixed : forall p q,
  p <> ozero -> q <> ozero -> onoteSplit q = (q, 0) ->
  onoteMul p q <> ozero.
Proof.
  intros p q hp hq hfixed.
  rewrite (onoteMul_split_fixed p q hp hfixed).
  now apply onoteScale_nonzero.
Qed.

Lemma onoteAdd_nonzero_right_nf : forall a b,
  NF a -> b <> ozero -> onoteAdd a b <> ozero.
Proof.
  intros a b ha hb hzero.
  pose proof (onoteCompare_add_nonzero_right a b ha hb) as hstrict.
  rewrite hzero in hstrict. destruct a; discriminate.
Qed.

(** For an infinite base, every power has leading exponent `a0*exponent`.
    The zero exponent gives the monomial one; a positive finite remainder is
    exactly the branch characterized by [onotePow_branch_head]. *)
Lemma onotePow_infinite_head_nf :
  forall base exponent a0 ac ar m,
    NF base -> NF exponent ->
    onoteSplit base = (oadd a0 ac ar, m) ->
    exists c r,
      onotePow base exponent =
      oadd (onoteMul a0 exponent) c r.
Proof.
  intros base exponent a0 ac ar m hbase hexponent hbaseSplit.
  pose proof (onoteSplit_nf base (oadd a0 ac ar) m
    hbase hbaseSplit) as homega.
  pose proof (onoteSplit_output_fixed base (oadd a0 ac ar) m
    hbaseSplit) as hfixed.
  assert (ha0 : a0 <> ozero).
  {
    intro ha0. subst a0. cbn [onoteSplit] in hfixed. discriminate.
  }
  remember (onoteSplit exponent) as exponentSplit eqn:hexponentSplit.
  destruct exponentSplit as [b k]. symmetry in hexponentSplit.
  pose proof (onoteSplit_nf exponent b k hexponent
    hexponentSplit) as hb.
  pose proof (onoteSplit_reconstruct exponent b k
    hexponent hexponentSplit) as hexponentReconstruct.
  unfold onotePow. rewrite hbaseSplit.
  cbn [onotePowAux2]. rewrite hexponentSplit.
  destruct k as [|k].
  - cbn.
    cbn [onoteNat] in hexponentReconstruct.
    rewrite onoteAdd_zero_r_nf in hexponentReconstruct by exact hb.
    subst exponent. now exists 0, ozero.
  - assert (hmulExponent :
      onoteMul a0 exponent =
      onoteAdd (onoteMul a0 b) (onoteMulNat a0 (S k))).
    {
      rewrite hexponentReconstruct.
      rewrite (onoteMul_add a0 b (onoteNat (S k))
        (proj1 homega) hb (onoteNat_nf (S k))).
      now rewrite onoteMul_onoteNat.
    }
    destruct (onotePow_branch_head (onoteMul a0 b)
      a0 ac ar k m
      ltac:(apply onoteMul_nf;
        [exact (proj1 homega) | exact hb])
      homega ha0) as [c [r hbranch]].
    cbn [fst snd].
    rewrite hbranch, hmulExponent. now exists c, r.
Qed.

Lemma onotePow_infinite_fixed :
  forall base exponent a0 ac ar m,
    onoteSplit base = (oadd a0 ac ar, m) ->
    onoteSplit exponent = (exponent, 0) ->
    onotePow base exponent =
    oadd (onoteMul a0 exponent) 0 ozero.
Proof.
  intros base exponent a0 ac ar m hbase hexponent.
  unfold onotePow. rewrite hbase.
  cbn [onotePowAux2]. rewrite hexponent. reflexivity.
Qed.

(** Adding a nonzero omega-divisible exponent is the limit step of ordinal
    exponentiation.  The finite-base branch uses the omega quotient split;
    the infinite-base branch compares leading exponents and invokes right
    distributivity of ordinal multiplication. *)
Theorem onotePow_add_omegaPart_nf : forall base left omega,
  NF base -> NF left -> NF omega ->
  omega <> ozero -> onoteSplit omega = (omega, 0) ->
  onotePow base (onoteAdd left omega) =
  onoteMul (onotePow base left) (onotePow base omega).
Proof.
  intros base left [|oe oc or] hbase hleft homega homega0 hfixedOmega;
    [contradiction |].
  set (omega := oadd oe oc or) in *.
  assert (hsumNF : NF (onoteAdd left omega)).
  { now apply onoteAdd_nf. }
  assert (hsum0 : onoteAdd left omega <> ozero).
  { now apply onoteAdd_nonzero_right_nf. }

  remember (onoteSplit left) as leftSplit eqn:hleftSplit.
  destruct leftSplit as [lq ln]. symmetry in hleftSplit.
  pose proof (onoteSplit_nf left lq ln hleft hleftSplit) as hlq.
  pose proof (onoteSplit_add left omega lq ln omega 0
    hleft homega hleftSplit hfixedOmega) as hsumSplit.
  change (onoteSplit (onoteAdd left omega) =
    (onoteAdd lq omega, 0)) in hsumSplit.
  pose proof (onoteSplit_reconstruct (onoteAdd left omega)
    (onoteAdd lq omega) 0 hsumNF hsumSplit) as hsumReconstruct.
  cbn [onoteNat] in hsumReconstruct.
  rewrite onoteAdd_zero_r_nf in hsumReconstruct.
  2: { now apply onoteAdd_nf. }
  assert (hsumFixed :
    onoteSplit (onoteAdd left omega) =
    (onoteAdd left omega, 0)).
  {
    rewrite hsumSplit. f_equal.
    symmetry. exact hsumReconstruct.
  }

  remember (onoteSplit' left) as leftSplit' eqn:hleftSplit'.
  destruct leftSplit' as [lp lk]. symmetry in hleftSplit'.
  pose proof (onoteSplit'_nf left lp lk hleft hleftSplit') as hlp.
  remember (onoteSplit' omega) as omegaSplit' eqn:homegaSplit'.
  destruct omegaSplit' as [op ok]. symmetry in homegaSplit'.
  pose proof (onoteSplit'_nf omega op ok homega homegaSplit') as hop.
  pose proof (onoteSplit_eq_scale_split' omega op ok
    homega homegaSplit') as homegaScale.
  rewrite hfixedOmega in homegaScale.
  inversion homegaScale; subst ok.
  assert (hop0 : op <> ozero).
  {
    intro hop0. subst op. cbn [onoteScale] in H0.
    unfold omega in H0. discriminate.
  }
  destruct op as [|ope opc opr]; [contradiction |].
  pose proof (onoteSplit'_add left omega lp lk
    (oadd ope opc opr) 0 hleft homega hleftSplit' homegaSplit')
    as hsumSplit'.
  change (onoteSplit' (onoteAdd left omega) =
    (onoteAdd lp (oadd ope opc opr), 0)) in hsumSplit'.

  remember (onoteSplit base) as baseSplit eqn:hbaseSplit.
  destruct baseSplit as [basePart finitePart]. symmetry in hbaseSplit.
  pose proof (onoteSplit_reconstruct base basePart finitePart
    hbase hbaseSplit) as hbaseReconstruct.
  destruct basePart as [|a0 ac ar].
  - rewrite onoteAdd_zero_l in hbaseReconstruct. subst base.
    destruct finitePart as [|[|finitePart]].
    + change (onotePow ozero (onoteAdd left omega) =
        onoteMul (onotePow ozero left) (onotePow ozero omega)).
      rewrite (onotePow_zero_base_nonzero (onoteAdd left omega) hsum0),
        (onotePow_zero_base_nonzero omega homega0), onoteMul_zero_r.
      reflexivity.
    + change (onotePow onoteOne (onoteAdd left omega) =
        onoteMul (onotePow onoteOne left) (onotePow onoteOne omega)).
      rewrite !onotePow_one_base, onoteMul_one_r. reflexivity.
    + unfold onotePow.
      rewrite !onoteSplit_onoteNat.
      cbn [onotePowAux2].
      rewrite hsumSplit', hleftSplit', homegaSplit'.
      cbn [fst snd onoteMul Nat.pow Nat.pred]. reflexivity.
  - pose proof (onoteSplit_nf base (oadd a0 ac ar) finitePart
      hbase hbaseSplit) as hbasePart.
    pose proof (onoteSplit_output_fixed base (oadd a0 ac ar)
      finitePart hbaseSplit) as hfixedBasePart.
    assert (ha0 : a0 <> ozero).
    {
      intro ha0. subst a0.
      cbn [onoteSplit] in hfixedBasePart. discriminate.
    }
    assert (ha0Omega : onoteMul a0 omega <> ozero).
    {
      apply onoteMul_nonzero_split_fixed;
        [exact ha0 | exact homega0 | exact hfixedOmega].
    }
    pose proof (onotePow_infinite_fixed base omega a0 ac ar
      finitePart hbaseSplit hfixedOmega) as hpowOmega.
    pose proof (onotePow_infinite_fixed base (onoteAdd left omega)
      a0 ac ar finitePart hbaseSplit hsumFixed) as hpowSum.
    destruct (onotePow_infinite_head_nf base left a0 ac ar finitePart
      hbase hleft hbaseSplit) as [pc [pr hpowLeft]].
    rewrite hpowSum, hpowLeft, hpowOmega.
    destruct (onoteMul a0 omega) as [|me mc mr] eqn:hmulOmega;
      [contradiction |].
    cbn [onoteMul].
    rewrite (onoteMul_add a0 left omega
      (proj1 hbasePart) hleft homega).
    rewrite hmulOmega.
    reflexivity.
Qed.

(** Every normal right exponent is an omega-divisible part followed by a
    finite tail.  The limit theorem handles the former, finite induction the
    latter, and multiplication associativity joins the two results. *)
Theorem onotePow_add_nf : forall base left right,
  NF base -> NF left -> NF right ->
  onotePow base (onoteAdd left right) =
  onoteMul (onotePow base left) (onotePow base right).
Proof.
  intros base left right hbase hleft hright.
  remember (onoteSplit right) as rightSplit eqn:hrightSplit.
  destruct rightSplit as [q n]. symmetry in hrightSplit.
  pose proof (onoteSplit_nf right q n hright hrightSplit) as hq.
  pose proof (onoteSplit_output_fixed right q n hrightSplit) as hqFixed.
  pose proof (onoteSplit_reconstruct right q n hright hrightSplit)
    as hrightReconstruct.
  destruct q as [|qe qc qr].
  - rewrite onoteAdd_zero_l in hrightReconstruct. subst right.
    now apply onotePow_add_nat_nf.
  - rewrite hrightReconstruct, <- onoteAdd_assoc.
    assert (hsum : NF (onoteAdd left (oadd qe qc qr))).
    { now apply onoteAdd_nf. }
    rewrite (onotePow_add_nat_nf base
      (onoteAdd left (oadd qe qc qr)) n hbase hsum).
    rewrite (onotePow_add_omegaPart_nf base left (oadd qe qc qr)
      hbase hleft hq ltac:(discriminate) hqFixed).
    rewrite (onotePow_add_nat_nf base (oadd qe qc qr) n
      hbase hq).
    apply onoteMul_assoc.
    + now apply onotePow_nf.
    + now apply onotePow_nf.
    + apply onotePow_nf; [exact hbase | apply onoteNat_nf].
Qed.

Theorem powCode_addCode : forall a b c,
  ValidOrdinalCode a -> ValidOrdinalCode b -> ValidOrdinalCode c ->
  powCode a (addCode b c) =
  mulCode (powCode a b) (powCode a c).
Proof.
  intros a b c ha hb hc. apply decode_injective.
  rewrite decode_powCode, decode_addCode, decode_mulCode,
    !decode_powCode.
  apply onotePow_add_nf; assumption.
Qed.

(** * The omega quotient of a product *)

(** Even before imposing normality, adding to a nonzero left notation cannot
    produce zero.  This small raw fact is useful for showing that scaling by
    [omega] really produces an operationally omega-divisible notation. *)
Lemma onoteAdd_nonzero_left_raw : forall a b,
  a <> ozero -> onoteAdd a b <> ozero.
Proof.
  induction a as [|e IHe c r IHr]; intros b ha; [contradiction |].
  cbn [onoteAdd]. unfold onoteAddAux.
  destruct (onoteAdd r b) as [|te tc tr] eqn:hsum;
    [discriminate |].
  destruct (onoteCompare e te); discriminate.
Qed.

(** Multiplication by [omega] on the left removes every finite tail.  Here
    this is stated directly for [onoteScale onoteOne], the executable form of
    that multiplication. *)
Lemma onoteSplit_scale_one : forall q,
  onoteSplit (onoteScale onoteOne q) =
  (onoteScale onoteOne q, 0).
Proof.
  intro q. apply omegaDivisible_split_fixed.
  induction q as [|e IHe c r IHr].
  - exact I.
  - cbn [onoteScale OmegaDivisible]. split.
    + apply onoteAdd_nonzero_left_raw. discriminate.
    + exact IHr.
Qed.

(** The quotient-oriented split is the inverse of scaling by [omega] on
    normal forms.  We obtain the result from the already-proved bridge
    between the two split functions; injectivity of scaling then recovers
    the quotient itself. *)
Lemma onoteSplit'_scale_one_nf : forall q,
  NF q -> onoteSplit' (onoteScale onoteOne q) = (q, 0).
Proof.
  intros q hq.
  remember (onoteSplit' (onoteScale onoteOne q)) as qr eqn:hsplit'.
  destruct qr as [r n]. symmetry in hsplit'.
  assert (hscaleNF : NF (onoteScale onoteOne q)).
  { now apply onoteScale_nf. }
  pose proof (onoteSplit'_nf (onoteScale onoteOne q) r n
    hscaleNF hsplit') as hr.
  pose proof (onoteSplit_eq_scale_split' (onoteScale onoteOne q)
    r n hscaleNF hsplit') as hbridge.
  rewrite onoteSplit_scale_one in hbridge.
  pose proof (f_equal (@fst ONote nat) hbridge) as hscale.
  pose proof (f_equal (@snd ONote nat) hbridge) as hn.
  cbn in hscale, hn. subst n.
  assert (hqr : q = r).
  {
    apply onoteScale_injective_nf with (x := onoteOne).
    - exact NF_one.
    - exact hq.
    - exact hr.
    - exact hscale.
  }
  subst r. reflexivity.
Qed.

(** Removing a finite tail preserves the leading exponent whenever the
    omega-divisible part is nonzero. *)
Lemma onoteHead_split_nonzero : forall o q n,
  onoteSplit o = (q, n) -> q <> ozero ->
  onoteHead o = onoteHead q.
Proof.
  intros o q n hsplit hq.
  destruct (onoteSplit_shape o q n hsplit) as [hzero | hshape].
  - contradiction.
  - destruct hshape as [e [c [r [r' [ho hq']]]]].
    subst o q. reflexivity.
Qed.

(** A scaled left factor can be pulled through multiplication.  The proof
    deliberately factors [onoteScale] through its monomial characterization,
    so that ordinary multiplication associativity does all the work. *)
Lemma onoteMul_scale_one_nf : forall q c,
  NF q -> NF c ->
  onoteMul (onoteScale onoteOne q) c =
  onoteScale onoteOne (onoteMul q c).
Proof.
  intros q c hq hc.
  rewrite <- (onoteMul_monomial_nf onoteOne q NF_one hq).
  rewrite (onoteMul_assoc (oadd onoteOne 0 ozero) q c
    ltac:(exact (conj NF_one (conj NF_zero I))) hq hc).
  apply onoteMul_monomial_nf.
  - exact NF_one.
  - now apply onoteMul_nf.
Qed.

(** Let [b = omega*bq + k] and let [c] have no finite tail.  Right
    multiplication by [c] ignores the finite tail of [b]; after replacing
    [b] by [omega*bq], associativity exposes one outer factor of [omega].
    Thus the quotient split of [b*c] is exactly [bq*c]. *)
Lemma onoteSplit'_mul_omegaPart_nf : forall b c bq k,
  NF b -> NF c -> b <> ozero -> bq <> ozero ->
  onoteSplit' b = (bq, k) -> onoteSplit c = (c, 0) ->
  onoteSplit' (onoteMul b c) = (onoteMul bq c, 0).
Proof.
  intros b c bq k hb hc hb0 hbq0 hsplitB' hfixedC.
  pose proof (onoteSplit'_nf b bq k hb hsplitB') as hbq.
  pose proof (onoteSplit_eq_scale_split' b bq k hb hsplitB')
    as hsplitB.
  assert (hscale0 : onoteScale onoteOne bq <> ozero).
  { now apply onoteScale_nonzero. }
  pose proof (onoteHead_split_nonzero b
    (onoteScale onoteOne bq) k hsplitB hscale0) as hhead.
  assert (hmul :
    onoteMul b c = onoteMul (onoteScale onoteOne bq) c).
  {
    rewrite (onoteMul_split_fixed b c hb0 hfixedC),
      (onoteMul_split_fixed (onoteScale onoteOne bq) c
        hscale0 hfixedC).
    now rewrite hhead.
  }
  rewrite hmul, onoteMul_scale_one_nf by assumption.
  apply onoteSplit'_scale_one_nf.
  now apply onoteMul_nf.
Qed.

(** Nonzero raw inputs always select a node-producing branch of
    [onoteMul].  No normality is needed for this shape observation. *)
Lemma onoteMul_nonzero_raw : forall a b,
  a <> ozero -> b <> ozero -> onoteMul a b <> ozero.
Proof.
  intros a b ha hb.
  destruct a as [|ae ac ar]; [contradiction |].
  destruct b as [|be bc br]; [contradiction |].
  destruct be; discriminate.
Qed.

(** Scaling preserves the structural absence of finite terms. *)
Lemma omegaDivisible_scale : forall x o,
  OmegaDivisible o -> OmegaDivisible (onoteScale x o).
Proof.
  intros x o. induction o as [|e IHe c r IHr]; intro ho.
  - exact I.
  - destruct ho as [he hr]. cbn [onoteScale OmegaDivisible]. split.
    + destruct x as [|xe xc xr].
      * cbn [onoteAdd]. exact he.
      * apply onoteAdd_nonzero_left_raw. discriminate.
    + now apply IHr.
Qed.

(** A split-fixed right factor remains split-fixed after arbitrary left
    multiplication.  The zero left factor is immediate; otherwise the
    multiplication algorithm is a scale of the right factor. *)
Lemma onoteSplit_mul_omegaPart : forall b c,
  onoteSplit c = (c, 0) ->
  onoteSplit (onoteMul b c) = (onoteMul b c, 0).
Proof.
  intros [|be bc br] c hfixed.
  - now rewrite onoteMul_zero_l.
  - set (b := oadd be bc br).
    rewrite (onoteMul_split_fixed b c ltac:(discriminate) hfixed).
    apply omegaDivisible_split_fixed, omegaDivisible_scale.
    now apply split_fixed_omegaDivisible.
Qed.

(** The closed form of exponentiation by a genuinely finite base at least
    two.  Stating it separately avoids repeatedly unfolding the four-way
    base split in the limit proof. *)
Lemma onotePow_onoteNat_ge_two : forall m exponent q k,
  onoteSplit' exponent = (q, k) ->
  onotePow (onoteNat (S (S m))) exponent =
  oadd q (Nat.pred (Nat.pow (S (S m)) k)) ozero.
Proof.
  intros m exponent q k hsplit.
  unfold onotePow. rewrite onoteSplit_onoteNat.
  cbn [onotePowAux2]. now rewrite hsplit.
Qed.

(** At a nonzero omega-divisible exponent, all finite bases at least two
    reduce to the same leading monomial: the natural coefficient is raised
    only to finite remainder zero, and hence becomes one. *)
Lemma onotePow_finite_limit_independent_nf : forall m n exponent,
  NF exponent -> exponent <> ozero ->
  onoteSplit exponent = (exponent, 0) ->
  onotePow (onoteNat (S (S m))) exponent =
  onotePow (onoteNat (S (S n))) exponent.
Proof.
  intros m n exponent hexponent hexponent0 hfixed.
  remember (onoteSplit' exponent) as quotient eqn:hsplit'.
  destruct quotient as [q k]. symmetry in hsplit'.
  pose proof (onoteSplit_eq_scale_split' exponent q k
    hexponent hsplit') as hbridge.
  rewrite hfixed in hbridge.
  pose proof (f_equal (@snd ONote nat) hbridge) as hk.
  cbn in hk. subst k.
  rewrite (onotePow_onoteNat_ge_two m exponent q 0 hsplit'),
    (onotePow_onoteNat_ge_two n exponent q 0 hsplit').
  reflexivity.
Qed.

(** Every positive finite left factor disappears in front of a nonzero
    omega-divisible right factor.  Operationally its head exponent is zero,
    so [onoteMul_split_fixed] reduces the product to scaling by zero. *)
Lemma onoteMul_onoteNat_omegaPart : forall n c,
  n <> 0 -> onoteSplit c = (c, 0) ->
  onoteMul (onoteNat n) c = c.
Proof.
  intros [|n] c hn hfixed; [contradiction |].
  rewrite (onoteMul_split_fixed (onoteNat (S n)) c
    ltac:(discriminate) hfixed).
  cbn [onoteNat onoteHead]. apply onoteScale_zero.
Qed.

(** Power-of-power at a nonzero limit exponent for finite bases at least
    two.  A finite [b] makes [base^b] another finite base and satisfies
    [b*c=c].  If [b] has a nonzero omega quotient, both sides are the same
    monomial, identified by [onoteSplit'_mul_omegaPart_nf]. *)
Lemma onotePow_pow_omegaPart_finite_nf : forall m b c,
  NF b -> NF c -> b <> ozero -> c <> ozero ->
  onoteSplit c = (c, 0) ->
  onotePow (onotePow (onoteNat (S (S m))) b) c =
  onotePow (onoteNat (S (S m))) (onoteMul b c).
Proof.
  intros m b c hb hc hb0 hc0 hfixedC.
  remember (onoteSplit' b) as quotient eqn:hsplitB'.
  destruct quotient as [bq k]. symmetry in hsplitB'.
  destruct bq as [|bqe bqc bqr].
  - pose proof (onoteSplit_eq_scale_split' b ozero k hb hsplitB')
      as hsplitB.
    cbn [onoteScale] in hsplitB.
    pose proof (onoteSplit_reconstruct b ozero k hb hsplitB)
      as hreconstructB.
    rewrite onoteAdd_zero_l in hreconstructB. subst b.
    destruct k as [|k]; [contradiction |].
    pose proof (Nat.pow_gt_1 (S (S m)) (S k)
      ltac:(lia) ltac:(discriminate)) as hpowLarge.
    remember (Nat.pow (S (S m)) (S k)) as powered eqn:hpowered.
    destruct powered as [|[|powered]]; try lia.
    assert (hpowB :
      onotePow (onoteNat (S (S m))) (onoteNat (S k)) =
      onoteNat (S (S powered))).
    {
      rewrite (onotePow_onoteNat_ge_two m (onoteNat (S k))
        ozero (S k) hsplitB').
      rewrite <- hpowered. reflexivity.
    }
    rewrite hpowB.
    rewrite (onoteMul_onoteNat_omegaPart (S k) c
      ltac:(discriminate) hfixedC).
    now apply onotePow_finite_limit_independent_nf.
  - set (bq := oadd bqe bqc bqr) in *.
    pose proof (onotePow_onoteNat_ge_two m b bq k hsplitB')
      as hpowB.
    pose proof (onoteSplit'_mul_omegaPart_nf b c bq k
      hb hc hb0 ltac:(discriminate) hsplitB' hfixedC)
      as hsplitProduct'.
    rewrite hpowB.
    rewrite (onotePow_infinite_fixed
      (oadd bq (Nat.pred (Nat.pow (S (S m)) k)) ozero)
      c bq (Nat.pred (Nat.pow (S (S m)) k)) ozero 0
      eq_refl hfixedC).
    symmetry.
    exact (onotePow_onoteNat_ge_two m (onoteMul b c)
      (onoteMul bq c) 0 hsplitProduct').
Qed.

(** Power-of-power at a nonzero limit exponent for an infinite base.  The
    leading exponent of [a^b] is [a0*b].  Raising that notation to [c]
    therefore produces [(a0*b)*c], while the right side produces
    [a0*(b*c)]; multiplication associativity makes the monomials identical. *)
Lemma onotePow_pow_omegaPart_infinite_nf :
  forall a b c a0 ac ar n,
    NF a -> NF b -> NF c -> b <> ozero -> c <> ozero ->
    onoteSplit a = (oadd a0 ac ar, n) ->
    onoteSplit c = (c, 0) ->
    onotePow (onotePow a b) c = onotePow a (onoteMul b c).
Proof.
  intros a b c a0 ac ar n ha hb hc hb0 hc0 hsplitA hfixedC.
  pose proof (onoteSplit_nf a (oadd a0 ac ar) n ha hsplitA)
    as hbasePart.
  pose proof (onoteSplit_output_fixed a (oadd a0 ac ar) n hsplitA)
    as hfixedBasePart.
  assert (ha0 : a0 <> ozero).
  {
    intro hzero. subst a0.
    cbn [onoteSplit] in hfixedBasePart. discriminate.
  }
  destruct (onotePow_infinite_head_nf a b a0 ac ar n
    ha hb hsplitA) as [pc [pr hpowHead]].
  assert (ha0b0 : onoteMul a0 b <> ozero).
  { now apply onoteMul_nonzero_raw. }
  remember (onoteMul a0 b) as a0b eqn:ha0b.
  destruct a0b as [|pe pc' pr']; [contradiction |].
  remember (onoteSplit pr) as tailSplit eqn:htailSplit.
  destruct tailSplit as [pq pn]. symmetry in htailSplit.
  assert (hpowSplit :
    onoteSplit (onotePow a b) =
    (oadd (oadd pe pc' pr') pc pq, pn)).
  {
    rewrite hpowHead.
    cbn [onoteSplit]. now rewrite htailSplit.
  }
  pose proof (onotePow_infinite_fixed (onotePow a b) c
    (oadd pe pc' pr') pc pq pn hpowSplit hfixedC) as hleft.
  pose proof (onoteSplit_mul_omegaPart b c hfixedC) as hproductFixed.
  pose proof (onotePow_infinite_fixed a (onoteMul b c)
    a0 ac ar n hsplitA hproductFixed) as hright.
  rewrite hleft, hright, ha0b.
  f_equal.
  apply onoteMul_assoc.
  - exact (proj1 hbasePart).
  - exact hb.
  - exact hc.
Qed.

(** The complete nonzero split-fixed exponent case.  The split of [a]
    exposes exactly the four operational base classes: zero, one, larger
    finite, and infinite. *)
Theorem onotePow_pow_omegaPart_nf : forall a b c,
  NF a -> NF b -> NF c -> c <> ozero ->
  onoteSplit c = (c, 0) ->
  onotePow (onotePow a b) c = onotePow a (onoteMul b c).
Proof.
  intros a b c ha hb hc hc0 hfixedC.
  destruct b as [|be bc br].
  - rewrite onotePow_zero, onotePow_one_base,
      onoteMul_zero_l, onotePow_zero.
    reflexivity.
  - set (b := oadd be bc br) in *.
    assert (hb0 : b <> ozero) by discriminate.
    remember (onoteSplit a) as baseSplit eqn:hsplitA.
    destruct baseSplit as [basePart n]. symmetry in hsplitA.
    pose proof (onoteSplit_reconstruct a basePart n ha hsplitA)
      as hreconstructA.
    destruct basePart as [|a0 ac ar].
    + rewrite onoteAdd_zero_l in hreconstructA. subst a.
      destruct n as [|[|m]].
      * assert (hbc0 : onoteMul b c <> ozero).
        { now apply onoteMul_nonzero_split_fixed. }
        change (onotePow (onotePow ozero b) c =
          onotePow ozero (onoteMul b c)).
        rewrite (onotePow_zero_base_nonzero b hb0),
          (onotePow_zero_base_nonzero c hc0),
          (onotePow_zero_base_nonzero (onoteMul b c) hbc0).
        reflexivity.
      * change (onotePow (onotePow onoteOne b) c =
          onotePow onoteOne (onoteMul b c)).
        rewrite !onotePow_one_base. reflexivity.
      * change (onotePow
          (onotePow (onoteNat (S (S m))) b) c =
          onotePow (onoteNat (S (S m))) (onoteMul b c)).
        now apply onotePow_pow_omegaPart_finite_nf.
    + now apply onotePow_pow_omegaPart_infinite_nf with
        (a0 := a0) (ac := ac) (ar := ar) (n := n).
Qed.

(** Finite outer exponents are the successor part of power-of-power.  The
    induction step expands both the outer power and [b*(n+1)], then uses the
    already-established power-add law in the reverse direction. *)
Lemma onotePow_pow_nat_nf : forall a b n,
  NF a -> NF b ->
  onotePow (onotePow a b) (onoteNat n) =
  onotePow a (onoteMul b (onoteNat n)).
Proof.
  intros a b n ha hb. induction n as [|n IH].
  - cbn [onoteNat]. rewrite onotePow_zero, onoteMul_zero_r,
      onotePow_zero. reflexivity.
  - rewrite onoteNat_add_one.
    rewrite (onotePow_succ_nf (onotePow a b) (onoteNat n)
      ltac:(now apply onotePow_nf) (onoteNat_nf n)).
    rewrite IH.
    rewrite (onoteMul_add b (onoteNat n) onoteOne
      hb (onoteNat_nf n) NF_one), onoteMul_one_r.
    symmetry. apply onotePow_add_nf.
    + exact ha.
    + apply onoteMul_nf; [exact hb | apply onoteNat_nf].
    + exact hb.
Qed.

(** Every normal outer exponent is its split-fixed omega part followed by a
    canonical natural.  The two preceding theorems handle those pieces, and
    power-add plus right distributivity of multiplication reassemble them. *)
Theorem onotePow_pow_nf : forall a b c,
  NF a -> NF b -> NF c ->
  onotePow (onotePow a b) c = onotePow a (onoteMul b c).
Proof.
  intros a b c ha hb hc.
  remember (onoteSplit c) as outerSplit eqn:hsplitC.
  destruct outerSplit as [q n]. symmetry in hsplitC.
  pose proof (onoteSplit_nf c q n hc hsplitC) as hq.
  pose proof (onoteSplit_output_fixed c q n hsplitC) as hfixedQ.
  pose proof (onoteSplit_reconstruct c q n hc hsplitC)
    as hreconstructC.
  destruct q as [|qe qc qr].
  - rewrite onoteAdd_zero_l in hreconstructC. subst c.
    now apply onotePow_pow_nat_nf.
  - set (q := oadd qe qc qr) in *.
    rewrite hreconstructC.
    rewrite (onotePow_add_nf (onotePow a b) q (onoteNat n)
      ltac:(now apply onotePow_nf) hq (onoteNat_nf n)).
    rewrite (onotePow_pow_omegaPart_nf a b q ha hb hq
      ltac:(discriminate) hfixedQ).
    rewrite (onotePow_pow_nat_nf a b n ha hb).
    rewrite (onoteMul_add b q (onoteNat n)
      hb hq (onoteNat_nf n)).
    symmetry. apply onotePow_add_nf.
    + exact ha.
    + exact (onoteMul_nf b q hb hq).
    + exact (onoteMul_nf b (onoteNat n) hb (onoteNat_nf n)).
Qed.

(** Code-level power-of-power, in the same result-free functional style as
    [powCode_addCode].  The validity hypotheses are precisely the normality
    assumptions required by the raw theorem. *)
Theorem powCode_mulCode : forall a b c,
  ValidOrdinalCode a -> ValidOrdinalCode b -> ValidOrdinalCode c ->
  powCode (powCode a b) c = powCode a (mulCode b c).
Proof.
  intros a b c ha hb hc. apply decode_injective.
  rewrite !decode_powCode, decode_mulCode.
  apply onotePow_pow_nf; assumption.
Qed.

End PAEpsilonZeroPowerLaws.
