(**
  Phase-one syntax and metatheory for quantifier-complexity-restricted PA
  proofs.

  This module deliberately separates two claims which are easy to conflate.
  Merely bounding the *conclusion* of a proof cannot yield a weakened
  consistency statement, because [pBot] has rank zero.  The operative
  predicate below therefore bounds every formula occurrence in the whole
  natural-deduction tree (including the contexts displayed at its nodes).

  The numerical formula rank is a polarity-aware arithmetical-hierarchy
  rank.  It is still a rank of the displayed syntax, not a theorem about
  conversion to canonical prenex normal form.  In particular implication
  swaps the polarity of its antecedent.

  This is the external, phase-one layer.  The final statement requested in
  the project -- an *internal PA proof* of each fixed-rank consistency
  sentence -- additionally needs arithmetized syntax, a coded restricted
  proof predicate, and fixed-level partial truth predicates.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.

Import ListNotations.

Module PABoundedConsistency.

Import PA.

(** [sigmaRank] and [piRank] are the two polarities of the same hierarchy
    calculation.  Atomic formulae have rank zero.  Conjunction and
    disjunction preserve polarity, while implication reverses the polarity
    of its antecedent.  A quantifier of the preferred kind starts level one;
    viewing it from the opposite polarity costs one further alternation. *)
Fixpoint sigmaRank (phi : formula) : nat :=
  match phi with
  | pEq _ _ => 0
  | pBot => 0
  | pImp a b => Nat.max (piRank a) (sigmaRank b)
  | pAnd a b => Nat.max (sigmaRank a) (sigmaRank b)
  | pOr a b => Nat.max (sigmaRank a) (sigmaRank b)
  | pAll a => S (Nat.max 1 (piRank a))
  | pEx a => Nat.max 1 (sigmaRank a)
  end
with piRank (phi : formula) : nat :=
  match phi with
  | pEq _ _ => 0
  | pBot => 0
  | pImp a b => Nat.max (sigmaRank a) (piRank b)
  | pAnd a b => Nat.max (piRank a) (piRank b)
  | pOr a b => Nat.max (piRank a) (piRank b)
  | pAll a => Nat.max 1 (piRank a)
  | pEx a => S (Nat.max 1 (sigmaRank a))
  end.

(** A formula may be presented from whichever hierarchy polarity is
    cheaper.  Thus a purely universal or purely existential formula has
    one group, while a formula requiring both polarities can have rank two
    or more. *)
Definition quantifierGroups (phi : formula) : nat :=
  Nat.min (sigmaRank phi) (piRank phi).

Definition QuantifierBounded (n : nat) (phi : formula) : Prop :=
  quantifierGroups phi <= n.

(** Small executable checks pin down the intended polarity convention. *)
Example quantifierGroups_existential_atom :
  quantifierGroups (pEx (pEq (tVar 0) (tVar 0))) = 1.
Proof. reflexivity. Qed.

Example quantifierGroups_universal_atom :
  quantifierGroups (pAll (pEq (tVar 0) (tVar 0))) = 1.
Proof. reflexivity. Qed.

Example quantifierGroups_mixed_branches :
  quantifierGroups
    (pAnd (pEx (pEq (tVar 0) (tVar 0)))
      (pAll (pEq (tVar 0) (tVar 0)))) = 2.
Proof. reflexivity. Qed.

Example quantifierGroups_implication_polarity :
  quantifierGroups
    (pImp (pEx (pEq (tVar 0) (tVar 0)))
      (pAll (pEq (tVar 0) (tVar 0)))) = 1.
Proof. reflexivity. Qed.

Lemma ranks_rename : forall phi r,
  sigmaRank (Formula.rename r phi) = sigmaRank phi /\
  piRank (Formula.rename r phi) = piRank phi.
Proof.
  induction phi as [s t | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa]; intro r; cbn.
  - split; reflexivity.
  - split; reflexivity.
  - destruct (IHa r) as [hsa hpa].
    destruct (IHb r) as [hsb hpb].
    rewrite hpa, hsb, hsa, hpb.
    split; reflexivity.
  - destruct (IHa r) as [hsa hpa].
    destruct (IHb r) as [hsb hpb].
    rewrite hsa, hsb, hpa, hpb.
    split; reflexivity.
  - destruct (IHa r) as [hsa hpa].
    destruct (IHb r) as [hsb hpb].
    rewrite hsa, hsb, hpa, hpb.
    split; reflexivity.
  - destruct (IHa (up r)) as [hsa hpa].
    rewrite hpa.
    split; reflexivity.
  - destruct (IHa (up r)) as [hsa hpa].
    rewrite hsa.
    split; reflexivity.
Qed.

Lemma sigmaRank_rename : forall phi r,
  sigmaRank (Formula.rename r phi) = sigmaRank phi.
Proof.
  intros phi r.
  exact (proj1 (ranks_rename phi r)).
Qed.

Lemma piRank_rename : forall phi r,
  piRank (Formula.rename r phi) = piRank phi.
Proof.
  intros phi r.
  exact (proj2 (ranks_rename phi r)).
Qed.

Lemma quantifierGroups_rename : forall phi r,
  quantifierGroups (Formula.rename r phi) = quantifierGroups phi.
Proof.
  intros phi r.
  unfold quantifierGroups.
  rewrite sigmaRank_rename, piRank_rename.
  reflexivity.
Qed.

Lemma ranks_subst : forall phi sigma,
  sigmaRank (Formula.subst sigma phi) = sigmaRank phi /\
  piRank (Formula.subst sigma phi) = piRank phi.
Proof.
  induction phi as [s t | | a IHa b IHb | a IHa b IHb |
      a IHa b IHb | a IHa | a IHa]; intro sigma; cbn.
  - split; reflexivity.
  - split; reflexivity.
  - destruct (IHa sigma) as [hsa hpa].
    destruct (IHb sigma) as [hsb hpb].
    rewrite hpa, hsb, hsa, hpb.
    split; reflexivity.
  - destruct (IHa sigma) as [hsa hpa].
    destruct (IHb sigma) as [hsb hpb].
    rewrite hsa, hsb, hpa, hpb.
    split; reflexivity.
  - destruct (IHa sigma) as [hsa hpa].
    destruct (IHb sigma) as [hsb hpb].
    rewrite hsa, hsb, hpa, hpb.
    split; reflexivity.
  - destruct (IHa (Term.upSubst sigma)) as [hsa hpa].
    rewrite hpa.
    split; reflexivity.
  - destruct (IHa (Term.upSubst sigma)) as [hsa hpa].
    rewrite hsa.
    split; reflexivity.
Qed.

Lemma sigmaRank_subst : forall phi sigma,
  sigmaRank (Formula.subst sigma phi) = sigmaRank phi.
Proof.
  intros phi sigma.
  exact (proj1 (ranks_subst phi sigma)).
Qed.

Lemma piRank_subst : forall phi sigma,
  piRank (Formula.subst sigma phi) = piRank phi.
Proof.
  intros phi sigma.
  exact (proj2 (ranks_subst phi sigma)).
Qed.

Lemma quantifierGroups_subst : forall phi sigma,
  quantifierGroups (Formula.subst sigma phi) = quantifierGroups phi.
Proof.
  intros phi sigma.
  unfold quantifierGroups.
  rewrite sigmaRank_subst, piRank_subst.
  reflexivity.
Qed.

Lemma QuantifierBounded_rename : forall n phi r,
  QuantifierBounded n (Formula.rename r phi) <->
  QuantifierBounded n phi.
Proof.
  intros n phi r.
  unfold QuantifierBounded.
  rewrite quantifierGroups_rename.
  reflexivity.
Qed.

Lemma QuantifierBounded_subst : forall n phi sigma,
  QuantifierBounded n (Formula.subst sigma phi) <->
  QuantifierBounded n phi.
Proof.
  intros n phi sigma.
  unfold QuantifierBounded.
  rewrite quantifierGroups_subst.
  reflexivity.
Qed.

Lemma QuantifierBounded_mono : forall n m phi,
  n <= m -> QuantifierBounded n phi -> QuantifierBounded m phi.
Proof.
  unfold QuantifierBounded.
  intros n m phi hnm hphi.
  lia.
Qed.

(** Maximum rank of every formula explicitly displayed in a context. *)
Fixpoint contextRank (G : list formula) : nat :=
  match G with
  | [] => 0
  | phi :: G' => Nat.max (quantifierGroups phi) (contextRank G')
  end.

(** Rocq's original [Formula.Prov] is intentionally proof-irrelevant: it is
    declared in [Prop].  A multi-constructor proposition cannot be eliminated
    into [nat], so its erased proof object cannot be traversed to compute an
    occurrence rank.  [ProvTree] is the faithful data-carrying mirror in
    [Type].  It has exactly one constructor for each [Formula.Prov] rule,
    with the same contexts, conclusions, terms, and side-condition proofs. *)
Inductive ProvTree : list formula -> formula -> Type :=
| PT_ass : forall G a, In a G -> ProvTree G a
| PT_impI : forall G a b,
    ProvTree (a :: G) b -> ProvTree G (pImp a b)
| PT_impE : forall G a b,
    ProvTree G (pImp a b) -> ProvTree G a -> ProvTree G b
| PT_botE : forall G a, ProvTree G pBot -> ProvTree G a
| PT_lem : forall G a, ProvTree G (pOr a (pImp a pBot))
| PT_andI : forall G a b,
    ProvTree G a -> ProvTree G b -> ProvTree G (pAnd a b)
| PT_andE1 : forall G a b, ProvTree G (pAnd a b) -> ProvTree G a
| PT_andE2 : forall G a b, ProvTree G (pAnd a b) -> ProvTree G b
| PT_orI1 : forall G a b, ProvTree G a -> ProvTree G (pOr a b)
| PT_orI2 : forall G a b, ProvTree G b -> ProvTree G (pOr a b)
| PT_orE : forall G a b c,
    ProvTree G (pOr a b) ->
    ProvTree (a :: G) c ->
    ProvTree (b :: G) c ->
    ProvTree G c
| PT_allI : forall G a,
    ProvTree (map (Formula.rename S) G) a -> ProvTree G (pAll a)
| PT_allE : forall G a t,
    ProvTree G (pAll a) ->
    ProvTree G (Formula.subst (Formula.instTerm t) a)
| PT_exI : forall G a t,
    ProvTree G (Formula.subst (Formula.instTerm t) a) ->
    ProvTree G (pEx a)
| PT_exE : forall G a c,
    ProvTree G (pEx a) ->
    ProvTree (a :: map (Formula.rename S) G) (Formula.rename S c) ->
    ProvTree G c
| PT_eqRefl : forall G t, ProvTree G (pEq t t)
| PT_eqElim : forall G s t a,
    ProvTree G (pEq s t) ->
    ProvTree G (Formula.subst (Formula.instTerm s) a) ->
    ProvTree G (Formula.subst (Formula.instTerm t) a).

(** Forgetting the data-carrying tree recovers the repository's ordinary PA
    derivation, constructor for constructor. *)
Fixpoint eraseProvTree {G phi} (d : ProvTree G phi) :
    Formula.Prov G phi :=
  match d with
  | PT_ass G a ha => Formula.P_ass G a ha
  | PT_impI G a b h => Formula.P_impI G a b (eraseProvTree h)
  | PT_impE G a b hImp hA =>
      Formula.P_impE G a b (eraseProvTree hImp) (eraseProvTree hA)
  | PT_botE G a hBot => Formula.P_botE G a (eraseProvTree hBot)
  | PT_lem G a => Formula.P_lem G a
  | PT_andI G a b hA hB =>
      Formula.P_andI G a b (eraseProvTree hA) (eraseProvTree hB)
  | PT_andE1 G a b hAnd => Formula.P_andE1 G a b (eraseProvTree hAnd)
  | PT_andE2 G a b hAnd => Formula.P_andE2 G a b (eraseProvTree hAnd)
  | PT_orI1 G a b hA => Formula.P_orI1 G a b (eraseProvTree hA)
  | PT_orI2 G a b hB => Formula.P_orI2 G a b (eraseProvTree hB)
  | PT_orE G a b c hOr hA hB =>
      Formula.P_orE G a b c (eraseProvTree hOr)
        (eraseProvTree hA) (eraseProvTree hB)
  | PT_allI G a hA => Formula.P_allI G a (eraseProvTree hA)
  | PT_allE G a t hAll => Formula.P_allE G a t (eraseProvTree hAll)
  | PT_exI G a t hA => Formula.P_exI G a t (eraseProvTree hA)
  | PT_exE G a c hEx hBody =>
      Formula.P_exE G a c (eraseProvTree hEx) (eraseProvTree hBody)
  | PT_eqRefl G t => Formula.P_eqRefl G t
  | PT_eqElim G s t a hEq hA =>
      Formula.P_eqElim G s t a (eraseProvTree hEq) (eraseProvTree hA)
  end.

(** Conversely, ordinary derivability propositionally supplies a concrete
    tree.  The result remains in [Prop], respecting Rocq's elimination rule;
    downstream proofs may nevertheless unpack the tree while proving another
    proposition such as bounded derivability. *)
Lemma ProvTree_complete : forall G phi,
  Formula.Prov G phi -> exists d : ProvTree G phi, True.
Proof.
  intros G phi h.
  induction h.
  - exists (PT_ass G a H). exact I.
  - destruct IHh as [d _]. exists (PT_impI G a b d). exact I.
  - destruct IHh1 as [dImp _]. destruct IHh2 as [dA _].
    exists (PT_impE G a b dImp dA). exact I.
  - destruct IHh as [dBot _]. exists (PT_botE G a dBot). exact I.
  - exists (PT_lem G a). exact I.
  - destruct IHh1 as [dA _]. destruct IHh2 as [dB _].
    exists (PT_andI G a b dA dB). exact I.
  - destruct IHh as [dAnd _]. exists (PT_andE1 G a b dAnd). exact I.
  - destruct IHh as [dAnd _]. exists (PT_andE2 G a b dAnd). exact I.
  - destruct IHh as [dA _]. exists (PT_orI1 G a b dA). exact I.
  - destruct IHh as [dB _]. exists (PT_orI2 G a b dB). exact I.
  - destruct IHh1 as [dOr _].
    destruct IHh2 as [dA _].
    destruct IHh3 as [dB _].
    exists (PT_orE G a b c dOr dA dB). exact I.
  - destruct IHh as [dA _]. exists (PT_allI G a dA). exact I.
  - destruct IHh as [dAll _]. exists (PT_allE G a t dAll). exact I.
  - destruct IHh as [dA _]. exists (PT_exI G a t dA). exact I.
  - destruct IHh1 as [dEx _]. destruct IHh2 as [dBody _].
    exists (PT_exE G a c dEx dBody). exact I.
  - exists (PT_eqRefl G t). exact I.
  - destruct IHh1 as [dEq _]. destruct IHh2 as [dA _].
    exists (PT_eqElim G s t a dEq dA). exact I.
Qed.

(** At every node [proofOccurrenceRank] counts the displayed context and
    conclusion.  Its constructor-specific tail also counts every
    formula-valued parameter, including the equality-elimination schema,
    before recurring into every premise tree. *)
Fixpoint proofOccurrenceRank {G phi}
    (d : ProvTree G phi) : nat :=
  Nat.max (contextRank G)
    (Nat.max (quantifierGroups phi)
      (match d with
       | PT_ass _ a _ => quantifierGroups a
       | PT_impI _ a b h =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b) (proofOccurrenceRank h))
       | PT_impE _ a b hImp hA =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b)
               (Nat.max (proofOccurrenceRank hImp)
                 (proofOccurrenceRank hA)))
       | PT_botE _ a hBot =>
           Nat.max (quantifierGroups a) (proofOccurrenceRank hBot)
       | PT_lem _ a => quantifierGroups a
       | PT_andI _ a b hA hB =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b)
               (Nat.max (proofOccurrenceRank hA)
                 (proofOccurrenceRank hB)))
       | PT_andE1 _ a b hAnd =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b) (proofOccurrenceRank hAnd))
       | PT_andE2 _ a b hAnd =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b) (proofOccurrenceRank hAnd))
       | PT_orI1 _ a b hA =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b) (proofOccurrenceRank hA))
       | PT_orI2 _ a b hB =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b) (proofOccurrenceRank hB))
       | PT_orE _ a b c hOr hA hB =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups b)
               (Nat.max (quantifierGroups c)
                 (Nat.max (proofOccurrenceRank hOr)
                   (Nat.max (proofOccurrenceRank hA)
                     (proofOccurrenceRank hB)))))
       | PT_allI _ a hA =>
           Nat.max (quantifierGroups a) (proofOccurrenceRank hA)
       | PT_allE _ a _ hAll =>
           Nat.max (quantifierGroups a) (proofOccurrenceRank hAll)
       | PT_exI _ a _ hA =>
           Nat.max (quantifierGroups a) (proofOccurrenceRank hA)
       | PT_exE _ a c hEx hBody =>
           Nat.max (quantifierGroups a)
             (Nat.max (quantifierGroups c)
               (Nat.max (proofOccurrenceRank hEx)
                 (proofOccurrenceRank hBody)))
       | PT_eqRefl _ _ => 0
       | PT_eqElim _ _ _ a hEq hA =>
           Nat.max (quantifierGroups a)
             (Nat.max (proofOccurrenceRank hEq)
               (proofOccurrenceRank hA))
       end)).

Definition ProofAllBounded (n : nat) {G phi}
    (d : ProvTree G phi) : Prop :=
  proofOccurrenceRank d <= n.

Definition RestrictedProv (n : nat) (G : list formula)
    (phi : formula) : Prop :=
  exists d : ProvTree G phi, ProofAllBounded n d.

(** The bounded-theory wrapper mirrors [Formula.BProv], but the witness is
    now an occurrence-bounded proof tree. *)
Definition RestrictedBProv (n : nat) (B : formula -> Prop)
    (G : list formula) (phi : formula) : Prop :=
  exists L,
    (forall x, In x L -> B x) /\
    RestrictedProv n (L ++ G) phi.

Lemma restrictedProv_erase : forall n G phi,
  RestrictedProv n G phi -> Formula.Prov G phi.
Proof.
  intros n G phi [d _].
  exact (eraseProvTree d).
Qed.

Lemma restrictedBProv_erase : forall n B G phi,
  RestrictedBProv n B G phi -> Formula.BProv B G phi.
Proof.
  intros n B G phi [L [hL [d hd]]].
  exists L.
  split; [exact hL | exact (eraseProvTree d)].
Qed.

Lemma ProofAllBounded_mono : forall n m G phi
    (d : ProvTree G phi),
  n <= m -> ProofAllBounded n d -> ProofAllBounded m d.
Proof.
  unfold ProofAllBounded.
  intros n m G phi d hnm hd.
  lia.
Qed.

Lemma RestrictedProv_mono : forall n m G phi,
  n <= m -> RestrictedProv n G phi -> RestrictedProv m G phi.
Proof.
  intros n m G phi hnm [d hd].
  exists d.
  exact (ProofAllBounded_mono n m G phi d hnm hd).
Qed.

Lemma RestrictedBProv_mono : forall n m B G phi,
  n <= m -> RestrictedBProv n B G phi -> RestrictedBProv m B G phi.
Proof.
  intros n m B G phi hnm [L [hL hd]].
  exists L.
  split; [exact hL |].
  exact (RestrictedProv_mono n m (L ++ G) phi hnm hd).
Qed.

(** Every concrete metatheoretic derivation is finite and consequently has
    some finite occurrence bound.  This is cofinality of the external
    restricted hierarchy, not a uniform reflection theorem inside PA. *)
Lemma ProofAllBounded_cofinal : forall G phi
    (d : ProvTree G phi),
  exists n, ProofAllBounded n d.
Proof.
  intros G phi d.
  exists (proofOccurrenceRank d).
  unfold ProofAllBounded.
  lia.
Qed.

Lemma RestrictedProv_cofinal : forall G phi,
  Formula.Prov G phi -> exists n, RestrictedProv n G phi.
Proof.
  intros G phi h.
  destruct (ProvTree_complete G phi h) as [d _].
  destruct (ProofAllBounded_cofinal G phi d) as [n hn].
  exists n, d.
  exact hn.
Qed.

Lemma RestrictedBProv_cofinal : forall B G phi,
  Formula.BProv B G phi -> exists n, RestrictedBProv n B G phi.
Proof.
  intros B G phi [L [hL h]].
  destruct (ProvTree_complete (L ++ G) phi h) as [d _].
  destruct (ProofAllBounded_cofinal (L ++ G) phi d) as [n hn].
  exists n, L.
  split; [exact hL |].
  exists d.
  exact hn.
Qed.

(** A deliberately inadequate conclusion-only restriction, included to
    make the Gödel-II pitfall executable: bottom has no quantifiers, so
    conclusion-only bounded consistency is exactly ordinary consistency. *)
Definition ConclusionRestrictedProv (n : nat) (G : list formula)
    (phi : formula) : Prop :=
  Formula.Prov G phi /\ QuantifierBounded n phi.

Definition ConclusionRestrictedBProv (n : nat) (B : formula -> Prop)
    (G : list formula) (phi : formula) : Prop :=
  Formula.BProv B G phi /\ QuantifierBounded n phi.

Lemma quantifierGroups_bot : quantifierGroups pBot = 0.
Proof. reflexivity. Qed.

Lemma ConclusionRestrictedProv_bot_iff : forall n G,
  ConclusionRestrictedProv n G pBot <-> Formula.Prov G pBot.
Proof.
  intros n G.
  unfold ConclusionRestrictedProv, QuantifierBounded.
  rewrite quantifierGroups_bot.
  split.
  - intros [h _]. exact h.
  - intro h. split; [exact h | lia].
Qed.

Lemma ConclusionRestrictedBProv_bot_iff : forall n B G,
  ConclusionRestrictedBProv n B G pBot <-> Formula.BProv B G pBot.
Proof.
  intros n B G.
  unfold ConclusionRestrictedBProv, QuantifierBounded.
  rewrite quantifierGroups_bot.
  split.
  - intros [h _]. exact h.
  - intro h. split; [exact h | lia].
Qed.

(** *External* consistency without a separate consistency hypothesis.
    Erasing the occurrence bound gives an ordinary [BProv] proof.  Soundness
    in the standard natural model, together with validity of every sealed PA
    axiom, rules out a derivation of bottom. *)
Theorem restrictedPA_consistent_standard : forall n,
  ~ RestrictedBProv n Formula.Ax_s [] pBot.
Proof.
  intros n hrestricted.
  pose proof (restrictedBProv_erase n Formula.Ax_s [] pBot hrestricted)
    as hproof.
  pose proof (Formula.soundness_BProv natModel Formula.Ax_s [] pBot
    hproof (fun _ => 0)) as hsound.
  assert (hax : forall b, Formula.Ax_s b ->
      Formula.Sat natModel (fun _ => 0) b).
  {
    intros b hb.
    exact (Formula.sat_axiom_s natModel (fun _ => 0) b hb).
  }
  assert (hctx : forall g, In g ([] : list formula) ->
      Formula.Sat natModel (fun _ => 0) g).
  {
    intros g hg.
    contradiction.
  }
  exact (hsound hax hctx).
Qed.

End PABoundedConsistency.
