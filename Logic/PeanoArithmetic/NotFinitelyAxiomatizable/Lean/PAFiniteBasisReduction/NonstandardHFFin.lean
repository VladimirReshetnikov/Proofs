import PAFiniteBasisReduction.FiniteRankSyntax
import FirstOrder.Relativization
import FirstOrder.Completeness
import PAHF.RawSemantics

/-!
# A nonstandard finite-adjunction model from first-order compactness

This file develops the model-existence ingredient used by the finite-fragment
countermodel construction.  Since the generic completeness theorem in
`FirstOrder.Completeness` is stated for a sentence theory, a shared witness
cannot simply be represented by a free variable.  Instead we add, semantically,
one point with a self-loop.  Quantifiers are relativized to the loop-free part
of the structure, and the looped point names a distinguished ordinal by its
sole outgoing membership edge.

Every finite part of the resulting closed theory has an explicit tagged
Ackermann-HF model.  Compactness therefore supplies one loop-free HFFin model
with an ordinal above every standard numeral.  This is an infrastructure
theorem, not by itself the finite-fragment separation theorem.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA Form

namespace NonstandardHFFin

-- The translated formulas below are intentionally large.  Their proofs are
-- structural, but normalization through sealing and the PA-in-HF translation
-- needs more elaborator depth than Lean's small default.
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-! ## Explicit tagged standard structures -/

/-- One marker point, disjoint from the standard Ackermann-coded HF universe. -/
abbrev Tagged := Unit ⊕ Nat

/-- The marker has a self-loop and points to one selected standard ordinal.
All relations among ordinary points are standard Ackermann membership. -/
def tagMem (height : Nat) : Tagged → Tagged → Prop
  | .inl _, .inl _ => True
  | .inl _, .inr y => y = AckermannHF.ordinalCode height
  | .inr _, .inl _ => False
  | .inr x, .inr y => AckermannHF.Mem x y

/-- Embed a standard HF environment into the ordinary part of a tagged model. -/
def tagEnv (e : Nat → Nat) : Nat → Tagged := fun i => .inr (e i)

@[simp] theorem tagMem_marker_marker (height : Nat) :
    tagMem height (.inl ()) (.inl ()) :=
  trivial

@[simp] theorem tagMem_marker_ordinary (height y : Nat) :
    tagMem height (.inl ()) (.inr y) ↔
      y = AckermannHF.ordinalCode height :=
  Iff.rfl

@[simp] theorem tagMem_ordinary_marker (height x : Nat) :
    ¬ tagMem height (.inr x) (.inl ()) := by
  simp [tagMem]

@[simp] theorem tagMem_ordinary_ordinary (height x y : Nat) :
    tagMem height (.inr x) (.inr y) ↔ AckermannHF.Mem x y :=
  Iff.rfl

/-- Precisely the ordinary points are loop-free. -/
theorem tag_loopFree_iff (height : Nat) (x : Tagged) :
    ¬ tagMem height x x ↔ ∃ n, x = .inr n := by
  cases x with
  | inl u =>
      cases u
      simp [tagMem]
  | inr n =>
      simp [tagMem, AckermannHF.not_mem_self n]

private theorem tagEnv_scons (d : Nat) (e : Nat → Nat) (i : Nat) :
    tagEnv (scons d e) i = scons (Sum.inr d) (tagEnv e) i := by
  cases i <;> rfl

/-- Relativization in a tagged structure recovers ordinary standard-HF
semantics.  This is the concrete finite-model counterpart of
`SetTheory.Sat_relativize`. -/
theorem Sat_tag_relativize (height : Nat) (f : Form) :
    ∀ e : Nat → Nat,
      Sat (tagMem height) (tagEnv e) (relativize f) ↔
        Sat AckermannHF.Mem e f := by
  induction f with
  | fMem i j =>
      intro e
      rfl
  | fEq i j =>
      intro e
      change ((Sum.inr (e i) : Tagged) = Sum.inr (e j)) ↔ e i = e j
      constructor
      · exact Sum.inr.inj
      · exact congrArg Sum.inr
  | fBot =>
      intro e
      rfl
  | fImp a b iha ihb =>
      intro e
      simp only [relativize, Sat]
      rw [iha e, ihb e]
  | fAnd a b iha ihb =>
      intro e
      simp only [relativize, Sat]
      rw [iha e, ihb e]
  | fOr a b iha ihb =>
      intro e
      simp only [relativize, Sat]
      rw [iha e, ihb e]
  | fAll a ih =>
      intro e
      simp only [relativize, Sat, loopFreeAt]
      constructor
      · intro h d
        have hd := h (.inr d) (AckermannHF.not_mem_self d)
        apply (ih (scons d e)).mp
        exact (Sat_ext (relativize a)
          (scons (.inr d) (tagEnv e))
          (tagEnv (scons d e))
          (fun i => (tagEnv_scons d e i).symm)).mp hd
      · intro h d hd
        rcases (tag_loopFree_iff height d).mp hd with ⟨n, rfl⟩
        have ha := (ih (scons n e)).mpr (h n)
        exact (Sat_ext (relativize a)
          (tagEnv (scons n e))
          (scons (.inr n) (tagEnv e))
          (tagEnv_scons n e)).mp ha
  | fEx a ih =>
      intro e
      simp only [relativize, Sat, loopFreeAt]
      constructor
      · rintro ⟨d, hd, ha⟩
        rcases (tag_loopFree_iff height d).mp hd with ⟨n, rfl⟩
        refine ⟨n, (ih (scons n e)).mp ?_⟩
        exact (Sat_ext (relativize a)
          (scons (.inr n) (tagEnv e))
          (tagEnv (scons n e))
          (fun i => (tagEnv_scons n e i).symm)).mp ha
      · rintro ⟨n, ha⟩
        refine ⟨.inr n, AckermannHF.not_mem_self n, ?_⟩
        have ha' := (ih (scons n e)).mpr ha
        exact (Sat_ext (relativize a)
          (tagEnv (scons n e))
          (scons (.inr n) (tagEnv e))
          (tagEnv_scons n e)).mp ha'

/-! ## The closed marker theory -/

/-- Slot `candidate` is an ordinary ordinal-like point named by a looped
marker.  In the tagged standard structures this picks out exactly the ordinal
of the selected height. -/
def candidateAt (candidate : Nat) : Form :=
  fAnd (loopFreeAt candidate)
    (fAnd
      (relativize (AckermannHF.HF_ordinalLikeAt candidate))
      (fEx (fAnd (fMem 0 0) (fMem 0 (candidate + 1)))))

/-- The candidate macro has no free slot other than its displayed one. -/
theorem candidateAt_free {i candidate : Nat}
    (h : Free i (candidateAt candidate)) : i = candidate := by
  simp only [candidateAt, Free] at h
  rcases h with h | h
  · exact (Free_loopFreeAt i candidate).mp h
  · rcases h with h | h
    · exact AckermannHF.HF_ordinalLikeAt_free
        ((Free_relativize i (AckermannHF.HF_ordinalLikeAt candidate)).mp h)
    · rcases h with h | h
      · omega
      · rcases h with h | h <;> omega

/-- Any tagged candidate is the ordinary copy of the selected ordinal.  This
direction works for an arbitrary tagged environment. -/
theorem Sat_candidateAt_unique (height candidate : Nat)
    (e : Nat → Tagged)
    (h : Sat (tagMem height) e (candidateAt candidate)) :
    e candidate = .inr (AckermannHF.ordinalCode height) := by
  rcases (tag_loopFree_iff height (e candidate)).mp h.1 with ⟨y, hy⟩
  rcases h.2.2 with ⟨marker, hloop, hnames⟩
  cases marker with
  | inl u =>
      cases u
      change tagMem height (.inl ()) (e candidate) at hnames
      rw [hy] at hnames
      exact hy.trans (congrArg Sum.inr hnames)
  | inr n =>
      change AckermannHF.Mem n n at hloop
      exact False.elim (AckermannHF.not_mem_self n hloop)

/-- Concrete candidate semantics for an ordinary tagged environment. -/
theorem Sat_tag_candidateAt (height candidate : Nat) (e : Nat → Nat) :
    Sat (tagMem height) (tagEnv e) (candidateAt candidate) ↔
      e candidate = AckermannHF.ordinalCode height := by
  constructor
  · intro h
    have hu := Sat_candidateAt_unique height candidate (tagEnv e) h
    exact Sum.inr.inj hu
  · intro h
    refine ⟨AckermannHF.not_mem_self (e candidate), ?_, ?_⟩
    · apply (Sat_tag_relativize height
        (AckermannHF.HF_ordinalLikeAt candidate) e).mpr
      exact AckermannHF.HF_ordinalLikeAt_of_ordinalCode e candidate height h
    · refine ⟨.inl (), trivial, ?_⟩
      exact h

/-- Conversely, any environment assigning the chosen ordinary ordinal to the
candidate slot satisfies the candidate macro. -/
theorem Sat_candidateAt_of_eq (height candidate : Nat) (e : Nat → Tagged)
    (h : e candidate = .inr (AckermannHF.ordinalCode height)) :
    Sat (tagMem height) e (candidateAt candidate) := by
  let std : Nat → Nat := fun _ => AckermannHF.ordinalCode height
  have hstd : Sat (tagMem height) (tagEnv std) (candidateAt candidate) :=
    (Sat_tag_candidateAt height candidate std).mpr rfl
  exact (Sat_ext_free (candidateAt candidate)
    (tagEnv std) e (fun i hi => by
      have hic := candidateAt_free hi
      subst i
      exact h.symm)).mp hstd

/-- The closed assertion that some candidate exists.  One explicit quantifier
is enough because `candidateAt 0` has exactly slot zero free. -/
def candidateExists : Form := fEx (candidateAt 0)

theorem Sentence_candidateExists : Sentence candidateExists := by
  intro i hi
  simp only [candidateExists, Free] at hi
  have := candidateAt_free hi
  omega

/-- Every tagged standard structure satisfies candidate existence. -/
theorem Sat_tag_candidateExists (height : Nat) (e : Nat → Tagged) :
    Sat (tagMem height) e candidateExists := by
  refine ⟨.inr (AckermannHF.ordinalCode height), ?_⟩
  exact Sat_candidateAt_of_eq height 0 _ rfl

/-- The PA formula `numeral n < variable 0`. -/
def paLtNumeralAt (n : Nat) : PA.Formula :=
  PA.Formula.ltTermAt (PA.Term.numeral n) (PA.Term.var 0)

private theorem not_termFree_numeral (i n : Nat) :
    ¬ PA.Term.Free i (PA.Term.numeral n) := by
  induction n with
  | zero => simp [PA.Term.numeral, PA.Term.Free]
  | succ n ih => simpa [PA.Term.numeral, PA.Term.Free] using ih

/-- Translate the PA bound into HF and then restrict every HF quantifier to
the loop-free part of the ambient marker structure. -/
def hfLtNumeralAt (n : Nat) : Form :=
  relativize (AckermannHF.PAInHF.formulaAt (fun i => i) (paLtNumeralAt n))

/-- The translated bound has only the distinguished candidate slot free. -/
theorem hfLtNumeralAt_free {i n : Nat} (h : Free i (hfLtNumeralAt n)) :
    i = 0 := by
  have h' := (Free_relativize i
    (AckermannHF.PAInHF.formulaAt (fun k => k) (paLtNumeralAt n))).mp h
  rcases AckermannHF.PAInHF.formulaAt_free (paLtNumeralAt n) h' with
    ⟨k, hk, hik⟩
  have hk0 : k = 0 := by
    simp only [paLtNumeralAt, PA.Formula.ltTermAt, PA.Formula.Free,
      PA.Term.Free, PA.Term.rename, PA.Term.rename_numeral,
      not_termFree_numeral, false_or] at hk
    omega
  simpa [hk0] using hik

/-- Closed sentence: every named candidate is above the standard numeral
`n` in the interpreted arithmetic.  As with candidate existence, the one
displayed quantifier closes the only free slot. -/
def starBound (n : Nat) : Form :=
  fAll (fImp (candidateAt 0) (hfLtNumeralAt n))

theorem Sentence_starBound (n : Nat) : Sentence (starBound n) := by
  intro i hi
  simp only [starBound, Free] at hi
  rcases hi with hi | hi
  · have := candidateAt_free hi
    omega
  · have := hfLtNumeralAt_free hi
    omega

/-- Exact finite tagged-model semantics of a translated arithmetic bound,
provided slot zero denotes the tagged model's selected ordinal. -/
theorem Sat_tag_hfLtNumeralAt_iff (height n : Nat) (e : Nat → Tagged)
    (he : e 0 = .inr (AckermannHF.ordinalCode height)) :
    Sat (tagMem height) e (hfLtNumeralAt n) ↔ n < height := by
  let v : Nat → Nat := fun _ => height
  let hfEnv : Nat → Nat := fun i => AckermannHF.ordinalCode (v i)
  have hfree :
      Sat (tagMem height) (tagEnv hfEnv) (hfLtNumeralAt n) ↔
        Sat (tagMem height) e (hfLtNumeralAt n) :=
    Sat_ext_free (hfLtNumeralAt n) (tagEnv hfEnv) e (fun i hi => by
      have hi0 := hfLtNumeralAt_free hi
      subst i
      exact he.symm)
  have hrel :
      Sat (tagMem height) (tagEnv hfEnv) (hfLtNumeralAt n) ↔
        Sat AckermannHF.Mem hfEnv
          (AckermannHF.PAInHF.formulaAt (fun i => i) (paLtNumeralAt n)) :=
    Sat_tag_relativize height _ hfEnv
  have hexact :
      Sat AckermannHF.Mem hfEnv
          (AckermannHF.PAInHF.formulaAt (fun i => i) (paLtNumeralAt n)) ↔
        PA.Formula.Sat PA.natModel v (paLtNumeralAt n) :=
    AckermannHF.PAInHF.formulaAt_exact (paLtNumeralAt n)
      (fun i => i) v hfEnv (fun i => rfl)
  have hltExact :
      PA.Formula.Sat PA.natModel v (paLtNumeralAt n) ↔ n < height := by
    unfold paLtNumeralAt
    rw [PA.Formula.ltTermAt_nat]
    rw [PA.Term.eval_numeral_natModel]
    rfl
  exact hfree.symm.trans (hrel.trans (hexact.trans hltExact))

/-- A closed bound sentence is true in the height-`height` tagged model
exactly below that height. -/
theorem Sat_tag_starBound_iff (height n : Nat) (e : Nat → Tagged) :
    Sat (tagMem height) e (starBound n) ↔ n < height := by
  constructor
  · intro h
    let candidate : Tagged := .inr (AckermannHF.ordinalCode height)
    let env := scons candidate e
    have hc : Sat (tagMem height) env (candidateAt 0) :=
      Sat_candidateAt_of_eq height 0 env rfl
    exact (Sat_tag_hfLtNumeralAt_iff height n env rfl).mp (h candidate hc)
  · intro hlt
    intro candidate hc
    exact (Sat_tag_hfLtNumeralAt_iff height n (scons candidate e)
      (Sat_candidateAt_unique height 0 (scons candidate e) hc)).mpr hlt

/-- Distinct standard bounds really are distinct closed formulas.  The proof
uses their exact threshold semantics rather than a brittle syntactic
injectivity calculation through sealing and translation. -/
theorem starBound_injective : Function.Injective starBound := by
  intro n m hnm
  rcases Nat.lt_trichotomy n m with hlt | heq | hgt
  · let e : Nat → Tagged := fun _ => .inr 0
    have hn : Sat (tagMem m) e (starBound n) :=
      (Sat_tag_starBound_iff m n e).mpr hlt
    rw [hnm] at hn
    have := (Sat_tag_starBound_iff m m e).mp hn
    omega
  · exact heq
  · let e : Nat → Tagged := fun _ => .inr 0
    have hm : Sat (tagMem n) e (starBound m) :=
      (Sat_tag_starBound_iff n m e).mpr hgt
    rw [← hnm] at hm
    have := (Sat_tag_starBound_iff n n e).mp hm
    omega

/-- Relativized HFFin, one named ordinal, and all its standard lower bounds. -/
def Ax (f : Form) : Prop :=
  (∃ g, AckermannHF.HFFinAx_s g ∧ f = relativize g) ∨
  f = candidateExists ∨
  ∃ n, f = starBound n

theorem Sentences_Ax : Sentences Ax := by
  intro f hf
  rcases hf with ⟨g, hg, rfl⟩ | rfl | ⟨n, rfl⟩
  · exact Sentence_relativize (AckermannHF.Sentences_HFFin g hg)
  · exact Sentence_candidateExists
  · exact Sentence_starBound n

/-- Every finite list of formulas has a tagged-model height above every bound
sentence occurring in that list. -/
theorem exists_tagHeight (fs : List Form) :
    ∃ height, ∀ f ∈ fs, ∀ n, f = starBound n → n < height := by
  induction fs with
  | nil =>
      exact ⟨0, by simp⟩
  | cons f fs ih =>
      rcases ih with ⟨height, hheight⟩
      by_cases hf : ∃ n, f = starBound n
      · rcases hf with ⟨k, hk⟩
        refine ⟨max (k + 1) height, ?_⟩
        intro g hg n hn
        rcases List.mem_cons.mp hg with rfl | hg
        · have hnk : n = k := starBound_injective (hn.symm.trans hk)
          subst n
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_left _ _)
        · exact Nat.lt_of_lt_of_le (hheight g hg n hn) (Nat.le_max_right _ _)
      · refine ⟨height, ?_⟩
        intro g hg n hn
        rcases List.mem_cons.mp hg with rfl | hg
        · exact False.elim (hf ⟨n, hn⟩)
        · exact hheight g hg n hn

/-- Finite satisfiability, packaged in the relative consistency notion used by
the generic first-order completeness theorem. -/
theorem Ax_BCon : BCon Ax [] := by
  intro hbad
  rcases hbad with ⟨used, hused, hp⟩
  rcases exists_tagHeight used with ⟨height, hheight⟩
  let e : Nat → Tagged := fun _ => .inr 0
  have hs : ∀ f ∈ used, Sat (tagMem height) e f := by
    intro f hf
    rcases hused f hf with ⟨g, hg, rfl⟩ | rfl | ⟨n, rfl⟩
    · exact (Sat_tag_relativize height g (fun _ => 0)).mpr
        (AckermannHF.standard_sat_HFFin (fun _ => 0) g hg)
    · exact Sat_tag_candidateExists height e
    · exact (Sat_tag_starBound_iff height n e).mpr
        (hheight (starBound n) hf n rfl)
  have hfalse : Sat (tagMem height) e fBot := by
    apply SetTheory.soundness hp e
    intro f hf
    apply hs f
    simpa using hf
  exact hfalse

/-! ## Compactness and decoding the loop-free model -/

/-- Compactness yields a finite-adjunction model with an ordinal-like point
above every standard numeral, first stated directly through the PA-in-HF
translation. -/
theorem nonstandardHFFin_translated_exists :
    ∃ (V : Type) (M : AckermannHF.FirstOrderFiniteAdjunctionModel V)
      (star : V),
      AckermannHF.OrdinalLike M.mem star ∧
      ∀ n, Sat M.mem (fun _ => star)
        (AckermannHF.PAInHF.formulaAt (fun i => i) (paLtNumeralAt n)) := by
  rcases model_of_BCon Ax [] Sentences_Ax Ax_BCon with
    ⟨Dom, mem, v, hAx, _⟩
  have hCandidateExists : Sat mem v candidateExists :=
    hAx candidateExists (Or.inr (Or.inl rfl))
  rcases hCandidateExists with ⟨c, hc⟩
  let star : RelDomain mem := ⟨c, hc.1⟩
  let envD : Nat → RelDomain mem := fun _ => star
  have hHFFin : ∀ g, AckermannHF.HFFinAx_s g →
      Sat (relDomainMem mem) envD g := by
    intro g hg
    have hAtV : Sat mem v (relativize g) :=
      hAx (relativize g) (Or.inl ⟨g, hg, rfl⟩)
    have hAtD : Sat mem (fun i => (envD i).1) (relativize g) :=
      (Sat_sentence_inv (relativize g)
        (Sentence_relativize (AckermannHF.Sentences_HFFin g hg))
        v (fun i => (envD i).1)).mp hAtV
    exact (Sat_relativize g envD).mp hAtD
  let M : AckermannHF.FirstOrderFiniteAdjunctionModel (RelDomain mem) :=
    AckermannHF.firstOrderFiniteAdjunctionModel_of_HFFinAx_s envD hHFFin
  have hcOrdinalAmbient :
      Sat mem (fun _ => c)
        (relativize (AckermannHF.HF_ordinalLikeAt 0)) := by
    exact (Sat_ext_free
      (relativize (AckermannHF.HF_ordinalLikeAt 0))
      (scons c v) (fun _ => c) (fun i hi => by
        have hi0 := AckermannHF.HF_ordinalLikeAt_free
          ((Free_relativize i (AckermannHF.HF_ordinalLikeAt 0)).mp hi)
        subst i
        rfl)).mp hc.2.1
  have hcOrdinalSat :
      Sat (relDomainMem mem) envD (AckermannHF.HF_ordinalLikeAt 0) := by
    apply (Sat_relativize (AckermannHF.HF_ordinalLikeAt 0) envD).mp
    exact hcOrdinalAmbient
  have hcOrdinal : AckermannHF.OrdinalLike (relDomainMem mem) star :=
    (AckermannHF.HF_ordinalLikeAt_spec envD 0).mp hcOrdinalSat
  refine ⟨RelDomain mem, M, star, ?_, ?_⟩
  · change AckermannHF.OrdinalLike (relDomainMem mem) star
    exact hcOrdinal
  · intro n
    have hBoundSentence : Sat mem v (starBound n) :=
      hAx (starBound n) (Or.inr (Or.inr ⟨n, rfl⟩))
    have hBoundAmbient : Sat mem (scons c v) (hfLtNumeralAt n) :=
      hBoundSentence c hc
    have hBoundConstant : Sat mem (fun _ => c) (hfLtNumeralAt n) :=
      (Sat_ext_free (hfLtNumeralAt n) (scons c v) (fun _ => c)
        (fun i hi => by
          have hi0 := hfLtNumeralAt_free hi
          subst i
          rfl)).mp hBoundAmbient
    change Sat (relDomainMem mem) envD
      (AckermannHF.PAInHF.formulaAt (fun i => i) (paLtNumeralAt n))
    exact (Sat_relativize
      (AckermannHF.PAInHF.formulaAt (fun i => i) (paLtNumeralAt n))
      envD).mp hBoundConstant

/-- The same compactness model expressed in the raw PA `PreModel` on its
ordinal-like carrier.  No meta-level PA induction field is assumed. -/
theorem nonstandardHFFin_fofam_exists :
    ∃ (V : Type) (M : AckermannHF.FirstOrderFiniteAdjunctionModel V)
      (star : AckermannHF.PAInHF.FOFAMOrdinal M),
      ∀ n, AckermannHF.PAInHF.fofamPAFormulaSat M (fun _ => star)
        (paLtNumeralAt n) := by
  rcases nonstandardHFFin_translated_exists with ⟨V, M, star, hord, hbound⟩
  let starOrdinal : AckermannHF.PAInHF.FOFAMOrdinal M := ⟨star, hord⟩
  refine ⟨V, M, starOrdinal, ?_⟩
  intro n
  apply (AckermannHF.PAInHF.formulaAt_iff_fofamPAFormulaSat M
    (paLtNumeralAt n) (fun i => i) (fun _ => star)
    (fun _ => starOrdinal) (fun _ _ => rfl)).mp
  exact hbound n

end NonstandardHFFin

end PAFiniteBasisReduction
end LeanProofs
