import SetTheory.PAHF.RoundTrip

namespace SetTheory
namespace AckermannHF

open Form

/-- A total two-slot map.  PA variable `0` is read from `elemCode`; every
positive variable is read from `setCode`.  The translated membership formula
below only has variables `0` and `1` free, while totality of this map makes the
standard exactness theorem directly applicable. -/
def repPairSlotMap (elemCode setCode : Nat) : Nat → Nat
  | 0 => elemCode
  | _+1 => setCode

def repPairNatMap (elemCode setCode : Nat) : Nat → Nat
  | 0 => elemCode
  | _+1 => setCode

/-- The HF formula obtained by translating Ackermann membership between two
PA numbers represented by finite ordinals in the indicated HF slots. -/
def HF_compositeMemAt (elemCode setCode : Nat) : Form :=
  PAInHF.formulaAt (repPairSlotMap elemCode setCode)
    (PA.Formula.hfMemAt 0 1)

/-- Exact standard semantics of the composite membership atom on two
finite-ordinal inputs. -/
theorem HF_compositeMemAt_exact_codes
    (e : Nat → Nat) (elemCode setCode rawElem rawSet : Nat)
    (helem : e elemCode = ordinalCode rawElem)
    (hset : e setCode = ordinalCode rawSet) :
    Sat Mem e (HF_compositeMemAt elemCode setCode) ↔
      Mem rawElem rawSet := by
  let v : Nat → Nat := repPairNatMap rawElem rawSet
  have hslots : ∀ n,
      e (repPairSlotMap elemCode setCode n) = ordinalCode (v n) := by
    intro n
    cases n with
    | zero => exact helem
    | succ n => exact hset
  exact
    (PAInHF.formulaAt_exact (PA.Formula.hfMemAt 0 1)
      (repPairSlotMap elemCode setCode) v e hslots).trans
      (by
        simpa [v, repPairNatMap] using
          (PA.Formula.hfMemAt_exact v 0 1))

/-- Semantic relation expressed by the translated coded-membership atom. -/
def CompositeMemObj (elemCode setCode : Nat) : Prop :=
  ∃ rawElem rawSet,
    elemCode = ordinalCode rawElem ∧
      setCode = ordinalCode rawSet ∧
      Mem rawElem rawSet

theorem HF_compositeMemAt_exact_of_ordinal
    (e : Nat → Nat) (elemCode setCode : Nat)
    (helem : IsOrdinalCode (e elemCode))
    (hset : IsOrdinalCode (e setCode)) :
    Sat Mem e (HF_compositeMemAt elemCode setCode) ↔
      CompositeMemObj (e elemCode) (e setCode) := by
  rcases helem with ⟨rawElem, helem⟩
  rcases hset with ⟨rawSet, hset⟩
  have hspec := HF_compositeMemAt_exact_codes e elemCode setCode
    rawElem rawSet helem.symm hset.symm
  constructor
  · intro h
    exact ⟨rawElem, rawSet, helem.symm, hset.symm, hspec.mp h⟩
  · intro h
    rcases h with ⟨rawElem', rawSet', helem', hset', hmem⟩
    have hrawElem : rawElem' = rawElem :=
      ordinalCode_injective (helem'.symm.trans helem.symm)
    have hrawSet : rawSet' = rawSet :=
      ordinalCode_injective (hset'.symm.trans hset.symm)
    subst rawElem'
    subst rawSet'
    exact hspec.mpr hmem

/-- A finite graph certificate is single-valued and is recursively closed under
membership: if `(x,n)` belongs to it, then `n` is a finite ordinal, and the
members of `x` correspond exactly to graph pairs whose ordinal codes satisfy
the translated Ackermann-membership atom against `n`. -/
def HF_setOrdinalRepCertificateAt (relation : Nat) : Form :=
  fAnd
    (HF_pairFunctionalAt relation)
    (fAll (fAll
      (fImp
        (HF_pairMemAt 1 0 (relation+2))
        (fAnd
          (HF_ordinalLikeAt 0)
          (fAnd
            (fAll
              (fIff
                (fMem 0 2)
                (fEx
                  (fAnd
                    (HF_pairMemAt 1 0 (relation+4))
                    (HF_compositeMemAt 0 2)))))
            (fAll
              (fImp
                (fAnd
                  (HF_ordinalLikeAt 0)
                  (HF_compositeMemAt 0 1))
                (fEx
                  (HF_pairMemAt 0 1 (relation+4))))))))))

/-- Slot `set` is paired with finite ordinal `code` by some finite recursive
representation certificate. -/
def HF_setOrdinalRepAt (set code : Nat) : Form :=
  fEx
    (fAnd
      (HF_pairMemAt (set+1) (code+1) 0)
      (HF_setOrdinalRepCertificateAt 0))

/-- Semantic reading of a representation certificate in standard Ackermann
HF. -/
def SetOrdinalRepCertificate (relation : Nat) : Prop :=
  PairFunctional standardModel relation ∧
    ∀ set code,
      Mem (kpair standardModel set code) relation →
        IsOrdinalCode code ∧
          (∀ elem,
              Mem elem set ↔
                ∃ elemCode,
                  Mem (kpair standardModel elem elemCode)
                      relation ∧
                    CompositeMemObj elemCode code) ∧
            ∀ elemCode,
              IsOrdinalCode elemCode →
              CompositeMemObj elemCode code →
                ∃ elem,
                  Mem (kpair standardModel elem elemCode) relation

/-- Semantic reading of the representation formula. -/
def SetOrdinalRep (set code : Nat) : Prop :=
  ∃ relation,
    Mem (kpair standardModel set code) relation ∧
      SetOrdinalRepCertificate relation

/-- Exact standard semantics of the finite recursive representation
certificate. -/
theorem HF_setOrdinalRepCertificateAt_exact
    (e : Nat → Nat) (relation : Nat) :
    Sat Mem e (HF_setOrdinalRepCertificateAt relation) ↔
      SetOrdinalRepCertificate (e relation) := by
  constructor
  · intro h
    refine ⟨(HF_pairFunctionalAt_spec standardModel e relation).mp h.1,
      ?_⟩
    intro set code hpair
    let E : Nat → Nat := scons code (scons set e)
    have hpairSat : Sat Mem E (HF_pairMemAt 1 0 (relation+2)) := by
      apply (HF_pairMemAt_spec standardModel E 1 0 (relation+2)).mpr
      simpa [standardModel, E, scons] using hpair
    have hlocal := h.2 set code hpairSat
    have hcodeOrd : IsOrdinalCode code := by
      have hspec := (HF_ordinalLikeAt_exact E 0).mp hlocal.1
      simpa [E, scons] using hspec
    refine ⟨hcodeOrd, ?_, ?_⟩
    intro elem
    have hpoint := hlocal.2.1 elem
    rw [Sat_fIff] at hpoint
    constructor
    · intro hmem
      have hmemSat : Sat Mem (scons elem E) (fMem 0 2) := by
        change Mem elem set
        exact hmem
      rcases hpoint.mp hmemSat with ⟨elemCode, hchildSat, hcodedSat⟩
      have hchild :
          Mem (kpair standardModel elem elemCode) (e relation) := by
        have hspec := (HF_pairMemAt_spec standardModel
          (scons elemCode (scons elem E)) 1 0 (relation+4)).mp hchildSat
        simpa [standardModel, E, scons] using hspec
      have hchildLocal := h.2 elem elemCode
      have hchildSat' : Sat Mem
          (scons elemCode (scons elem e))
          (HF_pairMemAt 1 0 (relation+2)) := by
        apply (HF_pairMemAt_spec standardModel
          (scons elemCode (scons elem e)) 1 0 (relation+2)).mpr
        simpa [standardModel, scons] using hchild
      have helemOrd : IsOrdinalCode elemCode := by
        have hspec := (HF_ordinalLikeAt_exact
          (scons elemCode (scons elem e)) 0).mp
          (hchildLocal hchildSat').1
        simpa [scons] using hspec
      have hcoded : CompositeMemObj elemCode code := by
        have hspec := (HF_compositeMemAt_exact_of_ordinal
          (scons elemCode (scons elem E)) 0 2
          (by simpa [E, scons] using helemOrd)
          (by simpa [E, scons] using hcodeOrd)).mp hcodedSat
        simpa [E, scons] using hspec
      exact ⟨elemCode, hchild, hcoded⟩
    · intro hmem
      rcases hmem with ⟨elemCode, hchild, hcoded⟩
      have hchildSat : Sat Mem
          (scons elemCode (scons elem E))
          (HF_pairMemAt 1 0 (relation+4)) := by
        apply (HF_pairMemAt_spec standardModel
          (scons elemCode (scons elem E)) 1 0 (relation+4)).mpr
        simpa [standardModel, E, scons] using hchild
      have helemOrd : IsOrdinalCode elemCode := by
        have hchildSat' : Sat Mem
            (scons elemCode (scons elem e))
            (HF_pairMemAt 1 0 (relation+2)) := by
          apply (HF_pairMemAt_spec standardModel
            (scons elemCode (scons elem e)) 1 0 (relation+2)).mpr
          simpa [standardModel, scons] using hchild
        have hspec := (HF_ordinalLikeAt_exact
          (scons elemCode (scons elem e)) 0).mp
          (h.2 elem elemCode hchildSat').1
        simpa [scons] using hspec
      have hcodedSat : Sat Mem
          (scons elemCode (scons elem E))
          (HF_compositeMemAt 0 2) := by
        apply (HF_compositeMemAt_exact_of_ordinal
          (scons elemCode (scons elem E)) 0 2
          (by simpa [E, scons] using helemOrd)
          (by simpa [E, scons] using hcodeOrd)).mpr
        simpa [E, scons] using hcoded
      have hrhs : Sat Mem (scons elem E)
          (fEx
            (fAnd
              (HF_pairMemAt 1 0 (relation+4))
              (HF_compositeMemAt 0 2))) :=
        ⟨elemCode, hchildSat, hcodedSat⟩
      have hmemSat := hpoint.mpr hrhs
      change Mem elem set at hmemSat
      exact hmemSat
    · intro elemCode helemOrd hcoded
      let EC : Nat → Nat := scons elemCode E
      have helemOrdSat : Sat Mem EC (HF_ordinalLikeAt 0) := by
        apply (HF_ordinalLikeAt_exact EC 0).mpr
        simpa [EC, scons] using helemOrd
      have hcodedSat : Sat Mem EC (HF_compositeMemAt 0 1) := by
        apply (HF_compositeMemAt_exact_of_ordinal EC 0 1
          (by simpa [EC, scons] using helemOrd)
          (by simpa [EC, E, scons] using hcodeOrd)).mpr
        simpa [EC, E, scons] using hcoded
      rcases hlocal.2.2 elemCode ⟨helemOrdSat, hcodedSat⟩ with
        ⟨elem, hpairSat⟩
      refine ⟨elem, ?_⟩
      have hspec := (HF_pairMemAt_spec standardModel
        (scons elem EC) 0 1 (relation+4)).mp hpairSat
      simpa [standardModel, EC, E, scons] using hspec
  · intro h
    refine ⟨(HF_pairFunctionalAt_spec standardModel e relation).mpr h.1,
      ?_⟩
    intro set code hpairSat
    let E : Nat → Nat := scons code (scons set e)
    have hpair :
        Mem (kpair standardModel set code) (e relation) := by
      have hspec := (HF_pairMemAt_spec standardModel E 1 0
        (relation+2)).mp (by simpa [standardModel, E] using hpairSat)
      simpa [standardModel, E, scons] using hspec
    have hlocal := h.2 set code hpair
    refine ⟨?_, ?_, ?_⟩
    · apply (HF_ordinalLikeAt_exact E 0).mpr
      simpa [E, scons] using hlocal.1
    · intro elem
      rw [Sat_fIff]
      constructor
      · intro hmemSat
        have hmem : Mem elem set := by
          change Mem elem set at hmemSat
          exact hmemSat
        rcases (hlocal.2.1 elem).mp hmem with
          ⟨elemCode, hchild, hcoded⟩
        refine ⟨elemCode, ?_, ?_⟩
        · apply (HF_pairMemAt_spec standardModel
            (scons elemCode (scons elem E)) 1 0 (relation+4)).mpr
          simpa [standardModel, E, scons] using hchild
        · have helemOrd : IsOrdinalCode elemCode := (h.2 elem elemCode hchild).1
          apply (HF_compositeMemAt_exact_of_ordinal
            (scons elemCode (scons elem E)) 0 2
            (by simpa [E, scons] using helemOrd)
            (by simpa [E, scons] using hlocal.1)).mpr
          simpa [E, scons] using hcoded
      · intro hrhs
        rcases hrhs with ⟨elemCode, hchildSat, hcodedSat⟩
        have hchild :
            Mem (kpair standardModel elem elemCode) (e relation) := by
          have hspec := (HF_pairMemAt_spec standardModel
            (scons elemCode (scons elem E)) 1 0 (relation+4)).mp hchildSat
          simpa [standardModel, E, scons] using hspec
        have helemOrd : IsOrdinalCode elemCode := (h.2 elem elemCode hchild).1
        have hcoded : CompositeMemObj elemCode code := by
          have hspec := (HF_compositeMemAt_exact_of_ordinal
            (scons elemCode (scons elem E)) 0 2
            (by simpa [E, scons] using helemOrd)
            (by simpa [E, scons] using hlocal.1)).mp hcodedSat
          simpa [E, scons] using hspec
        have hmem := (hlocal.2.1 elem).mpr ⟨elemCode, hchild, hcoded⟩
        change Mem elem set
        exact hmem
    · intro elemCode hant
      have helemOrd : IsOrdinalCode elemCode := by
        have hspec := (HF_ordinalLikeAt_exact
          (scons elemCode E) 0).mp hant.1
        simpa [E, scons] using hspec
      have hcoded : CompositeMemObj elemCode code := by
        have hspec := (HF_compositeMemAt_exact_of_ordinal
          (scons elemCode E) 0 1
          (by simpa [E, scons] using helemOrd)
          (by simpa [E, scons] using hlocal.1)).mp hant.2
        simpa [E, scons] using hspec
      rcases hlocal.2.2 elemCode helemOrd hcoded with ⟨elem, hpair⟩
      refine ⟨elem, ?_⟩
      apply (HF_pairMemAt_spec standardModel
        (scons elem (scons elemCode E)) 0 1 (relation+4)).mpr
      simpa [standardModel, E, scons] using hpair

/-- Exact standard semantics of the root representation relation. -/
theorem HF_setOrdinalRepAt_exact
    (e : Nat → Nat) (set code : Nat) :
    Sat Mem e (HF_setOrdinalRepAt set code) ↔
      SetOrdinalRep (e set) (e code) := by
  constructor
  · intro h
    rcases h with ⟨relation, hrootSat, hcertSat⟩
    refine ⟨relation, ?_, ?_⟩
    · have hspec := (HF_pairMemAt_spec standardModel
        (scons relation e) (set+1) (code+1) 0).mp hrootSat
      simpa [standardModel, scons] using hspec
    · have hspec := (HF_setOrdinalRepCertificateAt_exact
        (scons relation e) 0).mp hcertSat
      simpa [scons] using hspec
  · intro h
    rcases h with ⟨relation, hroot, hcert⟩
    refine ⟨relation, ?_, ?_⟩
    · apply (HF_pairMemAt_spec standardModel
        (scons relation e) (set+1) (code+1) 0).mpr
      simpa [standardModel, scons] using hroot
    · apply (HF_setOrdinalRepCertificateAt_exact
        (scons relation e) 0).mpr
      simpa [scons] using hcert

/-- Formula-level HF composite with an explicit map from the intermediate PA
variables to their finite-ordinal HF slots. -/
def hfCompositeAt (codedMap : Nat → Nat) (phi : Form) : Form :=
  PAInHF.formulaAt codedMap
    (PA.Formula.hfFormulaAt (fun n : Nat => n) phi)

theorem hfCompositeAt_id (phi : Form) :
    hfCompositeAt (fun n : Nat => n) phi =
      PAInHF.translateFormula (PA.Formula.translateHFFormula phi) := rfl

/-- Exact proof-theoretic frontier for the internal set-to-ordinal
representation relation.  Totality and range are both needed for translated
quantifiers; the two uniqueness directions handle equality; `mem_exact` is the
atomic membership bridge. -/
structure SetOrdinalRepresentationProofs where
  total : ∀ (G : List Form) (set : Nat),
    BProv HFFinAx_s G
      (fEx (HF_setOrdinalRepAt (set+1) 0))
  range : ∀ (G : List Form) (code : Nat),
    BProv HFFinAx_s G
      (fIff
        (HF_ordinalLikeAt code)
        (fEx (HF_setOrdinalRepAt 0 (code+1))))
  code_functional : ∀ {G : List Form} {set code₁ code₂ : Nat},
    BProv HFFinAx_s G (HF_setOrdinalRepAt set code₁) →
    BProv HFFinAx_s G (HF_setOrdinalRepAt set code₂) →
    BProv HFFinAx_s G (fEq code₁ code₂)
  set_injective : ∀ {G : List Form} {set₁ set₂ code : Nat},
    BProv HFFinAx_s G (HF_setOrdinalRepAt set₁ code) →
    BProv HFFinAx_s G (HF_setOrdinalRepAt set₂ code) →
    BProv HFFinAx_s G (fEq set₁ set₂)
  mem_exact : ∀ {G : List Form}
      {elem set elemCode setCode : Nat},
    BProv HFFinAx_s G (HF_setOrdinalRepAt elem elemCode) →
    BProv HFFinAx_s G (HF_setOrdinalRepAt set setCode) →
    BProv HFFinAx_s G
      (fIff (fMem elem set)
        (HF_compositeMemAt elemCode setCode))

/-- Conditional paired-variable formula-induction package for the HF-side
composite. -/
structure HFCompositeStructuralProofs extends SetOrdinalRepresentationProofs where
  formula_exact : ∀ (G : List Form) (phi : Form)
      (rawMap codedMap : Nat → Nat),
    (∀ n, Free n phi →
      BProv HFFinAx_s G
        (HF_setOrdinalRepAt (rawMap n) (codedMap n))) →
    BProv HFFinAx_s G
      (fIff (rename rawMap phi) (hfCompositeAt codedMap phi))

/-- A completed paired-variable structural induction closes the HF composite
identity on sentences. -/
theorem BProv_HFFin_hf_roundTrip_of_structuralProofs
    (P : HFCompositeStructuralProofs)
    (phi : Form) (hphi : Sentence phi) :
    BProv HFFinAx_s []
      (fIff phi
        (PAInHF.translateFormula
          (PA.Formula.translateHFFormula phi))) := by
  have h := P.formula_exact [] phi
    (fun n : Nat => n) (fun n : Nat => n)
    (fun n hn => False.elim (hphi n hn))
  simpa [hfCompositeAt_id, rename_id] using h

/-- Assembly point for both structural round-trip packages. -/
def PAHFFinDeductiveBiInterpretationCertificate_of_structuralProofs
    (PPA : PA.Formula.PACompositeStructuralProofs)
    (PHF : HFCompositeStructuralProofs) :
    PAHFFinDeductiveBiInterpretationCertificate :=
  PAHFFinDeductiveBiInterpretationCertificate_of_codeStructuralProofs
    PPA
    (fun phi hphi =>
      BProv_HFFin_hf_roundTrip_of_structuralProofs PHF phi hphi)

theorem SetOrdinalRep_code_eq :
  ∀ set code, SetOrdinalRep set code → code = ordinalCode set := by
  intro set
  exact Nat.strongRecOn set (fun set ih => by
      intro code hrep
      rcases hrep with ⟨relation, hroot, hcert⟩
      have hlocal := hcert.2 set code hroot
      rcases hlocal.1 with ⟨rawCode, hcode⟩
      have hset : set = rawCode := by
        apply AckermannHF.ext
        intro elem
        constructor
        · intro helemSet
          rcases (hlocal.2.1 elem).mp helemSet with
            ⟨elemCode, hchildPair, hcoded⟩
          rcases hcoded with
            ⟨rawElem, rawSet, helemCode, hsetCode, hrawMem⟩
          have hchildRep : SetOrdinalRep elem elemCode :=
            ⟨relation, hchildPair, hcert⟩
          have hchildCode : elemCode = ordinalCode elem :=
            ih elem (mem_lt helemSet) elemCode hchildRep
          have hrawElem : rawElem = elem :=
            ordinalCode_injective (helemCode.symm.trans hchildCode)
          have hrawSet : rawSet = rawCode :=
            (ordinalCode_injective (hcode.trans hsetCode)).symm
          simpa [hrawElem, hrawSet] using hrawMem
        · intro helemRaw
          let elemCode : Nat := ordinalCode elem
          have helemOrd : IsOrdinalCode elemCode :=
            ⟨elem, rfl⟩
          have hcoded : CompositeMemObj elemCode code :=
            ⟨elem, rawCode, rfl, hcode.symm, helemRaw⟩
          rcases hlocal.2.2 elemCode helemOrd hcoded with
            ⟨setElem, hchildPair⟩
          have hsetElemMem : Mem setElem set :=
            (hlocal.2.1 setElem).mpr
              ⟨elemCode, hchildPair, hcoded⟩
          have hchildRep : SetOrdinalRep setElem elemCode :=
            ⟨relation, hchildPair, hcert⟩
          have hchildCode : elemCode = ordinalCode setElem :=
            ih setElem (mem_lt hsetElemMem) elemCode hchildRep
          have heq : elem = setElem := by
            apply ordinalCode_injective
            simpa [elemCode] using hchildCode
          simpa [heq] using hsetElemMem
      calc
        code = ordinalCode rawCode := hcode.symm
        _ = ordinalCode set := by rw [hset])

/-- The concrete finite certificate containing `(x, ordinalCode x)` for every
`x ≤ bound`. -/
def standardSetOrdinalRepGraph : Nat → Nat
  | 0 => adjoin empty
      (kpair standardModel 0 (ordinalCode 0))
  | bound+1 => adjoin (standardSetOrdinalRepGraph bound)
      (kpair standardModel (bound+1) (ordinalCode (bound+1)))

theorem mem_standardSetOrdinalRepGraph_iff
    (pair bound : Nat) :
    Mem pair (standardSetOrdinalRepGraph bound) ↔
      ∃ set, set ≤ bound ∧
        pair = kpair standardModel set (ordinalCode set) := by
  induction bound with
  | zero =>
      constructor
      · intro h
        rcases (mem_adjoin pair empty
          (kpair standardModel 0 (ordinalCode 0))).mp h with
          hfalse | hpair
        · exact False.elim (mem_empty pair hfalse)
        · exact ⟨0, Nat.le_refl 0, hpair⟩
      · intro h
        rcases h with ⟨set, hset, hpair⟩
        have hzero : set = 0 := Nat.eq_zero_of_le_zero hset
        subst set
        apply (mem_adjoin pair empty
          (kpair standardModel 0 (ordinalCode 0))).mpr
        exact Or.inr hpair
  | succ bound ih =>
      constructor
      · intro h
        rcases (mem_adjoin pair
          (standardSetOrdinalRepGraph bound)
          (kpair standardModel (bound+1)
            (ordinalCode (bound+1)))).mp h with
          hold | hnew
        · rcases ih.mp hold with ⟨set, hset, hpair⟩
          exact ⟨set, Nat.le_trans hset (Nat.le_succ bound), hpair⟩
        · exact ⟨bound+1, Nat.le_refl (bound+1), hnew⟩
      · intro h
        rcases h with ⟨set, hset, hpair⟩
        apply (mem_adjoin pair
          (standardSetOrdinalRepGraph bound)
          (kpair standardModel (bound+1)
            (ordinalCode (bound+1)))).mpr
        rcases Nat.lt_or_eq_of_le hset with hlt | heq
        · exact Or.inl (ih.mpr
            ⟨set, Nat.le_of_lt_succ hlt, hpair⟩)
        · exact Or.inr (by simpa [heq] using hpair)

theorem standardSetOrdinalRepGraph_certificate (bound : Nat) :
    SetOrdinalRepCertificate
      (standardSetOrdinalRepGraph bound) := by
  constructor
  · intro key value value' hvalue hvalue'
    rcases (mem_standardSetOrdinalRepGraph_iff
      (kpair standardModel key value) bound).mp hvalue with
      ⟨i, hi, hpair⟩
    rcases (mem_standardSetOrdinalRepGraph_iff
      (kpair standardModel key value') bound).mp hvalue' with
      ⟨j, hj, hpair'⟩
    have hcomp := kpair_injective standardModel hpair
    have hcomp' := kpair_injective standardModel hpair'
    have hij : i = j := hcomp.1.symm.trans hcomp'.1
    calc
      value = ordinalCode i := hcomp.2
      _ = ordinalCode j := by rw [hij]
      _ = value' := hcomp'.2.symm
  · intro set code hpair
    rcases (mem_standardSetOrdinalRepGraph_iff
      (kpair standardModel set code) bound).mp hpair with
      ⟨root, hroot, hrootPair⟩
    have hcomp := kpair_injective standardModel hrootPair
    have hset : set = root := hcomp.1
    have hcode : code = ordinalCode root := hcomp.2
    subst set
    subst code
    refine ⟨⟨root, rfl⟩, ?_, ?_⟩
    · intro elem
      constructor
      · intro helem
        have helemLe : elem ≤ bound :=
          Nat.le_trans (Nat.le_of_lt (mem_lt helem)) hroot
        have hchild : Mem
            (kpair standardModel elem (ordinalCode elem))
            (standardSetOrdinalRepGraph bound) :=
          (mem_standardSetOrdinalRepGraph_iff _ bound).mpr
            ⟨elem, helemLe, rfl⟩
        exact ⟨ordinalCode elem, hchild,
          ⟨elem, root, rfl, rfl, helem⟩⟩
      · intro h
        rcases h with ⟨elemCode, hchild, hcoded⟩
        rcases (mem_standardSetOrdinalRepGraph_iff
          (kpair standardModel elem elemCode) bound).mp hchild with
          ⟨child, hchildLe, hchildPair⟩
        have hchildComp := kpair_injective standardModel hchildPair
        rcases hcoded with
          ⟨rawElem, rawSet, helemCode, hsetCode, hmem⟩
        have hrawElem : rawElem = child := by
          apply ordinalCode_injective
          exact helemCode.symm.trans hchildComp.2
        have hrawSet : rawSet = root := by
          apply ordinalCode_injective
          exact hsetCode.symm
        simpa [hchildComp.1, hrawElem, hrawSet] using hmem
    · intro elemCode helemOrd hcoded
      rcases hcoded with
        ⟨rawElem, rawSet, helemCode, hsetCode, hmem⟩
      have hrawSet : rawSet = root := by
        apply ordinalCode_injective
        exact hsetCode.symm
      have hrawElemLe : rawElem ≤ bound := by
        apply Nat.le_trans (Nat.le_of_lt ?_) hroot
        simpa [hrawSet] using mem_lt hmem
      refine ⟨rawElem, ?_⟩
      apply (mem_standardSetOrdinalRepGraph_iff _ bound).mpr
      refine ⟨rawElem, hrawElemLe, ?_⟩
      simp [helemCode]

theorem SetOrdinalRep_exists (set : Nat) :
    SetOrdinalRep set (ordinalCode set) := by
  refine ⟨standardSetOrdinalRepGraph set, ?_,
    standardSetOrdinalRepGraph_certificate set⟩
  apply (mem_standardSetOrdinalRepGraph_iff _ set).mpr
  exact ⟨set, Nat.le_refl set, rfl⟩

theorem SetOrdinalRep_iff (set code : Nat) :
    SetOrdinalRep set code ↔ code = ordinalCode set := by
  constructor
  · exact SetOrdinalRep_code_eq set code
  · intro h
    rw [h]
    exact SetOrdinalRep_exists set


theorem rename_HF_compositeMemAt
    (r : Nat → Nat) (elemCode setCode : Nat) :
    rename r (HF_compositeMemAt elemCode setCode) =
      HF_compositeMemAt (r elemCode) (r setCode) := by
  simp only [HF_compositeMemAt]
  rw [PAInHF.formulaAt_rename]
  apply PAInHF.formulaAt_map_ext
  intro n
  cases n <;> rfl

theorem HF_compositeMemAt_free
    {i elemCode setCode : Nat}
    (h : Free i (HF_compositeMemAt elemCode setCode)) :
    i = elemCode ∨ i = setCode := by
  rcases PAInHF.formulaAt_free (PA.Formula.hfMemAt 0 1) h with
    ⟨n, hn, hi⟩
  rcases PA.Formula.hfMemAt_free hn with hzero | hone
  · subst n
    exact Or.inl hi
  · subst n
    exact Or.inr hi

theorem rename_HF_ordinalLikeAt
    (r : Nat → Nat) (code : Nat) :
    rename r (HF_ordinalLikeAt code) = HF_ordinalLikeAt (r code) := by
  simp [HF_ordinalLikeAt, HF_transitiveAt, HF_memTotalOnAt,
    rename, SetTheory.up]

theorem rename_HF_setOrdinalRepCertificateAt
    (r : Nat → Nat) (relation : Nat) :
    rename r (HF_setOrdinalRepCertificateAt relation) =
      HF_setOrdinalRepCertificateAt (r relation) := by
  simp [HF_setOrdinalRepCertificateAt, fIff, rename, SetTheory.up,
    PAInHF.rename_HF_pairFunctionalAt,
    PAInHF.rename_HF_pairMemAt,
    rename_HF_ordinalLikeAt,
    rename_HF_compositeMemAt]

theorem rename_HF_setOrdinalRepAt
    (r : Nat → Nat) (set code : Nat) :
    rename r (HF_setOrdinalRepAt set code) =
      HF_setOrdinalRepAt (r set) (r code) := by
  simp [HF_setOrdinalRepAt, rename, SetTheory.up,
    PAInHF.rename_HF_pairMemAt,
    rename_HF_setOrdinalRepCertificateAt]

theorem HF_setOrdinalRepCertificateAt_free
    {i relation : Nat}
    (h : Free i (HF_setOrdinalRepCertificateAt relation)) :
    i = relation := by
  simp only [HF_setOrdinalRepCertificateAt, fIff, Free] at h
  repeat first
    | omega
    | have hf := HF_pairFunctionalAt_free h; omega
    | have hp := HF_pairMemAt_free h; omega
    | have hd := HF_ordinalLikeAt_free h; omega
    | have hc := HF_compositeMemAt_free h; omega
    | rcases h with h | h

theorem HF_setOrdinalRepAt_free
    {i set code : Nat}
    (h : Free i (HF_setOrdinalRepAt set code)) :
    i = set ∨ i = code := by
  simp only [HF_setOrdinalRepAt, Free] at h
  rcases h with hroot | hcert
  · have hp := HF_pairMemAt_free hroot
    omega
  · have hc := HF_setOrdinalRepCertificateAt_free hcert
    omega

theorem BProv_HF_setOrdinalRepAt_of_set_eq
    {B : Form → Prop} {G : List Form}
    {oldSet newSet code : Nat}
    (heq : BProv B G (fEq oldSet newSet))
    (hrep : BProv B G (HF_setOrdinalRepAt oldSet code)) :
    BProv B G (HF_setOrdinalRepAt newSet code) := by
  let body : Form := HF_setOrdinalRepAt 0 (code+1)
  have hrepInst : BProv B G (rename (inst oldSet) body) := by
    simpa [body, rename_HF_setOrdinalRepAt, inst] using hrep
  have htransport := BProv_eqElim heq hrepInst
  simpa [body, rename_HF_setOrdinalRepAt, inst] using htransport

theorem BProv_HF_setOrdinalRepAt_of_code_eq
    {B : Form → Prop} {G : List Form}
    {set oldCode newCode : Nat}
    (heq : BProv B G (fEq oldCode newCode))
    (hrep : BProv B G (HF_setOrdinalRepAt set oldCode)) :
    BProv B G (HF_setOrdinalRepAt set newCode) := by
  let body : Form := HF_setOrdinalRepAt (set+1) 0
  have hrepInst : BProv B G (rename (inst oldCode) body) := by
    simpa [body, rename_HF_setOrdinalRepAt, inst] using hrep
  have htransport := BProv_eqElim heq hrepInst
  simpa [body, rename_HF_setOrdinalRepAt, inst] using htransport

theorem hfCompositeAt_mem
    (codedMap : Nat → Nat) (elem set : Nat) :
    hfCompositeAt codedMap (fMem elem set) =
      HF_compositeMemAt (codedMap elem) (codedMap set) := by
  simp only [hfCompositeAt, PA.Formula.hfFormulaAt]
  have hmem : PA.Formula.hfMemAt elem set =
      PA.Formula.rename (repPairNatMap elem set)
        (PA.Formula.hfMemAt 0 1) := by
    rw [PA.Formula.rename_hfMemAt]
    rfl
  rw [hmem]
  rw [PAInHF.formulaAt_PA_rename]
  simp only [HF_compositeMemAt]
  apply PAInHF.formulaAt_map_ext
  intro n
  cases n <;> rfl

theorem BProv_hfCompositeAt_eq_of_eq
    {B : Form → Prop} {G : List Form}
    (codedMap : Nat → Nat) (left right : Nat)
    (heq : BProv B G (fEq (codedMap left) (codedMap right))) :
    BProv B G (hfCompositeAt codedMap (fEq left right)) := by
  simpa [hfCompositeAt, PA.Formula.hfFormulaAt] using
    PAInHF.BProv_formulaAt_eq_var_of_eq codedMap left right heq

theorem BProv_eq_of_hfCompositeAt_eq
    {B : Form → Prop} {G : List Form}
    (codedMap : Nat → Nat) (left right : Nat)
    (heq : BProv B G (hfCompositeAt codedMap (fEq left right))) :
    BProv B G (fEq (codedMap left) (codedMap right)) := by
  apply PAInHF.BProv_eq_of_formulaAt_eq_var codedMap left right
  simpa [hfCompositeAt, PA.Formula.hfFormulaAt] using heq

theorem BProv_HFFin_hfCompositeAt_mem_of_representations
    (P : SetOrdinalRepresentationProofs)
    {G : List Form} {elem set : Nat}
    (rawMap codedMap : Nat → Nat)
    (helem : BProv HFFinAx_s G
      (HF_setOrdinalRepAt (rawMap elem) (codedMap elem)))
    (hset : BProv HFFinAx_s G
      (HF_setOrdinalRepAt (rawMap set) (codedMap set))) :
    BProv HFFinAx_s G
      (fIff
        (rename rawMap (fMem elem set))
        (hfCompositeAt codedMap (fMem elem set))) := by
  simpa [rename, hfCompositeAt_mem] using
    P.mem_exact helem hset

theorem BProv_HFFin_hfCompositeAt_eq_of_representations
    (P : SetOrdinalRepresentationProofs)
    {G : List Form} {left right : Nat}
    (rawMap codedMap : Nat → Nat)
    (hleft : BProv HFFinAx_s G
      (HF_setOrdinalRepAt (rawMap left) (codedMap left)))
    (hright : BProv HFFinAx_s G
      (HF_setOrdinalRepAt (rawMap right) (codedMap right))) :
    BProv HFFinAx_s G
      (fIff
        (rename rawMap (fEq left right))
        (hfCompositeAt codedMap (fEq left right))) := by
  have hforward : BProv HFFinAx_s G
      (fImp
        (fEq (rawMap left) (rawMap right))
        (hfCompositeAt codedMap (fEq left right))) := by
    apply PAInHF.BProv_impI
    let C : List Form := fEq (rawMap left) (rawMap right) :: G
    have hrawEq : BProv HFFinAx_s C
        (fEq (rawMap left) (rawMap right)) :=
      BProv_of_Prov (B := HFFinAx_s)
        (Prov.P_ass C _ (by simp [C]))
    have hleftC : BProv HFFinAx_s C
        (HF_setOrdinalRepAt (rawMap left) (codedMap left)) :=
      PAInHF.BProv_context_cons hleft
    have hrightC : BProv HFFinAx_s C
        (HF_setOrdinalRepAt (rawMap right) (codedMap right)) :=
      PAInHF.BProv_context_cons hright
    have hleftAtRight : BProv HFFinAx_s C
        (HF_setOrdinalRepAt (rawMap right) (codedMap left)) :=
      BProv_HF_setOrdinalRepAt_of_set_eq hrawEq hleftC
    have hcodeEq : BProv HFFinAx_s C
        (fEq (codedMap left) (codedMap right)) :=
      P.code_functional hleftAtRight hrightC
    exact BProv_hfCompositeAt_eq_of_eq
      codedMap left right hcodeEq
  have hreverse : BProv HFFinAx_s G
      (fImp
        (hfCompositeAt codedMap (fEq left right))
        (fEq (rawMap left) (rawMap right))) := by
    apply PAInHF.BProv_impI
    let C : List Form := hfCompositeAt codedMap (fEq left right) :: G
    have hcomposite : BProv HFFinAx_s C
        (hfCompositeAt codedMap (fEq left right)) :=
      BProv_of_Prov (B := HFFinAx_s)
        (Prov.P_ass C _ (by simp [C]))
    have hcodeEq : BProv HFFinAx_s C
        (fEq (codedMap left) (codedMap right)) :=
      BProv_eq_of_hfCompositeAt_eq
        codedMap left right hcomposite
    have hleftC : BProv HFFinAx_s C
        (HF_setOrdinalRepAt (rawMap left) (codedMap left)) :=
      PAInHF.BProv_context_cons hleft
    have hrightC : BProv HFFinAx_s C
        (HF_setOrdinalRepAt (rawMap right) (codedMap right)) :=
      PAInHF.BProv_context_cons hright
    have hleftAtRightCode : BProv HFFinAx_s C
        (HF_setOrdinalRepAt (rawMap left) (codedMap right)) :=
      BProv_HF_setOrdinalRepAt_of_code_eq hcodeEq hleftC
    exact P.set_injective hleftAtRightCode hrightC
  simpa [fIff, rename] using PAInHF.BProv_andI hforward hreverse

/-! ### Set-formula equivalence calculus -/

theorem BProv_fIff_refl
    {B : Form → Prop} {G : List Form} (a : Form) :
    BProv B G (fIff a a) := by
  have haa : BProv B G (fImp a a) :=
    PAInHF.BProv_impI
      (BProv_of_Prov (B := B) (Prov.P_ass (a :: G) a (by simp)))
  simpa [fIff] using PAInHF.BProv_andI haa haa

theorem BProv_fIff_imp_congr
    {B : Form → Prop} {G : List Form}
    {a a' b b' : Form}
    (ha : BProv B G (fIff a a'))
    (hb : BProv B G (fIff b b')) :
    BProv B G (fIff (fImp a b) (fImp a' b')) := by
  have haa' : BProv B G (fImp a a') := by
    simpa [fIff] using PAInHF.BProv_andE1 ha
  have ha'a : BProv B G (fImp a' a) := by
    simpa [fIff] using PAInHF.BProv_andE2 ha
  have hbb' : BProv B G (fImp b b') := by
    simpa [fIff] using PAInHF.BProv_andE1 hb
  have hb'b : BProv B G (fImp b' b) := by
    simpa [fIff] using PAInHF.BProv_andE2 hb
  have hforward : BProv B G (fImp (fImp a b) (fImp a' b')) := by
    apply PAInHF.BProv_impI
    apply PAInHF.BProv_impI
    let C : List Form := a' :: fImp a b :: G
    have ha'C : BProv B C a' :=
      BProv_of_Prov (B := B) (Prov.P_ass C a' (by simp [C]))
    have haC : BProv B C a :=
      BProv_mp B C a' a
        (PAInHF.BProv_context_cons
          (PAInHF.BProv_context_cons ha'a)) ha'C
    have habC : BProv B C (fImp a b) :=
      BProv_of_Prov (B := B) (Prov.P_ass C _ (by simp [C]))
    have hbC : BProv B C b := BProv_mp B C a b habC haC
    exact BProv_mp B C b b'
      (PAInHF.BProv_context_cons
        (PAInHF.BProv_context_cons hbb')) hbC
  have hreverse : BProv B G (fImp (fImp a' b') (fImp a b)) := by
    apply PAInHF.BProv_impI
    apply PAInHF.BProv_impI
    let C : List Form := a :: fImp a' b' :: G
    have haC : BProv B C a :=
      BProv_of_Prov (B := B) (Prov.P_ass C a (by simp [C]))
    have ha'C : BProv B C a' :=
      BProv_mp B C a a'
        (PAInHF.BProv_context_cons
          (PAInHF.BProv_context_cons haa')) haC
    have ha'b'C : BProv B C (fImp a' b') :=
      BProv_of_Prov (B := B) (Prov.P_ass C _ (by simp [C]))
    have hb'C : BProv B C b' := BProv_mp B C a' b' ha'b'C ha'C
    exact BProv_mp B C b' b
      (PAInHF.BProv_context_cons
        (PAInHF.BProv_context_cons hb'b)) hb'C
  simpa [fIff] using PAInHF.BProv_andI hforward hreverse

theorem BProv_fIff_and_congr
    {B : Form → Prop} {G : List Form}
    {a a' b b' : Form}
    (ha : BProv B G (fIff a a'))
    (hb : BProv B G (fIff b b')) :
    BProv B G (fIff (fAnd a b) (fAnd a' b')) := by
  have haa' : BProv B G (fImp a a') := by
    simpa [fIff] using PAInHF.BProv_andE1 ha
  have ha'a : BProv B G (fImp a' a) := by
    simpa [fIff] using PAInHF.BProv_andE2 ha
  have hbb' : BProv B G (fImp b b') := by
    simpa [fIff] using PAInHF.BProv_andE1 hb
  have hb'b : BProv B G (fImp b' b) := by
    simpa [fIff] using PAInHF.BProv_andE2 hb
  have hforward : BProv B G (fImp (fAnd a b) (fAnd a' b')) := by
    apply PAInHF.BProv_impI
    let C : List Form := fAnd a b :: G
    have hp : BProv B C (fAnd a b) :=
      BProv_of_Prov (B := B) (Prov.P_ass C _ (by simp [C]))
    have haC : BProv B C a := PAInHF.BProv_andE1 hp
    have hbC : BProv B C b := PAInHF.BProv_andE2 hp
    exact PAInHF.BProv_andI
      (BProv_mp B C a a' (PAInHF.BProv_context_cons haa') haC)
      (BProv_mp B C b b' (PAInHF.BProv_context_cons hbb') hbC)
  have hreverse : BProv B G (fImp (fAnd a' b') (fAnd a b)) := by
    apply PAInHF.BProv_impI
    let C : List Form := fAnd a' b' :: G
    have hp : BProv B C (fAnd a' b') :=
      BProv_of_Prov (B := B) (Prov.P_ass C _ (by simp [C]))
    have ha'C : BProv B C a' := PAInHF.BProv_andE1 hp
    have hb'C : BProv B C b' := PAInHF.BProv_andE2 hp
    exact PAInHF.BProv_andI
      (BProv_mp B C a' a (PAInHF.BProv_context_cons ha'a) ha'C)
      (BProv_mp B C b' b (PAInHF.BProv_context_cons hb'b) hb'C)
  simpa [fIff] using PAInHF.BProv_andI hforward hreverse

theorem BProv_fIff_or_congr
    {B : Form → Prop} {G : List Form}
    {a a' b b' : Form}
    (ha : BProv B G (fIff a a'))
    (hb : BProv B G (fIff b b')) :
    BProv B G (fIff (fOr a b) (fOr a' b')) := by
  have haa' : BProv B G (fImp a a') := by
    simpa [fIff] using PAInHF.BProv_andE1 ha
  have ha'a : BProv B G (fImp a' a) := by
    simpa [fIff] using PAInHF.BProv_andE2 ha
  have hbb' : BProv B G (fImp b b') := by
    simpa [fIff] using PAInHF.BProv_andE1 hb
  have hb'b : BProv B G (fImp b' b) := by
    simpa [fIff] using PAInHF.BProv_andE2 hb
  have hforward : BProv B G (fImp (fOr a b) (fOr a' b')) := by
    apply PAInHF.BProv_impI
    let C : List Form := fOr a b :: G
    have hor : BProv B C (fOr a b) :=
      BProv_of_Prov (B := B) (Prov.P_ass C _ (by simp [C]))
    have hleft : BProv B (a :: C) (fOr a' b') := by
      have haC : BProv B (a :: C) a :=
        BProv_of_Prov (B := B) (Prov.P_ass (a :: C) a (by simp))
      exact PAInHF.BProv_orI1
        (BProv_mp B (a :: C) a a'
          (PAInHF.BProv_context_cons
            (PAInHF.BProv_context_cons haa')) haC)
    have hright : BProv B (b :: C) (fOr a' b') := by
      have hbC : BProv B (b :: C) b :=
        BProv_of_Prov (B := B) (Prov.P_ass (b :: C) b (by simp))
      exact PAInHF.BProv_orI2
        (BProv_mp B (b :: C) b b'
          (PAInHF.BProv_context_cons
            (PAInHF.BProv_context_cons hbb')) hbC)
    exact PAInHF.BProv_orE hor hleft hright
  have hreverse : BProv B G (fImp (fOr a' b') (fOr a b)) := by
    apply PAInHF.BProv_impI
    let C : List Form := fOr a' b' :: G
    have hor : BProv B C (fOr a' b') :=
      BProv_of_Prov (B := B) (Prov.P_ass C _ (by simp [C]))
    have hleft : BProv B (a' :: C) (fOr a b) := by
      have ha'C : BProv B (a' :: C) a' :=
        BProv_of_Prov (B := B) (Prov.P_ass (a' :: C) a' (by simp))
      exact PAInHF.BProv_orI1
        (BProv_mp B (a' :: C) a' a
          (PAInHF.BProv_context_cons
            (PAInHF.BProv_context_cons ha'a)) ha'C)
    have hright : BProv B (b' :: C) (fOr a b) := by
      have hb'C : BProv B (b' :: C) b' :=
        BProv_of_Prov (B := B) (Prov.P_ass (b' :: C) b' (by simp))
      exact PAInHF.BProv_orI2
        (BProv_mp B (b' :: C) b' b
          (PAInHF.BProv_context_cons
            (PAInHF.BProv_context_cons hb'b)) hb'C)
    exact PAInHF.BProv_orE hor hleft hright
  simpa [fIff] using PAInHF.BProv_andI hforward hreverse

def HFQuantifierFree : Form → Prop
  | fMem _ _ => True
  | fEq _ _ => True
  | fBot => True
  | fImp a b => HFQuantifierFree a ∧ HFQuantifierFree b
  | fAnd a b => HFQuantifierFree a ∧ HFQuantifierFree b
  | fOr a b => HFQuantifierFree a ∧ HFQuantifierFree b
  | fAll _ => False
  | fEx _ => False

theorem BProv_HFFin_hfCompositeAt_iff_of_quantifierFree
    (P : SetOrdinalRepresentationProofs) :
    ∀ (G : List Form) (phi : Form) (rawMap codedMap : Nat → Nat),
      HFQuantifierFree phi →
      (∀ n, Free n phi →
        BProv HFFinAx_s G
          (HF_setOrdinalRepAt (rawMap n) (codedMap n))) →
      BProv HFFinAx_s G
        (fIff (rename rawMap phi) (hfCompositeAt codedMap phi)) := by
  intro G phi
  induction phi with
  | fMem elem set =>
      intro rawMap codedMap hq hrep
      exact BProv_HFFin_hfCompositeAt_mem_of_representations
        P rawMap codedMap
        (hrep elem (Or.inl rfl))
        (hrep set (Or.inr rfl))
  | fEq left right =>
      intro rawMap codedMap hq hrep
      exact BProv_HFFin_hfCompositeAt_eq_of_representations
        P rawMap codedMap
        (hrep left (Or.inl rfl))
        (hrep right (Or.inr rfl))
  | fBot =>
      intro rawMap codedMap hq hrep
      simpa [hfCompositeAt, PA.Formula.hfFormulaAt,
        PAInHF.formulaAt, rename] using
        (BProv_fIff_refl (B := HFFinAx_s) (G := G) fBot)
  | fImp a b iha ihb =>
      intro rawMap codedMap hq hrep
      have ha := iha rawMap codedMap hq.1
        (fun n hn => hrep n (Or.inl hn))
      have hb := ihb rawMap codedMap hq.2
        (fun n hn => hrep n (Or.inr hn))
      simpa [hfCompositeAt, PA.Formula.hfFormulaAt,
        PAInHF.formulaAt, rename] using
        BProv_fIff_imp_congr ha hb
  | fAnd a b iha ihb =>
      intro rawMap codedMap hq hrep
      have ha := iha rawMap codedMap hq.1
        (fun n hn => hrep n (Or.inl hn))
      have hb := ihb rawMap codedMap hq.2
        (fun n hn => hrep n (Or.inr hn))
      simpa [hfCompositeAt, PA.Formula.hfFormulaAt,
        PAInHF.formulaAt, rename] using
        BProv_fIff_and_congr ha hb
  | fOr a b iha ihb =>
      intro rawMap codedMap hq hrep
      have ha := iha rawMap codedMap hq.1
        (fun n hn => hrep n (Or.inl hn))
      have hb := ihb rawMap codedMap hq.2
        (fun n hn => hrep n (Or.inr hn))
      simpa [hfCompositeAt, PA.Formula.hfFormulaAt,
        PAInHF.formulaAt, rename] using
        BProv_fIff_or_congr ha hb
  | fAll a ih =>
      intro rawMap codedMap hq hrep
      exact False.elim hq
  | fEx a ih =>
      intro rawMap codedMap hq hrep
      exact False.elim hq


theorem hfCompositeAt_all
    (codedMap : Nat → Nat) (a : Form) :
    hfCompositeAt codedMap (fAll a) =
      fAll (fImp PAInHF.domainForm
        (hfCompositeAt (PAInHF.upVarMap codedMap) a)) := by
  have hinner :
      PA.Formula.hfFormulaAt
          (PA.Formula.hfUpVarMap (fun n => n)) a =
        PA.Formula.hfFormulaAt (fun n => n) a := by
    apply PA.Formula.hfFormulaAt_ext
    intro n
    cases n <;> rfl
  simp only [hfCompositeAt, PA.Formula.hfFormulaAt,
    PAInHF.formulaAt]
  rw [hinner]

theorem hfCompositeAt_ex
    (codedMap : Nat → Nat) (a : Form) :
    hfCompositeAt codedMap (fEx a) =
      fEx (fAnd PAInHF.domainForm
        (hfCompositeAt (PAInHF.upVarMap codedMap) a)) := by
  have hinner :
      PA.Formula.hfFormulaAt
          (PA.Formula.hfUpVarMap (fun n => n)) a =
        PA.Formula.hfFormulaAt (fun n => n) a := by
    apply PA.Formula.hfFormulaAt_ext
    intro n
    cases n <;> rfl
  simp only [hfCompositeAt, PA.Formula.hfFormulaAt,
    PAInHF.formulaAt]
  rw [hinner]

/-! ### Paired slots under range and totality witnesses -/

/-- After opening the range witness for a coded value, the fresh raw set is
slot `0`, the coded value is slot `1`, and ambient raw slots move by two. -/
def rangeRawMap (rawMap : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => rawMap n + 2

/-- Coded companion to `rangeRawMap`. -/
def rangeCodedMap (codedMap : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n+1 => codedMap n + 2

/-- After totality opens a code for a fresh raw set, the code is slot `0`,
the raw set is slot `1`, and ambient raw slots move by two. -/
def totalRawMap (rawMap : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n+1 => rawMap n + 2

/-- Coded companion to `totalRawMap`. -/
def totalCodedMap (codedMap : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => codedMap n + 2

theorem rename_hfCompositeAt
    (r codedMap : Nat → Nat) (phi : Form) :
    rename r (hfCompositeAt codedMap phi) =
      hfCompositeAt (fun n => r (codedMap n)) phi := by
  simpa [hfCompositeAt] using
    (PAInHF.formulaAt_rename
      (PA.Formula.hfFormulaAt (fun n : Nat => n) phi)
      (ρ := codedMap) (r := r))

theorem rename_succ_hfCompositeAt_up
    (codedMap : Nat → Nat) (phi : Form) :
    rename Nat.succ
        (hfCompositeAt (PAInHF.upVarMap codedMap) phi) =
      hfCompositeAt (rangeCodedMap codedMap) phi := by
  rw [rename_hfCompositeAt]
  apply congrArg (fun m => hfCompositeAt m phi)
  funext n
  cases n <;> rfl

theorem rename_succ_rawBody
    (rawMap : Nat → Nat) (phi : Form) :
    rename Nat.succ
        (rename (PAInHF.upVarMap rawMap) phi) =
      rename (totalRawMap rawMap) phi := by
  rw [rename_comp]
  apply rename_ext
  intro n
  cases n <;> rfl

theorem inst_range_rawBody
    (rawMap : Nat → Nat) (phi : Form) :
    rename (inst 0)
        (rename (SetTheory.up Nat.succ)
          (rename (SetTheory.up Nat.succ)
            (rename (PAInHF.upVarMap rawMap) phi))) =
      rename (rangeRawMap rawMap) phi := by
  repeat rw [rename_comp]
  apply rename_ext
  intro n
  cases n <;> rfl

theorem inst_total_codedBody
    (codedMap : Nat → Nat) (phi : Form) :
    rename (inst 0)
        (rename (SetTheory.up Nat.succ)
          (rename (SetTheory.up Nat.succ)
            (hfCompositeAt (PAInHF.upVarMap codedMap) phi))) =
      hfCompositeAt (totalCodedMap codedMap) phi := by
  simp only [rename_hfCompositeAt]
  apply congrArg (fun m => hfCompositeAt m phi)
  funext n
  cases n <;> rfl

/-! ### Proof-calculus support for paired binders -/

theorem BProv_rename_of_sentences
    {B : Form → Prop} (hB : Sentences B)
    {G : List Form} {phi : Form}
    (h : BProv B G phi) (r : Nat → Nat) :
    BProv B (G.map (rename r)) (rename r phi) := by
  rcases h with ⟨L, hL, hp⟩
  have hLmap : L.map (rename r) = L := by
    calc
      L.map (rename r) = L.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact PAInHF.rename_eq_of_sentence (hB x (hL x hx)) r
      _ = L := by simp
  refine ⟨L, hL, ?_⟩
  have hpRen : Prov ((L ++ G).map (rename r)) (rename r phi) :=
    Prov_rename hp r
  apply Prov_weaken hpRen
  intro x hx
  simp only [List.map_append, List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (by simpa [hLmap] using hx)
  · exact Or.inr hx

theorem BProv_HFFin_rep_exists_of_ordinalLike
    (P : SetOrdinalRepresentationProofs)
    {G : List Form} {code : Nat}
    (hdom : BProv HFFinAx_s G (HF_ordinalLikeAt code)) :
    BProv HFFinAx_s G
      (fEx (HF_setOrdinalRepAt 0 (code+1))) := by
  have hforward : BProv HFFinAx_s G
      (fImp (HF_ordinalLikeAt code)
        (fEx (HF_setOrdinalRepAt 0 (code+1)))) := by
    simpa [fIff] using PAInHF.BProv_andE1 (P.range G code)
  exact BProv_mp HFFinAx_s G _ _ hforward hdom

theorem BProv_HFFin_ordinalLike_of_rep
    (P : SetOrdinalRepresentationProofs)
    {G : List Form} {set code : Nat}
    (hrep : BProv HFFinAx_s G (HF_setOrdinalRepAt set code)) :
    BProv HFFinAx_s G (HF_ordinalLikeAt code) := by
  have hex : BProv HFFinAx_s G
      (fEx (HF_setOrdinalRepAt 0 (code+1))) := by
    apply PAInHF.BProv_exI (k := set)
    simpa [rename_HF_setOrdinalRepAt, inst] using hrep
  have hreverse : BProv HFFinAx_s G
      (fImp (fEx (HF_setOrdinalRepAt 0 (code+1)))
        (HF_ordinalLikeAt code)) := by
    simpa [fIff] using PAInHF.BProv_andE2 (P.range G code)
  exact BProv_mp HFFinAx_s G _ _ hreverse hex

/-! ### Paired-variable universal steps -/

theorem BProv_HFFin_hfCompositeAt_all_forward
    (P : SetOrdinalRepresentationProofs)
    (phi : Form)
    (ih : ∀ (G : List Form) (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv HFFinAx_s G
          (HF_setOrdinalRepAt (rawMap n) (codedMap n))) →
      BProv HFFinAx_s G
        (fIff (rename rawMap phi) (hfCompositeAt codedMap phi)))
    (G : List Form) (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (fAll phi) →
      BProv HFFinAx_s G
        (HF_setOrdinalRepAt (rawMap n) (codedMap n))) :
    BProv HFFinAx_s G
      (fImp (rename rawMap (fAll phi))
        (hfCompositeAt codedMap (fAll phi))) := by
  let rawBody : Form :=
    rename (PAInHF.upVarMap rawMap) phi
  let codedBody : Form :=
    hfCompositeAt (PAInHF.upVarMap codedMap) phi
  let rawAll : Form := fAll rawBody
  let codedAll : Form :=
    fAll (fImp PAInHF.domainForm codedBody)
  let C₀ : List Form := rawAll :: G
  let C₁ : List Form := C₀.map (rename Nat.succ)
  let C₂ : List Form := PAInHF.domainForm :: C₁
  have hcodedBody : BProv HFFinAx_s C₂ codedBody := by
    have hdomain : BProv HFFinAx_s C₂ PAInHF.domainForm :=
      BProv_of_Prov (B := HFFinAx_s)
        (Prov.P_ass C₂ _ (by simp [C₂]))
    have hrange :=
      BProv_HFFin_rep_exists_of_ordinalLike P hdomain
    let repBody : Form := HF_setOrdinalRepAt 0 1
    have hrange' : BProv HFFinAx_s C₂ (fEx repBody) := by
      simpa [repBody] using hrange
    let C₃ : List Form := repBody :: C₂.map (rename Nat.succ)
    have hopened : BProv HFFinAx_s C₃ (rename Nat.succ codedBody) := by
      have hrep : BProv HFFinAx_s C₃
          (HF_setOrdinalRepAt 0 1) := by
        have hass : BProv HFFinAx_s C₃ repBody :=
          BProv_of_Prov (B := HFFinAx_s)
            (Prov.P_ass C₃ _ (by simp [C₃]))
        simpa [repBody] using hass
      have hpaired : ∀ n, Free n phi →
          BProv HFFinAx_s C₃
            (HF_setOrdinalRepAt
              (rangeRawMap rawMap n)
              (rangeCodedMap codedMap n)) := by
        intro n hn
        cases n with
        | zero =>
            simpa [rangeRawMap,
              rangeCodedMap] using hrep
        | succ n =>
            have h₀ := hcode n hn
            have h₁ := BProv_rename_of_sentences
              Sentences_HFFin h₀ Nat.succ
            have h₂ := BProv_rename_of_sentences
              Sentences_HFFin h₁ Nat.succ
            have hrawCtx := PAInHF.BProv_context_cons
              (a := rename Nat.succ (rename Nat.succ rawAll)) h₂
            have hdomainCtx := PAInHF.BProv_context_cons
              (a := rename Nat.succ PAInHF.domainForm) hrawCtx
            have hctx := PAInHF.BProv_context_cons
              (a := repBody) hdomainCtx
            simpa [C₃, C₂, C₁, C₀,
              rangeRawMap, rangeCodedMap,
              rename_HF_setOrdinalRepAt, List.map_map,
              Function.comp_def] using hctx
      have hih := ih C₃
        (rangeRawMap rawMap)
        (rangeCodedMap codedMap) hpaired
      have hihForward : BProv HFFinAx_s C₃
          (fImp
            (rename (rangeRawMap rawMap) phi)
            (hfCompositeAt (rangeCodedMap codedMap) phi)) := by
        simpa [fIff] using PAInHF.BProv_andE1 hih
      have hall₀ : BProv HFFinAx_s C₀ rawAll :=
        BProv_of_Prov (B := HFFinAx_s)
          (Prov.P_ass C₀ _ (by simp [C₀]))
      have hall₁ := BProv_rename_of_sentences
        Sentences_HFFin hall₀ Nat.succ
      have hall₂ := BProv_rename_of_sentences
        Sentences_HFFin hall₁ Nat.succ
      have hallDomainCtx := PAInHF.BProv_context_cons
        (a := rename Nat.succ PAInHF.domainForm) hall₂
      have hallCtx := PAInHF.BProv_context_cons
        (a := repBody) hallDomainCtx
      have hallCtx' : BProv HFFinAx_s C₃
          (fAll (rename (SetTheory.up Nat.succ)
            (rename (SetTheory.up Nat.succ) rawBody))) := by
        simpa [C₃, C₂, C₁, C₀, rawAll, rename] using hallCtx
      have hrawInst := PAInHF.BProv_allE
        (B := HFFinAx_s) (G := C₃) (k := 0) hallCtx'
      have hraw : BProv HFFinAx_s C₃
          (rename (rangeRawMap rawMap) phi) := by
        simpa [rawBody, inst_range_rawBody] using hrawInst
      have hcomp : BProv HFFinAx_s C₃
          (hfCompositeAt (rangeCodedMap codedMap) phi) :=
        BProv_mp HFFinAx_s C₃ _ _ hihForward hraw
      simpa [codedBody, rename_succ_hfCompositeAt_up]
        using hcomp
    exact PAInHF.BProv_exE_of_sentences
      (B := HFFinAx_s) Sentences_HFFin
      (a := repBody) (c := codedBody) hrange' (by
        simpa [C₃] using hopened)
  have himp : BProv HFFinAx_s C₁
      (fImp PAInHF.domainForm codedBody) := by
    simpa [C₂] using PAInHF.BProv_impI hcodedBody
  have hall : BProv HFFinAx_s C₀ codedAll := by
    simpa [codedAll, C₁] using
      (PAInHF.BProv_allI_of_sentences
        (B := HFFinAx_s) Sentences_HFFin (G := C₀) himp)
  have hmain : BProv HFFinAx_s G (fImp rawAll codedAll) := by
    simpa [C₀] using PAInHF.BProv_impI hall
  have hup : PAInHF.upVarMap rawMap = SetTheory.up rawMap := by
    funext n
    cases n <;> rfl
  simpa [rawAll, rawBody, codedAll, codedBody, hup,
    rename, hfCompositeAt_all] using hmain

theorem BProv_HFFin_hfCompositeAt_all_reverse
    (P : SetOrdinalRepresentationProofs)
    (phi : Form)
    (ih : ∀ (G : List Form) (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv HFFinAx_s G
          (HF_setOrdinalRepAt (rawMap n) (codedMap n))) →
      BProv HFFinAx_s G
        (fIff (rename rawMap phi) (hfCompositeAt codedMap phi)))
    (G : List Form) (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (fAll phi) →
      BProv HFFinAx_s G
        (HF_setOrdinalRepAt (rawMap n) (codedMap n))) :
    BProv HFFinAx_s G
      (fImp (hfCompositeAt codedMap (fAll phi))
        (rename rawMap (fAll phi))) := by
  let rawBody : Form :=
    rename (PAInHF.upVarMap rawMap) phi
  let codedBody : Form :=
    hfCompositeAt (PAInHF.upVarMap codedMap) phi
  let rawAll : Form := fAll rawBody
  let codedAll : Form :=
    fAll (fImp PAInHF.domainForm codedBody)
  let C₀ : List Form := codedAll :: G
  let C₁ : List Form := C₀.map (rename Nat.succ)
  have hrawBody : BProv HFFinAx_s C₁ rawBody := by
    have htotal := P.total C₁ 0
    let repBody : Form := HF_setOrdinalRepAt 1 0
    have htotal' : BProv HFFinAx_s C₁ (fEx repBody) := by
      simpa [repBody] using htotal
    let C₂ : List Form := repBody :: C₁.map (rename Nat.succ)
    have hopened : BProv HFFinAx_s C₂ (rename Nat.succ rawBody) := by
      have hrep : BProv HFFinAx_s C₂
          (HF_setOrdinalRepAt 1 0) := by
        have hass : BProv HFFinAx_s C₂ repBody :=
          BProv_of_Prov (B := HFFinAx_s)
            (Prov.P_ass C₂ _ (by simp [C₂]))
        simpa [repBody] using hass
      have hpaired : ∀ n, Free n phi →
          BProv HFFinAx_s C₂
            (HF_setOrdinalRepAt
              (totalRawMap rawMap n)
              (totalCodedMap codedMap n)) := by
        intro n hn
        cases n with
        | zero =>
            simpa [totalRawMap,
              totalCodedMap] using hrep
        | succ n =>
            have h₀ := hcode n hn
            have h₁ := BProv_rename_of_sentences
              Sentences_HFFin h₀ Nat.succ
            have h₂ := BProv_rename_of_sentences
              Sentences_HFFin h₁ Nat.succ
            have hcodedCtx := PAInHF.BProv_context_cons
              (a := rename Nat.succ (rename Nat.succ codedAll)) h₂
            have hctx := PAInHF.BProv_context_cons
              (a := repBody) hcodedCtx
            simpa [C₂, C₁, C₀,
              totalRawMap, totalCodedMap,
              rename_HF_setOrdinalRepAt, List.map_map,
              Function.comp_def] using hctx
      have hih := ih C₂
        (totalRawMap rawMap)
        (totalCodedMap codedMap) hpaired
      have hihReverse : BProv HFFinAx_s C₂
          (fImp
            (hfCompositeAt (totalCodedMap codedMap) phi)
            (rename (totalRawMap rawMap) phi)) := by
        simpa [fIff] using PAInHF.BProv_andE2 hih
      have hall₀ : BProv HFFinAx_s C₀ codedAll :=
        BProv_of_Prov (B := HFFinAx_s)
          (Prov.P_ass C₀ _ (by simp [C₀]))
      have hall₁ := BProv_rename_of_sentences
        Sentences_HFFin hall₀ Nat.succ
      have hall₂ := BProv_rename_of_sentences
        Sentences_HFFin hall₁ Nat.succ
      have hallCtx := PAInHF.BProv_context_cons
        (a := repBody) hall₂
      have hallCtx' : BProv HFFinAx_s C₂
          (fAll (rename (SetTheory.up Nat.succ)
            (rename (SetTheory.up Nat.succ)
              (fImp PAInHF.domainForm codedBody)))) := by
        simpa [C₂, C₁, C₀, codedAll, rename] using hallCtx
      have hbodyInst := PAInHF.BProv_allE
        (B := HFFinAx_s) (G := C₂) (k := 0) hallCtx'
      have hcodedImp : BProv HFFinAx_s C₂
          (fImp PAInHF.domainForm
            (hfCompositeAt (totalCodedMap codedMap) phi)) := by
        simpa [rename, PAInHF.rename_domainForm_up,
          PAInHF.rename_domainForm_inst_zero, codedBody,
          inst_total_codedBody] using hbodyInst
      have hdomain : BProv HFFinAx_s C₂ PAInHF.domainForm := by
        simpa [PAInHF.domainForm] using
          BProv_HFFin_ordinalLike_of_rep P hrep
      have hcomp : BProv HFFinAx_s C₂
          (hfCompositeAt (totalCodedMap codedMap) phi) :=
        BProv_mp HFFinAx_s C₂ _ _ hcodedImp hdomain
      have hraw : BProv HFFinAx_s C₂
          (rename (totalRawMap rawMap) phi) :=
        BProv_mp HFFinAx_s C₂ _ _ hihReverse hcomp
      simpa [rawBody, rename_succ_rawBody] using hraw
    exact PAInHF.BProv_exE_of_sentences
      (B := HFFinAx_s) Sentences_HFFin
      (a := repBody) (c := rawBody) htotal' (by
        simpa [C₂] using hopened)
  have hall : BProv HFFinAx_s C₀ rawAll := by
    simpa [rawAll, C₁] using
      (PAInHF.BProv_allI_of_sentences
        (B := HFFinAx_s) Sentences_HFFin (G := C₀) hrawBody)
  have hmain : BProv HFFinAx_s G (fImp codedAll rawAll) := by
    simpa [C₀] using PAInHF.BProv_impI hall
  have hup : PAInHF.upVarMap rawMap = SetTheory.up rawMap := by
    funext n
    cases n <;> rfl
  simpa [rawAll, rawBody, codedAll, codedBody, hup,
    rename, hfCompositeAt_all] using hmain

theorem BProv_HFFin_hfCompositeAt_all
    (P : SetOrdinalRepresentationProofs)
    (phi : Form)
    (ih : ∀ (G : List Form) (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv HFFinAx_s G
          (HF_setOrdinalRepAt (rawMap n) (codedMap n))) →
      BProv HFFinAx_s G
        (fIff (rename rawMap phi) (hfCompositeAt codedMap phi)))
    (G : List Form) (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (fAll phi) →
      BProv HFFinAx_s G
        (HF_setOrdinalRepAt (rawMap n) (codedMap n))) :
    BProv HFFinAx_s G
      (fIff (rename rawMap (fAll phi))
        (hfCompositeAt codedMap (fAll phi))) := by
  have hforward :=
    BProv_HFFin_hfCompositeAt_all_forward
      P phi ih G rawMap codedMap hcode
  have hreverse :=
    BProv_HFFin_hfCompositeAt_all_reverse
      P phi ih G rawMap codedMap hcode
  simpa [fIff] using PAInHF.BProv_andI hforward hreverse

/-! ### Paired-variable existential steps -/

theorem BProv_HFFin_hfCompositeAt_ex_forward
    (P : SetOrdinalRepresentationProofs)
    (phi : Form)
    (ih : ∀ (G : List Form) (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv HFFinAx_s G
          (HF_setOrdinalRepAt (rawMap n) (codedMap n))) →
      BProv HFFinAx_s G
        (fIff (rename rawMap phi) (hfCompositeAt codedMap phi)))
    (G : List Form) (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (fEx phi) →
      BProv HFFinAx_s G
        (HF_setOrdinalRepAt (rawMap n) (codedMap n))) :
    BProv HFFinAx_s G
      (fImp (rename rawMap (fEx phi))
        (hfCompositeAt codedMap (fEx phi))) := by
  let rawBody : Form :=
    rename (PAInHF.upVarMap rawMap) phi
  let codedBody : Form :=
    hfCompositeAt (PAInHF.upVarMap codedMap) phi
  let rawEx : Form := fEx rawBody
  let codedEx : Form :=
    fEx (fAnd PAInHF.domainForm codedBody)
  let C₀ : List Form := rawEx :: G
  have hcodedEx : BProv HFFinAx_s C₀ codedEx := by
    have hrawEx : BProv HFFinAx_s C₀ rawEx :=
      BProv_of_Prov (B := HFFinAx_s)
        (Prov.P_ass C₀ _ (by simp [C₀]))
    let C₁ : List Form := rawBody :: C₀.map (rename Nat.succ)
    have hrawOpened : BProv HFFinAx_s C₁
        (rename Nat.succ codedEx) := by
      have htotal := P.total C₁ 0
      let repBody : Form := HF_setOrdinalRepAt 1 0
      have htotal' : BProv HFFinAx_s C₁ (fEx repBody) := by
        simpa [repBody] using htotal
      let C₂ : List Form := repBody :: C₁.map (rename Nat.succ)
      have hcodeOpened : BProv HFFinAx_s C₂
          (rename Nat.succ (rename Nat.succ codedEx)) := by
        have hrep : BProv HFFinAx_s C₂
            (HF_setOrdinalRepAt 1 0) := by
          have hass : BProv HFFinAx_s C₂ repBody :=
            BProv_of_Prov (B := HFFinAx_s)
              (Prov.P_ass C₂ _ (by simp [C₂]))
          simpa [repBody] using hass
        have hpaired : ∀ n, Free n phi →
            BProv HFFinAx_s C₂
              (HF_setOrdinalRepAt
                (totalRawMap rawMap n)
                (totalCodedMap codedMap n)) := by
          intro n hn
          cases n with
          | zero =>
              simpa [totalRawMap,
                totalCodedMap] using hrep
          | succ n =>
              have h₀ := hcode n hn
              have h₁ := BProv_rename_of_sentences
                Sentences_HFFin h₀ Nat.succ
              have h₂ := BProv_rename_of_sentences
                Sentences_HFFin h₁ Nat.succ
              have hexCtx := PAInHF.BProv_context_cons
                (a := rename Nat.succ (rename Nat.succ rawEx)) h₂
              have hrawCtx := PAInHF.BProv_context_cons
                (a := rename Nat.succ rawBody) hexCtx
              have hctx := PAInHF.BProv_context_cons
                (a := repBody) hrawCtx
              simpa [C₂, C₁, C₀,
                totalRawMap, totalCodedMap,
                rename_HF_setOrdinalRepAt, List.map_map,
                Function.comp_def] using hctx
        have hih := ih C₂
          (totalRawMap rawMap)
          (totalCodedMap codedMap) hpaired
        have hihForward : BProv HFFinAx_s C₂
            (fImp
              (rename (totalRawMap rawMap) phi)
              (hfCompositeAt (totalCodedMap codedMap) phi)) := by
          simpa [fIff] using PAInHF.BProv_andE1 hih
        have hrawShifted : BProv HFFinAx_s C₂
            (rename Nat.succ rawBody) :=
          BProv_of_Prov (B := HFFinAx_s)
            (Prov.P_ass C₂ _ (by simp [C₂, C₁]))
        have hraw : BProv HFFinAx_s C₂
            (rename (totalRawMap rawMap) phi) := by
          simpa [rawBody, rename_succ_rawBody]
            using hrawShifted
        have hcomp : BProv HFFinAx_s C₂
            (hfCompositeAt (totalCodedMap codedMap) phi) :=
          BProv_mp HFFinAx_s C₂ _ _ hihForward hraw
        have hdomain : BProv HFFinAx_s C₂ PAInHF.domainForm := by
          simpa [PAInHF.domainForm] using
            BProv_HFFin_ordinalLike_of_rep P hrep
        have hconj : BProv HFFinAx_s C₂
            (fAnd PAInHF.domainForm
              (hfCompositeAt (totalCodedMap codedMap) phi)) :=
          PAInHF.BProv_andI hdomain hcomp
        apply PAInHF.BProv_exI (k := 0)
        simpa [codedEx, codedBody, rename,
          PAInHF.rename_domainForm_up,
          PAInHF.rename_domainForm_inst_zero,
          inst_total_codedBody] using hconj
      exact PAInHF.BProv_exE_of_sentences
        (B := HFFinAx_s) Sentences_HFFin
        (a := repBody) (c := rename Nat.succ codedEx)
        htotal' (by simpa [C₂] using hcodeOpened)
    exact PAInHF.BProv_exE_of_sentences
      (B := HFFinAx_s) Sentences_HFFin
      (a := rawBody) (c := codedEx)
      hrawEx (by simpa [C₁] using hrawOpened)
  have hmain : BProv HFFinAx_s G (fImp rawEx codedEx) := by
    simpa [C₀] using PAInHF.BProv_impI hcodedEx
  have hup : PAInHF.upVarMap rawMap = SetTheory.up rawMap := by
    funext n
    cases n <;> rfl
  simpa [rawEx, rawBody, codedEx, codedBody, hup,
    rename, hfCompositeAt_ex] using hmain

theorem BProv_HFFin_hfCompositeAt_ex_reverse
    (P : SetOrdinalRepresentationProofs)
    (phi : Form)
    (ih : ∀ (G : List Form) (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv HFFinAx_s G
          (HF_setOrdinalRepAt (rawMap n) (codedMap n))) →
      BProv HFFinAx_s G
        (fIff (rename rawMap phi) (hfCompositeAt codedMap phi)))
    (G : List Form) (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (fEx phi) →
      BProv HFFinAx_s G
        (HF_setOrdinalRepAt (rawMap n) (codedMap n))) :
    BProv HFFinAx_s G
      (fImp (hfCompositeAt codedMap (fEx phi))
        (rename rawMap (fEx phi))) := by
  let rawBody : Form :=
    rename (PAInHF.upVarMap rawMap) phi
  let codedBody : Form :=
    hfCompositeAt (PAInHF.upVarMap codedMap) phi
  let rawEx : Form := fEx rawBody
  let pairBody : Form := fAnd PAInHF.domainForm codedBody
  let codedEx : Form := fEx pairBody
  let C₀ : List Form := codedEx :: G
  have hrawEx : BProv HFFinAx_s C₀ rawEx := by
    have hcodedEx : BProv HFFinAx_s C₀ codedEx :=
      BProv_of_Prov (B := HFFinAx_s)
        (Prov.P_ass C₀ _ (by simp [C₀]))
    let C₁ : List Form := pairBody :: C₀.map (rename Nat.succ)
    have hcodedOpened : BProv HFFinAx_s C₁
        (rename Nat.succ rawEx) := by
      have hpair : BProv HFFinAx_s C₁ pairBody :=
        BProv_of_Prov (B := HFFinAx_s)
          (Prov.P_ass C₁ _ (by simp [C₁]))
      have hdomain : BProv HFFinAx_s C₁ PAInHF.domainForm := by
        simpa [pairBody] using PAInHF.BProv_andE1 hpair
      have hrange :=
        BProv_HFFin_rep_exists_of_ordinalLike P hdomain
      let repBody : Form := HF_setOrdinalRepAt 0 1
      have hrange' : BProv HFFinAx_s C₁ (fEx repBody) := by
        simpa [repBody] using hrange
      let C₂ : List Form := repBody :: C₁.map (rename Nat.succ)
      have hrawOpened : BProv HFFinAx_s C₂
          (rename Nat.succ (rename Nat.succ rawEx)) := by
        have hrep : BProv HFFinAx_s C₂
            (HF_setOrdinalRepAt 0 1) := by
          have hass : BProv HFFinAx_s C₂ repBody :=
            BProv_of_Prov (B := HFFinAx_s)
              (Prov.P_ass C₂ _ (by simp [C₂]))
          simpa [repBody] using hass
        have hpaired : ∀ n, Free n phi →
            BProv HFFinAx_s C₂
              (HF_setOrdinalRepAt
                (rangeRawMap rawMap n)
                (rangeCodedMap codedMap n)) := by
          intro n hn
          cases n with
          | zero =>
              simpa [rangeRawMap,
                rangeCodedMap] using hrep
          | succ n =>
              have h₀ := hcode n hn
              have h₁ := BProv_rename_of_sentences
                Sentences_HFFin h₀ Nat.succ
              have h₂ := BProv_rename_of_sentences
                Sentences_HFFin h₁ Nat.succ
              have hexCtx := PAInHF.BProv_context_cons
                (a := rename Nat.succ (rename Nat.succ codedEx)) h₂
              have hpairCtx := PAInHF.BProv_context_cons
                (a := rename Nat.succ pairBody) hexCtx
              have hctx := PAInHF.BProv_context_cons
                (a := repBody) hpairCtx
              simpa [C₂, C₁, C₀,
                rangeRawMap, rangeCodedMap,
                rename_HF_setOrdinalRepAt, List.map_map,
                Function.comp_def] using hctx
        have hih := ih C₂
          (rangeRawMap rawMap)
          (rangeCodedMap codedMap) hpaired
        have hihReverse : BProv HFFinAx_s C₂
            (fImp
              (hfCompositeAt (rangeCodedMap codedMap) phi)
              (rename (rangeRawMap rawMap) phi)) := by
          simpa [fIff] using PAInHF.BProv_andE2 hih
        have hpairShifted : BProv HFFinAx_s C₂
            (rename Nat.succ pairBody) :=
          BProv_of_Prov (B := HFFinAx_s)
            (Prov.P_ass C₂ _ (by simp [C₂, C₁]))
        have hcompShifted : BProv HFFinAx_s C₂
            (rename Nat.succ codedBody) := by
          simpa [pairBody, rename] using
            PAInHF.BProv_andE2 hpairShifted
        have hcomp : BProv HFFinAx_s C₂
            (hfCompositeAt (rangeCodedMap codedMap) phi) := by
          simpa [codedBody, rename_succ_hfCompositeAt_up]
            using hcompShifted
        have hraw : BProv HFFinAx_s C₂
            (rename (rangeRawMap rawMap) phi) :=
          BProv_mp HFFinAx_s C₂ _ _ hihReverse hcomp
        apply PAInHF.BProv_exI (k := 0)
        simpa [rawEx, rawBody, rename,
          inst_range_rawBody] using hraw
      exact PAInHF.BProv_exE_of_sentences
        (B := HFFinAx_s) Sentences_HFFin
        (a := repBody) (c := rename Nat.succ rawEx)
        hrange' (by simpa [C₂] using hrawOpened)
    exact PAInHF.BProv_exE_of_sentences
      (B := HFFinAx_s) Sentences_HFFin
      (a := pairBody) (c := rawEx)
      hcodedEx (by simpa [C₁] using hcodedOpened)
  have hmain : BProv HFFinAx_s G (fImp codedEx rawEx) := by
    simpa [C₀] using PAInHF.BProv_impI hrawEx
  have hup : PAInHF.upVarMap rawMap = SetTheory.up rawMap := by
    funext n
    cases n <;> rfl
  simpa [rawEx, rawBody, codedEx, pairBody, codedBody, hup,
    rename, hfCompositeAt_ex] using hmain

theorem BProv_HFFin_hfCompositeAt_ex
    (P : SetOrdinalRepresentationProofs)
    (phi : Form)
    (ih : ∀ (G : List Form) (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv HFFinAx_s G
          (HF_setOrdinalRepAt (rawMap n) (codedMap n))) →
      BProv HFFinAx_s G
        (fIff (rename rawMap phi) (hfCompositeAt codedMap phi)))
    (G : List Form) (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (fEx phi) →
      BProv HFFinAx_s G
        (HF_setOrdinalRepAt (rawMap n) (codedMap n))) :
    BProv HFFinAx_s G
      (fIff (rename rawMap (fEx phi))
        (hfCompositeAt codedMap (fEx phi))) := by
  have hforward :=
    BProv_HFFin_hfCompositeAt_ex_forward
      P phi ih G rawMap codedMap hcode
  have hreverse :=
    BProv_HFFin_hfCompositeAt_ex_reverse
      P phi ih G rawMap codedMap hcode
  simpa [fIff] using PAInHF.BProv_andI hforward hreverse

/-! ### Full paired-variable structural induction -/

theorem BProv_HFFin_hfCompositeAt_iff
    (P : SetOrdinalRepresentationProofs) :
    ∀ (G : List Form) (phi : Form) (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv HFFinAx_s G
          (HF_setOrdinalRepAt (rawMap n) (codedMap n))) →
      BProv HFFinAx_s G
        (fIff (rename rawMap phi) (hfCompositeAt codedMap phi)) := by
  intro G phi
  induction phi generalizing G with
  | fMem elem set =>
      intro rawMap codedMap hrep
      exact BProv_HFFin_hfCompositeAt_mem_of_representations
        P rawMap codedMap
        (hrep elem (Or.inl rfl))
        (hrep set (Or.inr rfl))
  | fEq left right =>
      intro rawMap codedMap hrep
      exact BProv_HFFin_hfCompositeAt_eq_of_representations
        P rawMap codedMap
        (hrep left (Or.inl rfl))
        (hrep right (Or.inr rfl))
  | fBot =>
      intro rawMap codedMap hrep
      simpa [hfCompositeAt, PA.Formula.hfFormulaAt,
        PAInHF.formulaAt, rename] using
        (BProv_fIff_refl (B := HFFinAx_s) (G := G) fBot)
  | fImp a b iha ihb =>
      intro rawMap codedMap hrep
      have ha := iha G rawMap codedMap
        (fun n hn => hrep n (Or.inl hn))
      have hb := ihb G rawMap codedMap
        (fun n hn => hrep n (Or.inr hn))
      simpa [hfCompositeAt, PA.Formula.hfFormulaAt,
        PAInHF.formulaAt, rename] using
        BProv_fIff_imp_congr ha hb
  | fAnd a b iha ihb =>
      intro rawMap codedMap hrep
      have ha := iha G rawMap codedMap
        (fun n hn => hrep n (Or.inl hn))
      have hb := ihb G rawMap codedMap
        (fun n hn => hrep n (Or.inr hn))
      simpa [hfCompositeAt, PA.Formula.hfFormulaAt,
        PAInHF.formulaAt, rename] using
        BProv_fIff_and_congr ha hb
  | fOr a b iha ihb =>
      intro rawMap codedMap hrep
      have ha := iha G rawMap codedMap
        (fun n hn => hrep n (Or.inl hn))
      have hb := ihb G rawMap codedMap
        (fun n hn => hrep n (Or.inr hn))
      simpa [hfCompositeAt, PA.Formula.hfFormulaAt,
        PAInHF.formulaAt, rename] using
        BProv_fIff_or_congr ha hb
  | fAll a ih =>
      intro rawMap codedMap hrep
      exact BProv_HFFin_hfCompositeAt_all
        P a (fun G rawMap codedMap => ih G rawMap codedMap)
        G rawMap codedMap hrep
  | fEx a ih =>
      intro rawMap codedMap hrep
      exact BProv_HFFin_hfCompositeAt_ex
        P a (fun G rawMap codedMap => ih G rawMap codedMap)
        G rawMap codedMap hrep

def HFCompositeStructuralProofs_of_representationProofs
    (P : SetOrdinalRepresentationProofs) :
    HFCompositeStructuralProofs where
  toSetOrdinalRepresentationProofs := P
  formula_exact := BProv_HFFin_hfCompositeAt_iff P

/-- A representation proof package alone closes the HF composite identity on
every sentence. -/
theorem BProv_HFFin_hf_roundTrip_of_representationProofs
    (P : SetOrdinalRepresentationProofs)
    (phi : Form) (hphi : Sentence phi) :
    BProv HFFinAx_s []
      (fIff phi
        (PAInHF.translateFormula
          (PA.Formula.translateHFFormula phi))) :=
  BProv_HFFin_hf_roundTrip_of_structuralProofs
    (HFCompositeStructuralProofs_of_representationProofs P) phi hphi

/-- The two concrete relational proof packages now suffice to assemble the
full deductive PA/finite-HF bi-interpretation certificate.  Both formula-level
structural inductions are supplied canonically. -/
def PAHFFinDeductiveBiInterpretationCertificate_of_graphRepresentationProofs
    (PPA : PA.Formula.OrdinalCodeGraphProofs)
    (PHF : SetOrdinalRepresentationProofs) :
    PAHFFinDeductiveBiInterpretationCertificate :=
  PAHFFinDeductiveBiInterpretationCertificate_of_structuralProofs
    (PA.Formula.PACompositeStructuralProofs_of_graphProofs PPA)
    (HFCompositeStructuralProofs_of_representationProofs PHF)


/-! ## Arbitrary finite-model semantics of the representation certificate -/

/-- Semantic reading of `HF_setOrdinalRepCertificateAt` in a chosen
first-order adjunction model.  The ambient environment is retained explicitly;
the two composite-membership occurrences below are exactly the environments
produced by the binders in the object-language certificate. -/
def ModelSetOrdinalRepCertificate {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α) (relation : α) : Prop :=
  FirstOrderAdjunctionModel.PairFunctional M relation ∧
    ∀ set code,
      M.mem (FirstOrderAdjunctionModel.kpair M set code) relation →
        OrdinalLike M.mem code ∧
          (∀ elem,
              M.mem elem set ↔
                ∃ elemCode,
                  M.mem (FirstOrderAdjunctionModel.kpair M elem elemCode)
                      relation ∧
                    Sat M.mem
                      (scons elemCode
                        (scons elem (scons code (scons set e))))
                      (HF_compositeMemAt 0 2)) ∧
            ∀ elemCode,
              OrdinalLike M.mem elemCode →
              Sat M.mem
                (scons elemCode (scons code (scons set e)))
                (HF_compositeMemAt 0 1) →
                ∃ elem,
                  M.mem (FirstOrderAdjunctionModel.kpair M elem elemCode)
                    relation

theorem HF_setOrdinalRepCertificateAt_model
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (relation : Nat) :
    Sat M.mem e (HF_setOrdinalRepCertificateAt relation) ↔
      ModelSetOrdinalRepCertificate M e (e relation) := by
  constructor
  · intro h
    refine ⟨(FirstOrderAdjunctionModel.HF_pairFunctionalAt_spec
      M e relation).mp h.1, ?_⟩
    intro set code hpair
    let E : Nat → α := scons code (scons set e)
    have hpairSat : Sat M.mem E
        (HF_pairMemAt 1 0 (relation+2)) := by
      apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec
        M E 1 0 (relation+2)).mpr
      simpa [E, scons] using hpair
    have hlocal := h.2 set code hpairSat
    have hcodeOrd : OrdinalLike M.mem code := by
      have hspec := (HF_ordinalLikeAt_spec E 0).mp hlocal.1
      simpa [E, scons] using hspec
    refine ⟨hcodeOrd, ?_, ?_⟩
    · intro elem
      have hpoint := hlocal.2.1 elem
      rw [Sat_fIff] at hpoint
      constructor
      · intro hmem
        have hmemSat : Sat M.mem (scons elem E) (fMem 0 2) := by
          change M.mem elem set
          exact hmem
        rcases hpoint.mp hmemSat with
          ⟨elemCode, hchildSat, hcodedSat⟩
        have hchild : M.mem
            (FirstOrderAdjunctionModel.kpair M elem elemCode)
            (e relation) := by
          have hspec :=
            (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
              (scons elemCode (scons elem E)) 1 0 (relation+4)).mp
                hchildSat
          simpa [E, scons] using hspec
        exact ⟨elemCode, hchild, by simpa [E] using hcodedSat⟩
      · intro hmem
        rcases hmem with ⟨elemCode, hchild, hcoded⟩
        have hchildSat : Sat M.mem
            (scons elemCode (scons elem E))
            (HF_pairMemAt 1 0 (relation+4)) := by
          apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
            (scons elemCode (scons elem E)) 1 0 (relation+4)).mpr
          simpa [E, scons] using hchild
        have hrhs : Sat M.mem (scons elem E)
            (fEx
              (fAnd
                (HF_pairMemAt 1 0 (relation+4))
                (HF_compositeMemAt 0 2))) :=
          ⟨elemCode, hchildSat, by simpa [E] using hcoded⟩
        have hmemSat := hpoint.mpr hrhs
        change M.mem elem set at hmemSat
        exact hmemSat
    · intro elemCode helemOrd hcoded
      let EC : Nat → α := scons elemCode E
      have helemOrdSat : Sat M.mem EC (HF_ordinalLikeAt 0) := by
        apply (HF_ordinalLikeAt_spec EC 0).mpr
        simpa [EC, scons] using helemOrd
      have hcodedSat : Sat M.mem EC (HF_compositeMemAt 0 1) := by
        simpa [EC, E] using hcoded
      rcases hlocal.2.2 elemCode ⟨helemOrdSat, hcodedSat⟩ with
        ⟨elem, hpairSat⟩
      refine ⟨elem, ?_⟩
      have hspec := (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
        (scons elem EC) 0 1 (relation+4)).mp hpairSat
      simpa [EC, E, scons] using hspec
  · intro h
    refine ⟨(FirstOrderAdjunctionModel.HF_pairFunctionalAt_spec
      M e relation).mpr h.1, ?_⟩
    intro set code hpairSat
    let E : Nat → α := scons code (scons set e)
    have hpair : M.mem
        (FirstOrderAdjunctionModel.kpair M set code) (e relation) := by
      have hspec := (FirstOrderAdjunctionModel.HF_pairMemAt_spec
        M E 1 0 (relation+2)).mp hpairSat
      simpa [E, scons] using hspec
    have hlocal := h.2 set code hpair
    refine ⟨?_, ?_, ?_⟩
    · apply (HF_ordinalLikeAt_spec E 0).mpr
      simpa [E, scons] using hlocal.1
    · intro elem
      rw [Sat_fIff]
      constructor
      · intro hmemSat
        have hmem : M.mem elem set := by
          change M.mem elem set at hmemSat
          exact hmemSat
        rcases (hlocal.2.1 elem).mp hmem with
          ⟨elemCode, hchild, hcoded⟩
        refine ⟨elemCode, ?_, ?_⟩
        · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
            (scons elemCode (scons elem E)) 1 0 (relation+4)).mpr
          simpa [E, scons] using hchild
        · simpa [E] using hcoded
      · intro hrhs
        rcases hrhs with ⟨elemCode, hchildSat, hcodedSat⟩
        have hchild : M.mem
            (FirstOrderAdjunctionModel.kpair M elem elemCode)
            (e relation) := by
          have hspec := (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
            (scons elemCode (scons elem E)) 1 0 (relation+4)).mp
              hchildSat
          simpa [E, scons] using hspec
        have hcoded : Sat M.mem
            (scons elemCode (scons elem (scons code (scons set e))))
            (HF_compositeMemAt 0 2) := by
          simpa [E] using hcodedSat
        have hmem := (hlocal.2.1 elem).mpr ⟨elemCode, hchild, hcoded⟩
        change M.mem elem set
        exact hmem
    · intro elemCode hant
      have helemOrd : OrdinalLike M.mem elemCode := by
        have hspec := (HF_ordinalLikeAt_spec (scons elemCode E) 0).mp hant.1
        simpa [E, scons] using hspec
      have hcoded : Sat M.mem
          (scons elemCode (scons code (scons set e)))
          (HF_compositeMemAt 0 1) := by
        simpa [E] using hant.2
      rcases hlocal.2.2 elemCode helemOrd hcoded with ⟨elem, hpair⟩
      refine ⟨elem, ?_⟩
      apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
        (scons elem (scons elemCode E)) 0 1 (relation+4)).mpr
      simpa [E, scons] using hpair

/-- Arbitrary-model semantic reading of the root representation formula. -/
def ModelSetOrdinalRep {α : Type u}
    (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (set code : α) : Prop :=
  ∃ relation,
    M.mem (FirstOrderAdjunctionModel.kpair M set code) relation ∧
      ModelSetOrdinalRepCertificate M (scons relation e) relation

theorem HF_setOrdinalRepAt_model
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (set code : Nat) :
    Sat M.mem e (HF_setOrdinalRepAt set code) ↔
      ModelSetOrdinalRep M e (e set) (e code) := by
  constructor
  · intro h
    rcases h with ⟨relation, hrootSat, hcertSat⟩
    refine ⟨relation, ?_, ?_⟩
    · have hspec := (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
        (scons relation e) (set+1) (code+1) 0).mp hrootSat
      simpa [scons] using hspec
    · have hspec := HF_setOrdinalRepCertificateAt_model
        M (scons relation e) 0
      simpa [scons] using hspec.mp hcertSat
  · intro h
    rcases h with ⟨relation, hroot, hcert⟩
    refine ⟨relation, ?_, ?_⟩
    · apply (FirstOrderAdjunctionModel.HF_pairMemAt_spec M
        (scons relation e) (set+1) (code+1) 0).mpr
      simpa [scons] using hroot
    · apply (HF_setOrdinalRepCertificateAt_model
        M (scons relation e) 0).mpr
      simpa [scons] using hcert

/-! ## Exact completeness reduction for the totality field -/

/-- If the representation certificate can be constructed for every object in
every chosen first-order finite-HF model, relative completeness yields exactly
the `SetOrdinalRepresentationProofs.total` field, with arbitrary finite
context. -/
theorem BProv_HFFin_setOrdinalRep_total_of_model_total
    (hmodel : ∀ {α : Type}
      (M : FirstOrderFiniteAdjunctionModel α)
      (e : Nat → α) (set : Nat),
        ∃ code,
          ModelSetOrdinalRep M.toFirstOrderAdjunctionModel
            (scons code e) (e set) code)
    (G : List Form) (set : Nat) :
    BProv HFFinAx_s G
      (fEx (HF_setOrdinalRepAt (set+1) 0)) := by
  apply completeness_inf_context HFFinAx_s G
    (fEx (HF_setOrdinalRepAt (set+1) 0)) Sentences_HFFin
  intro Dom mem v hHF _hG
  let M : FirstOrderFiniteAdjunctionModel Dom :=
    firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  rcases hmodel M v set with ⟨code, hrep⟩
  refine ⟨code, ?_⟩
  apply (HF_setOrdinalRepAt_model
    M.toFirstOrderAdjunctionModel (scons code v) (set+1) 0).mpr
  simpa [scons] using hrep

/-! ## Honest base-certificate construction -/

/-- Arithmetic boundary needed by the empty-set certificate: the translated
Ackermann membership predicate has no member whose set-code is the internal
zero ordinal. -/
def NoCompositeMembersOfEmpty {α : Type u}
    (M : FirstOrderAdjunctionModel α) : Prop :=
  ∀ env : Nat → α,
    OrdinalLike M.mem (env 0) →
    env 1 = M.empty →
      ¬ Sat M.mem env (HF_compositeMemAt 0 1)

/-- Canonical arbitrary-model reading of the translated Ackermann membership
atom.  Its environment tail is immaterial because the formula has only slots
`0` and `1` free. -/
def ModelCompositeMem {α : Type u}
    (M : FirstOrderAdjunctionModel α) (elemCode setCode : α) : Prop :=
  Sat M.mem
    (scons elemCode (scons setCode (fun _ => M.empty)))
    (HF_compositeMemAt 0 1)

theorem HF_compositeMemAt_01_model
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (env : Nat → α) :
    Sat M.mem env (HF_compositeMemAt 0 1) ↔
      ModelCompositeMem M (env 0) (env 1) := by
  unfold ModelCompositeMem
  exact Sat_ext_free (HF_compositeMemAt 0 1) env
    (scons (env 0) (scons (env 1) (fun _ => M.empty))) (by
      intro n hn
      rcases HF_compositeMemAt_free hn with rfl | rfl <;> rfl)

theorem HF_compositeMemAt_02_model
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (env : Nat → α) :
    Sat M.mem env (HF_compositeMemAt 0 2) ↔
      ModelCompositeMem M (env 0) (env 2) := by
  let r : Nat → Nat := repPairSlotMap 0 2
  have hrenamed :
      rename r (HF_compositeMemAt 0 1) =
        HF_compositeMemAt 0 2 := by
    simpa [r, repPairSlotMap] using
      (rename_HF_compositeMemAt r 0 1)
  calc
    Sat M.mem env (HF_compositeMemAt 0 2) ↔
        Sat M.mem env (rename r (HF_compositeMemAt 0 1)) := by
          rw [hrenamed]
    _ ↔ Sat M.mem (fun n => env (r n))
        (HF_compositeMemAt 0 1) :=
      Sat_rename (mem := M.mem) (HF_compositeMemAt 0 1) r env
    _ ↔ ModelCompositeMem M (env 0) (env 2) := by
      simpa [r, repPairSlotMap] using
        (HF_compositeMemAt_01_model M (fun n => env (r n)))

/-- The singleton graph containing only `⟨∅,∅⟩`. -/
def emptySetOrdinalRepGraph {α : Type u}
    (M : FirstOrderAdjunctionModel α) : α :=
  FirstOrderAdjunctionModel.single M
    (FirstOrderAdjunctionModel.kpair M M.empty M.empty)

theorem emptySetOrdinalRepGraph_root {α : Type u}
    (M : FirstOrderAdjunctionModel α) :
    M.mem (FirstOrderAdjunctionModel.kpair M M.empty M.empty)
      (emptySetOrdinalRepGraph M) := by
  apply (FirstOrderAdjunctionModel.single_spec M
    (FirstOrderAdjunctionModel.kpair M M.empty M.empty)
    (FirstOrderAdjunctionModel.kpair M M.empty M.empty)).mpr
  rfl

/-- Kernel-checked empty-object representation certificate.  All set-theoretic
graph obligations are discharged here; the only remaining premise is the
explicit PA-arithmetic fact `NoCompositeMembersOfEmpty`. -/
theorem ModelSetOrdinalRep_empty
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (e : Nat → α) (hzero : NoCompositeMembersOfEmpty M) :
    ModelSetOrdinalRep M e M.empty M.empty := by
  let relation := emptySetOrdinalRepGraph M
  refine ⟨relation, emptySetOrdinalRepGraph_root M, ?_⟩
  refine ⟨?functional, ?certificate⟩
  · intro k y y' hky hky'
    have hkyEq : FirstOrderAdjunctionModel.kpair M k y =
        FirstOrderAdjunctionModel.kpair M M.empty M.empty :=
      (FirstOrderAdjunctionModel.single_spec M
        (FirstOrderAdjunctionModel.kpair M M.empty M.empty)
        (FirstOrderAdjunctionModel.kpair M k y)).mp hky
    have hky'Eq : FirstOrderAdjunctionModel.kpair M k y' =
        FirstOrderAdjunctionModel.kpair M M.empty M.empty :=
      (FirstOrderAdjunctionModel.single_spec M
        (FirstOrderAdjunctionModel.kpair M M.empty M.empty)
        (FirstOrderAdjunctionModel.kpair M k y')).mp hky'
    have hy := (FirstOrderAdjunctionModel.kpair_injective M hkyEq).2
    have hy' := (FirstOrderAdjunctionModel.kpair_injective M hky'Eq).2
    rw [hy, hy']
  · intro set code hpair
    have hpairEq : FirstOrderAdjunctionModel.kpair M set code =
        FirstOrderAdjunctionModel.kpair M M.empty M.empty :=
      (FirstOrderAdjunctionModel.single_spec M
        (FirstOrderAdjunctionModel.kpair M M.empty M.empty)
        (FirstOrderAdjunctionModel.kpair M set code)).mp hpair
    have hset : set = M.empty :=
      (FirstOrderAdjunctionModel.kpair_injective M hpairEq).1
    have hcode : code = M.empty :=
      (FirstOrderAdjunctionModel.kpair_injective M hpairEq).2
    subst set
    subst code
    refine ⟨FirstOrderAdjunctionModel.ordinalLike_empty M, ?_, ?_⟩
    · intro elem
      constructor
      · intro hmem
        exact False.elim (M.empty_spec elem hmem)
      · intro hrhs
        rcases hrhs with ⟨elemCode, hchild, hcoded⟩
        have hchildEq : FirstOrderAdjunctionModel.kpair M elem elemCode =
            FirstOrderAdjunctionModel.kpair M M.empty M.empty :=
          (FirstOrderAdjunctionModel.single_spec M
            (FirstOrderAdjunctionModel.kpair M M.empty M.empty)
            (FirstOrderAdjunctionModel.kpair M elem elemCode)).mp hchild
        have helemCode : elemCode = M.empty :=
          (FirstOrderAdjunctionModel.kpair_injective M hchildEq).2
        let sourceEnv : Nat → α :=
          scons elemCode
            (scons elem (scons M.empty (scons M.empty (scons relation e))))
        let r : Nat → Nat := repPairSlotMap 0 2
        have hrenamed :
            rename r (HF_compositeMemAt 0 1) =
              HF_compositeMemAt 0 2 := by
          simpa [r, repPairSlotMap] using
            (rename_HF_compositeMemAt r 0 1)
        have hcoded01 : Sat M.mem (fun n => sourceEnv (r n))
            (HF_compositeMemAt 0 1) := by
          apply (Sat_rename (mem := M.mem)
            (HF_compositeMemAt 0 1) r sourceEnv).mp
          rw [hrenamed]
          simpa [sourceEnv] using hcoded
        have hord : OrdinalLike M.mem ((fun n => sourceEnv (r n)) 0) := by
          change OrdinalLike M.mem elemCode
          rw [helemCode]
          exact FirstOrderAdjunctionModel.ordinalLike_empty M
        have hsetZero : (fun n => sourceEnv (r n)) 1 = M.empty := by
          rfl
        exact False.elim
          (hzero (fun n => sourceEnv (r n)) hord hsetZero hcoded01)
    · intro elemCode helemOrd hcoded
      have hsetZero :
          (scons elemCode
            (scons M.empty (scons M.empty (scons relation e)))) 1 =
              M.empty := rfl
      exact False.elim
        (hzero
          (scons elemCode
            (scons M.empty (scons M.empty (scons relation e))))
          helemOrd hsetZero hcoded)

/-! ## Discharging the empty-code arithmetic boundary -/

theorem PA_BProv_no_hfMem_of_eq_zero :
    PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.imp (PA.Formula.eqConstAt 1 0)
        (PA.Formula.imp (PA.Formula.hfMemAt 0 1)
          PA.Formula.bot)) := by
  apply PA.Formula.BProv_impI
  apply PA.Formula.BProv_impI
  let C : List PA.Formula :=
    PA.Formula.hfMemAt 0 1 :: PA.Formula.eqConstAt 1 0 :: []
  have hset : PA.Formula.BProv PA.Formula.Ax_s C
      (PA.Formula.eqConstAt 1 0) :=
    PA.Formula.BProv_ass (by simp [C])
  have hmem : PA.Formula.BProv PA.Formula.Ax_s C
      (PA.Formula.hfMemAt 0 1) :=
    PA.Formula.BProv_ass (by simp [C])
  exact PA.Formula.BProv_Ax_s_hfMemAt_bot_of_eqConst_zero hset hmem

theorem NoCompositeMembersOfEmpty_of_HFFinAx_s
    {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g) :
    let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    NoCompositeMembersOfEmpty M.toFirstOrderAdjunctionModel := by
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  change NoCompositeMembersOfEmpty M.toFirstOrderAdjunctionModel
  rcases PAInHF.BProv_HFFin_formulaAt_of_PA_BProv_domainContext
      PA_BProv_no_hfMem_of_eq_zero with
    ⟨n, htranslated⟩
  intro env helem hset hcomp
  let ρ : Nat → Nat := repPairSlotMap 0 1
  have hord : ∀ k, k < n → OrdinalLike M.mem (env (ρ k)) := by
    intro k hk
    cases k with
    | zero =>
        simpa [ρ, repPairSlotMap] using helem
    | succ k =>
        have hslot : env (ρ (k+1)) = M.empty := by
          simpa [ρ, repPairSlotMap] using hset
        rw [hslot]
        exact FirstOrderAdjunctionModel.ordinalLike_empty
          M.toFirstOrderAdjunctionModel
  have hdomain : ∀ g,
      g ∈ PAInHF.domainContextAt ρ n → Sat M.mem env g :=
    PAInHF.Sat_domainContextAt_of_ordinalLike hord
  have hAx : ∀ g, HFFinAx_s g → Sat M.mem env g := by
    intro g hg
    exact (Sat_sentence_inv g (Sentences_HFFin g hg) v env).mp
      (hHF g hg)
  have htranslatedSat := soundness_BProv (htranslated ρ) env hAx (by
    intro g hg
    simp only [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hdomain g hg
    · simp [PAInHF.translateContextAt] at hg)
  have hzeroEq : Sat M.mem env
      (PAInHF.formulaAt ρ (PA.Formula.eqConstAt 1 0)) := by
    change ∃ x y,
      Sat M.mem (scons y (scons x env))
          (PAInHF.termGraphAt (fun k => ρ k + 2) 1 (PA.Term.var 1)) ∧
        Sat M.mem (scons y (scons x env))
          (PAInHF.termGraphAt (fun k => ρ k + 2) 0 PA.Term.zero) ∧
          x = y
    refine ⟨M.empty, M.empty, ?_, ?_, rfl⟩
    · apply (PAInHF.termGraphAt_var_spec
        (fun k => ρ k + 2) 1 1
        (scons M.empty (scons M.empty env))).mpr
      simpa [ρ, repPairSlotMap, scons] using hset.symm
    · apply (PAInHF.termGraphAt_zero_spec
        (fun k => ρ k + 2) 0
        (scons M.empty (scons M.empty env))).mpr
      exact M.empty_spec
  have hmem : Sat M.mem env
      (PAInHF.formulaAt ρ (PA.Formula.hfMemAt 0 1)) := by
    simpa [HF_compositeMemAt, ρ] using hcomp
  exact htranslatedSat hzeroEq hmem

theorem ModelSetOrdinalRep_empty_of_HFFinAx_s
    {α : Type u} {mem : α → α → Prop}
    (v : Nat → α) (hHF : ∀ g, HFFinAx_s g → Sat mem v g)
    (e : Nat → α) :
    let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    ModelSetOrdinalRep M.toFirstOrderAdjunctionModel
      e M.empty M.empty := by
  let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  exact ModelSetOrdinalRep_empty M.toFirstOrderAdjunctionModel e
    (NoCompositeMembersOfEmpty_of_HFFinAx_s v hHF)

/-- The empty-object base case required by a future finite-generation or
set-induction proof of representation totality. -/
theorem BProv_HFFin_setOrdinalRep_total_of_empty
    (G : List Form) (set : Nat) :
    BProv HFFinAx_s G
      (fImp (HF_emptyAt set)
        (fEx (HF_setOrdinalRepAt (set+1) 0))) := by
  apply completeness_inf_context HFFinAx_s G
    (fImp (HF_emptyAt set)
      (fEx (HF_setOrdinalRepAt (set+1) 0))) Sentences_HFFin
  intro Dom mem v hHF _hG hEmpty
  let M : FirstOrderFiniteAdjunctionModel Dom :=
    firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  have hset : v set = M.empty :=
    (FirstOrderAdjunctionModel.HF_emptyAt_empty
      M.toFirstOrderAdjunctionModel v set).mp hEmpty
  refine ⟨M.empty, ?_⟩
  apply (HF_setOrdinalRepAt_model
    M.toFirstOrderAdjunctionModel (scons M.empty v) (set+1) 0).mpr
  have hrep := ModelSetOrdinalRep_empty_of_HFFinAx_s
    v hHF (scons M.empty v)
  simpa [scons, hset] using hrep

/-! ## Single-relation adjunction extension interface -/

/-- Exact hypotheses under which one certified relation containing both input
representations can be extended by the representation of their adjunction.

`code_injective` and the three freshness/compatibility clauses are the honest
merge boundary: they are precisely what prevents the newly adjoined root pair
from creating spurious witnesses in an existing certificate. -/
structure ModelSetOrdinalRepAdjoinData
    {α : Type u} (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    (relation old oldCode elem elemCode newSet newCode : α) : Prop where
  certificate : ModelSetOrdinalRepCertificate M e relation
  code_injective : ∀ {set₁ set₂ code},
    M.mem (FirstOrderAdjunctionModel.kpair M set₁ code) relation →
    M.mem (FirstOrderAdjunctionModel.kpair M set₂ code) relation →
      set₁ = set₂
  old_root :
    M.mem (FirstOrderAdjunctionModel.kpair M old oldCode) relation
  elem_root :
    M.mem (FirstOrderAdjunctionModel.kpair M elem elemCode) relation
  newSet_spec : ∀ x, M.mem x newSet ↔ M.mem x old ∨ x = elem
  newCode_ordinal : OrdinalLike M.mem newCode
  code_adjoin : ∀ query,
    OrdinalLike M.mem query →
      (ModelCompositeMem M query newCode ↔
        ModelCompositeMem M query oldCode ∨ query = elemCode)
  root_compatible : ∀ code,
    M.mem (FirstOrderAdjunctionModel.kpair M newSet code) relation →
      code = newCode
  newCode_not_old_member : ∀ {set code},
    M.mem (FirstOrderAdjunctionModel.kpair M set code) relation →
      ¬ ModelCompositeMem M newCode code
  newCode_irrefl : ¬ ModelCompositeMem M newCode newCode

def adjoinSetOrdinalRepGraph
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (relation newSet newCode : α) : α :=
  M.adjoin relation
    (FirstOrderAdjunctionModel.kpair M newSet newCode)

theorem adjoinSetOrdinalRepGraph_old
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    {relation newSet newCode p : α} (hp : M.mem p relation) :
    M.mem p (adjoinSetOrdinalRepGraph M relation newSet newCode) :=
  (M.adjoin_spec p relation
    (FirstOrderAdjunctionModel.kpair M newSet newCode)).mpr (Or.inl hp)

theorem adjoinSetOrdinalRepGraph_new
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (relation newSet newCode : α) :
    M.mem (FirstOrderAdjunctionModel.kpair M newSet newCode)
      (adjoinSetOrdinalRepGraph M relation newSet newCode) :=
  (M.adjoin_spec
    (FirstOrderAdjunctionModel.kpair M newSet newCode) relation
    (FirstOrderAdjunctionModel.kpair M newSet newCode)).mpr (Or.inr rfl)

theorem ModelSetOrdinalRepCertificate_adjoin
    {α : Type u} (M : FirstOrderAdjunctionModel α) (e : Nat → α)
    {relation old oldCode elem elemCode newSet newCode : α}
    (D : ModelSetOrdinalRepAdjoinData M e relation
      old oldCode elem elemCode newSet newCode) :
    ModelSetOrdinalRepCertificate M e
      (adjoinSetOrdinalRepGraph M relation newSet newCode) := by
  let newPair := FirstOrderAdjunctionModel.kpair M newSet newCode
  let extended := adjoinSetOrdinalRepGraph M relation newSet newCode
  have hmemExtended : ∀ p, M.mem p extended ↔
      M.mem p relation ∨ p = newPair := by
    intro p
    exact M.adjoin_spec p relation newPair
  refine ⟨?functional, ?certificate⟩
  · intro key value value' hvalue hvalue'
    rcases (hmemExtended
      (FirstOrderAdjunctionModel.kpair M key value)).mp hvalue with
      hOld | hNew
    · rcases (hmemExtended
        (FirstOrderAdjunctionModel.kpair M key value')).mp hvalue' with
        hOld' | hNew'
      · exact D.certificate.1 key value value' hOld hOld'
      · have hk : key = newSet :=
          (FirstOrderAdjunctionModel.kpair_injective M hNew').1
        have hv' : value' = newCode :=
          (FirstOrderAdjunctionModel.kpair_injective M hNew').2
        have hv : value = newCode := by
          apply D.root_compatible value
          simpa [hk] using hOld
        rw [hv, hv']
    · rcases (hmemExtended
        (FirstOrderAdjunctionModel.kpair M key value')).mp hvalue' with
        hOld' | hNew'
      · have hk : key = newSet :=
          (FirstOrderAdjunctionModel.kpair_injective M hNew).1
        have hv : value = newCode :=
          (FirstOrderAdjunctionModel.kpair_injective M hNew).2
        have hv' : value' = newCode := by
          apply D.root_compatible value'
          simpa [hk] using hOld'
        rw [hv, hv']
      · have hv : value = newCode :=
          (FirstOrderAdjunctionModel.kpair_injective M hNew).2
        have hv' : value' = newCode :=
          (FirstOrderAdjunctionModel.kpair_injective M hNew').2
        rw [hv, hv']
  · intro set code hpair
    rcases (hmemExtended
      (FirstOrderAdjunctionModel.kpair M set code)).mp hpair with
      hOld | hNew
    · have hlocal := D.certificate.2 set code hOld
      refine ⟨hlocal.1, ?_, ?_⟩
      · intro child
        constructor
        · intro hchild
          rcases (hlocal.2.1 child).mp hchild with
            ⟨childCode, hchildPair, hcoded⟩
          exact ⟨childCode,
            adjoinSetOrdinalRepGraph_old M hchildPair, hcoded⟩
        · intro hrhs
          rcases hrhs with ⟨childCode, hchildPair, hcoded⟩
          rcases (hmemExtended
            (FirstOrderAdjunctionModel.kpair M child childCode)).mp
              hchildPair with hchildOld | hchildNew
          · exact (hlocal.2.1 child).mpr
              ⟨childCode, hchildOld, hcoded⟩
          · have hchildCode : childCode = newCode :=
              (FirstOrderAdjunctionModel.kpair_injective M hchildNew).2
            have hcodedModel : ModelCompositeMem M childCode code := by
              have hspec := HF_compositeMemAt_02_model M
                (scons childCode (scons child (scons code (scons set e))))
              simpa [scons] using hspec.mp hcoded
            exact False.elim
              (D.newCode_not_old_member hOld (by
                simpa [hchildCode] using hcodedModel))
      · intro query hqueryOrd hcoded
        rcases hlocal.2.2 query hqueryOrd hcoded with
          ⟨child, hchildPair⟩
        exact ⟨child, adjoinSetOrdinalRepGraph_old M hchildPair⟩
    · have hset : set = newSet :=
        (FirstOrderAdjunctionModel.kpair_injective M hNew).1
      have hcode : code = newCode :=
        (FirstOrderAdjunctionModel.kpair_injective M hNew).2
      subst set
      subst code
      have holdLocal := D.certificate.2 old oldCode D.old_root
      refine ⟨D.newCode_ordinal, ?_, ?_⟩
      · intro child
        constructor
        · intro hchild
          rcases (D.newSet_spec child).mp hchild with
            hchildOld | hchildElem
          · rcases (holdLocal.2.1 child).mp hchildOld with
              ⟨childCode, hchildPair, hcodedOld⟩
            have hchildOrd := (D.certificate.2 child childCode hchildPair).1
            have hcodedOldModel :
                ModelCompositeMem M childCode oldCode := by
              have hspec := HF_compositeMemAt_02_model M
                (scons childCode
                  (scons child (scons oldCode (scons old e))))
              simpa [scons] using hspec.mp hcodedOld
            have hcodedNewModel :
                ModelCompositeMem M childCode newCode :=
              (D.code_adjoin childCode hchildOrd).mpr (Or.inl hcodedOldModel)
            have hcodedNew : Sat M.mem
                (scons childCode
                  (scons child (scons newCode (scons newSet e))))
                (HF_compositeMemAt 0 2) := by
              have hspec := HF_compositeMemAt_02_model M
                (scons childCode
                  (scons child (scons newCode (scons newSet e))))
              apply hspec.mpr
              simpa [scons] using hcodedNewModel
            exact ⟨childCode,
              adjoinSetOrdinalRepGraph_old M hchildPair,
              hcodedNew⟩
          · subst child
            have helemOrd :=
              (D.certificate.2 elem elemCode D.elem_root).1
            have hcodedNewModel :
                ModelCompositeMem M elemCode newCode :=
              (D.code_adjoin elemCode helemOrd).mpr (Or.inr rfl)
            have hcodedNew : Sat M.mem
                (scons elemCode
                  (scons elem (scons newCode (scons newSet e))))
                (HF_compositeMemAt 0 2) := by
              have hspec := HF_compositeMemAt_02_model M
                (scons elemCode
                  (scons elem (scons newCode (scons newSet e))))
              apply hspec.mpr
              simpa [scons] using hcodedNewModel
            exact ⟨elemCode,
              adjoinSetOrdinalRepGraph_old M D.elem_root,
              hcodedNew⟩
        · intro hrhs
          rcases hrhs with ⟨childCode, hchildPair, hcodedNew⟩
          rcases (hmemExtended
            (FirstOrderAdjunctionModel.kpair M child childCode)).mp
              hchildPair with hchildOld | hchildNew
          · have hchildOrd :=
              (D.certificate.2 child childCode hchildOld).1
            have hcodedNewModel :
                ModelCompositeMem M childCode newCode := by
              have hspec := HF_compositeMemAt_02_model M
                (scons childCode
                  (scons child (scons newCode (scons newSet e))))
              simpa [scons] using hspec.mp hcodedNew
            rcases (D.code_adjoin childCode hchildOrd).mp hcodedNewModel with
              hcodedOldModel | hchildCode
            · apply (D.newSet_spec child).mpr
              left
              apply (holdLocal.2.1 child).mpr
              refine ⟨childCode, hchildOld, ?_⟩
              have hspec := HF_compositeMemAt_02_model M
                (scons childCode
                  (scons child (scons oldCode (scons old e))))
              apply hspec.mpr
              simpa [scons] using hcodedOldModel
            · apply (D.newSet_spec child).mpr
              right
              have hchildOld' : M.mem
                  (FirstOrderAdjunctionModel.kpair M child elemCode)
                  relation := by
                simpa [hchildCode] using hchildOld
              exact D.code_injective hchildOld' D.elem_root
          · have hchildCode : childCode = newCode :=
              (FirstOrderAdjunctionModel.kpair_injective M hchildNew).2
            have hcodedSelf : ModelCompositeMem M newCode newCode := by
              have hspec := HF_compositeMemAt_02_model M
                (scons childCode
                  (scons child (scons newCode (scons newSet e))))
              have hcodedModel := hspec.mp hcodedNew
              simpa [scons, hchildCode] using hcodedModel
            exact False.elim (D.newCode_irrefl hcodedSelf)
      · intro query hqueryOrd hcodedNew
        have hcodedNewModel : ModelCompositeMem M query newCode := by
          have hspec := HF_compositeMemAt_01_model M
            (scons query (scons newCode (scons newSet e)))
          simpa [scons] using hspec.mp hcodedNew
        rcases (D.code_adjoin query hqueryOrd).mp hcodedNewModel with
          hcodedOldModel | hquery
        · rcases holdLocal.2.2 query hqueryOrd (by
            have hspec := HF_compositeMemAt_01_model M
              (scons query (scons oldCode (scons old e)))
            apply hspec.mpr
            simpa [scons] using hcodedOldModel) with
            ⟨child, hchildPair⟩
          exact ⟨child, adjoinSetOrdinalRepGraph_old M hchildPair⟩
        · subst query
          exact ⟨elem, adjoinSetOrdinalRepGraph_old M D.elem_root⟩

/-- The environment parameter in the semantic certificate is bookkeeping only:
all actual composite-membership slots are explicitly rebound. -/
theorem ModelSetOrdinalRepCertificate_changeEnv
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    {e e' : Nat → α} {relation : α}
    (h : ModelSetOrdinalRepCertificate M e relation) :
    ModelSetOrdinalRepCertificate M e' relation := by
  refine ⟨h.1, ?_⟩
  intro set code hpair
  have hlocal := h.2 set code hpair
  refine ⟨hlocal.1, ?_, ?_⟩
  · intro elem
    constructor
    · intro hmem
      rcases (hlocal.2.1 elem).mp hmem with
        ⟨elemCode, hchild, hcoded⟩
      refine ⟨elemCode, hchild, ?_⟩
      have hcodedModel : ModelCompositeMem M elemCode code := by
        have hspec := HF_compositeMemAt_02_model M
          (scons elemCode (scons elem (scons code (scons set e))))
        simpa [scons] using hspec.mp hcoded
      have hspec := HF_compositeMemAt_02_model M
        (scons elemCode (scons elem (scons code (scons set e'))))
      apply hspec.mpr
      simpa [scons] using hcodedModel
    · intro hrhs
      rcases hrhs with ⟨elemCode, hchild, hcoded⟩
      apply (hlocal.2.1 elem).mpr
      refine ⟨elemCode, hchild, ?_⟩
      have hcodedModel : ModelCompositeMem M elemCode code := by
        have hspec := HF_compositeMemAt_02_model M
          (scons elemCode (scons elem (scons code (scons set e'))))
        simpa [scons] using hspec.mp hcoded
      have hspec := HF_compositeMemAt_02_model M
        (scons elemCode (scons elem (scons code (scons set e))))
      apply hspec.mpr
      simpa [scons] using hcodedModel
  · intro query hqueryOrd hcoded
    have hcodedModel : ModelCompositeMem M query code := by
      have hspec := HF_compositeMemAt_01_model M
        (scons query (scons code (scons set e')))
      simpa [scons] using hspec.mp hcoded
    have hcodedOld : Sat M.mem
        (scons query (scons code (scons set e)))
        (HF_compositeMemAt 0 1) := by
      have hspec := HF_compositeMemAt_01_model M
        (scons query (scons code (scons set e)))
      apply hspec.mpr
      simpa [scons] using hcodedModel
    exact hlocal.2.2 query hqueryOrd hcodedOld

/-! ## Exact separate-relation merge boundary -/

/-- A common certified graph containing two independently obtained roots. -/
structure ModelSetOrdinalRepMergeResult
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (rootEnv : Nat → α) (old oldCode elem elemCode : α) where
  relation : α
  certificate : ModelSetOrdinalRepCertificate M
    (scons relation rootEnv) relation
  code_injective : ∀ {set₁ set₂ code},
    M.mem (FirstOrderAdjunctionModel.kpair M set₁ code) relation →
    M.mem (FirstOrderAdjunctionModel.kpair M set₂ code) relation →
      set₁ = set₂
  old_root :
    M.mem (FirstOrderAdjunctionModel.kpair M old oldCode) relation
  elem_root :
    M.mem (FirstOrderAdjunctionModel.kpair M elem elemCode) relation

/-- The exact merge theorem still needed to combine representation witnesses
whose existentially chosen certificate relations are initially unrelated. -/
def ModelSetOrdinalRepMergeLaw
    {α : Type u} (M : FirstOrderAdjunctionModel α) : Prop :=
  ∀ (rootEnv : Nat → α) (old oldCode elem elemCode : α),
    ModelSetOrdinalRep M rootEnv old oldCode →
    ModelSetOrdinalRep M rootEnv elem elemCode →
      Nonempty (ModelSetOrdinalRepMergeResult M rootEnv
        old oldCode elem elemCode)

/-! ## Finite-model merging of independently chosen representation graphs -/

private theorem mergeModelSetOrdinalRep_changeEnv
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    {e e' : Nat → α} {set code : α}
    (h : ModelSetOrdinalRep M e set code) :
    ModelSetOrdinalRep M e' set code := by
  rcases h with ⟨relation, hroot, hcertificate⟩
  exact ⟨relation, hroot,
    ModelSetOrdinalRepCertificate_changeEnv M hcertificate⟩

private def mergeCanonicalRepEnv
    {α : Type u} (M : FirstOrderAdjunctionModel α) : Nat → α :=
  fun _ => M.empty

/-- The exact compatibility invariant needed to take the union of two
set-to-ordinal representation graphs.  The first clause is mixed graph
functionality; the second is mixed graph injectivity. -/
def ModelSetOrdinalRepRelationsCompatible {α : Type u}
    (M : FirstOrderAdjunctionModel α) (left right : α) : Prop :=
  (∀ {set leftCode rightCode},
      M.mem (FirstOrderAdjunctionModel.kpair M set leftCode) left →
      M.mem (FirstOrderAdjunctionModel.kpair M set rightCode) right →
        leftCode = rightCode) ∧
    (∀ {leftSet rightSet code},
      (M.mem (FirstOrderAdjunctionModel.kpair M leftSet code) left ∨
        M.mem (FirstOrderAdjunctionModel.kpair M leftSet code) right) →
      (M.mem (FirstOrderAdjunctionModel.kpair M rightSet code) left ∨
        M.mem (FirstOrderAdjunctionModel.kpair M rightSet code) right) →
          leftSet = rightSet)

/-- The union of two compatible certified representation graphs is again a
certified representation graph.  Finite-generation induction is used only to
obtain the binary union object; the certificate argument below is algebraic. -/
theorem ModelSetOrdinalRepCertificate_binUnion
    {α : Type u} (M : FirstOrderFiniteAdjunctionModel α)
    {e : Nat → α} {left right union : α}
    (hleft : ModelSetOrdinalRepCertificate
      M.toFirstOrderAdjunctionModel e left)
    (hright : ModelSetOrdinalRepCertificate
      M.toFirstOrderAdjunctionModel e right)
    (hcompat : ModelSetOrdinalRepRelationsCompatible
      M.toFirstOrderAdjunctionModel left right)
    (hunion : ∀ p, M.mem p union ↔ M.mem p left ∨ M.mem p right) :
    ModelSetOrdinalRepCertificate
      M.toFirstOrderAdjunctionModel e union := by
  let N := M.toFirstOrderAdjunctionModel
  refine ⟨?_, ?_⟩
  · intro set code code' hcode hcode'
    rcases (hunion _).mp hcode with hcodeLeft | hcodeRight <;>
      rcases (hunion _).mp hcode' with hcodeLeft' | hcodeRight'
    · exact hleft.1 set code code' hcodeLeft hcodeLeft'
    · exact hcompat.1 hcodeLeft hcodeRight'
    · exact (hcompat.1 hcodeLeft' hcodeRight).symm
    · exact hright.1 set code code' hcodeRight hcodeRight'
  · intro set code hroot
    rcases (hunion _).mp hroot with hrootLeft | hrootRight
    · have hlocal := hleft.2 set code hrootLeft
      refine ⟨hlocal.1, ?_, ?_⟩
      · intro elem
        constructor
        · intro helem
          rcases (hlocal.2.1 elem).mp helem with
            ⟨elemCode, hpair, hcoded⟩
          exact ⟨elemCode, (hunion _).mpr (Or.inl hpair), hcoded⟩
        · rintro ⟨elemCode, hpair, hcoded⟩
          rcases (hunion _).mp hpair with hpairLeft | hpairRight
          · exact (hlocal.2.1 elem).mpr ⟨elemCode, hpairLeft, hcoded⟩
          · have helemOrd : OrdinalLike M.mem elemCode :=
              (hright.2 elem elemCode hpairRight).1
            have hcodedModel : ModelCompositeMem N elemCode code := by
              have hspec := HF_compositeMemAt_02_model N
                (scons elemCode (scons elem (scons code (scons set e))))
              exact hspec.mp hcoded
            have hcodedLocal : Sat N.mem
                (scons elemCode (scons code (scons set e)))
                (HF_compositeMemAt 0 1) := by
              apply (HF_compositeMemAt_01_model N
                (scons elemCode (scons code (scons set e)))).mpr
              simpa [scons] using hcodedModel
            rcases hlocal.2.2 elemCode helemOrd hcodedLocal with
              ⟨leftElem, hleftPair⟩
            have heq : leftElem = elem :=
              hcompat.2 (Or.inl hleftPair) (Or.inr hpairRight)
            subst leftElem
            exact (hlocal.2.1 elem).mpr
              ⟨elemCode, hleftPair, hcoded⟩
      · intro elemCode helemOrd hcoded
        rcases hlocal.2.2 elemCode helemOrd hcoded with ⟨elem, hpair⟩
        exact ⟨elem, (hunion _).mpr (Or.inl hpair)⟩
    · have hlocal := hright.2 set code hrootRight
      refine ⟨hlocal.1, ?_, ?_⟩
      · intro elem
        constructor
        · intro helem
          rcases (hlocal.2.1 elem).mp helem with
            ⟨elemCode, hpair, hcoded⟩
          exact ⟨elemCode, (hunion _).mpr (Or.inr hpair), hcoded⟩
        · rintro ⟨elemCode, hpair, hcoded⟩
          rcases (hunion _).mp hpair with hpairLeft | hpairRight
          · have helemOrd : OrdinalLike M.mem elemCode :=
              (hleft.2 elem elemCode hpairLeft).1
            have hcodedModel : ModelCompositeMem N elemCode code := by
              have hspec := HF_compositeMemAt_02_model N
                (scons elemCode (scons elem (scons code (scons set e))))
              exact hspec.mp hcoded
            have hcodedLocal : Sat N.mem
                (scons elemCode (scons code (scons set e)))
                (HF_compositeMemAt 0 1) := by
              apply (HF_compositeMemAt_01_model N
                (scons elemCode (scons code (scons set e)))).mpr
              simpa [scons] using hcodedModel
            rcases hlocal.2.2 elemCode helemOrd hcodedLocal with
              ⟨rightElem, hrightPair⟩
            have heq : elem = rightElem :=
              hcompat.2 (Or.inl hpairLeft) (Or.inr hrightPair)
            subst rightElem
            exact (hlocal.2.1 elem).mpr
              ⟨elemCode, hrightPair, hcoded⟩
          · exact (hlocal.2.1 elem).mpr ⟨elemCode, hpairRight, hcoded⟩
      · intro elemCode helemOrd hcoded
        rcases hlocal.2.2 elemCode helemOrd hcoded with ⟨elem, hpair⟩
        exact ⟨elem, (hunion _).mpr (Or.inr hpair)⟩

/-- Two compatible representation witnesses admit exactly the common graph
required by `ModelSetOrdinalRepMergeResult`. -/
theorem ModelSetOrdinalRepMergeResult_of_compatible
    {α : Type u} (M : FirstOrderFiniteAdjunctionModel α)
    (rootEnv : Nat → α) (old oldCode elem elemCode : α)
    (hold : ModelSetOrdinalRep M.toFirstOrderAdjunctionModel
      rootEnv old oldCode)
    (helem : ModelSetOrdinalRep M.toFirstOrderAdjunctionModel
      rootEnv elem elemCode)
    (hcompat : ∀ {left right},
      ModelSetOrdinalRepCertificate M.toFirstOrderAdjunctionModel
        (scons left rootEnv) left →
      ModelSetOrdinalRepCertificate M.toFirstOrderAdjunctionModel
        (scons right rootEnv) right →
      ModelSetOrdinalRepRelationsCompatible
        M.toFirstOrderAdjunctionModel left right) :
    Nonempty (ModelSetOrdinalRepMergeResult
      M.toFirstOrderAdjunctionModel rootEnv old oldCode elem elemCode) := by
  rcases hold with ⟨left, holdRoot, hleft⟩
  rcases helem with ⟨right, helemRoot, hright⟩
  rcases M.binUnion_exists left right with ⟨union, hunion⟩
  let N := M.toFirstOrderAdjunctionModel
  have hcompat' := hcompat hleft hright
  have hleft' : ModelSetOrdinalRepCertificate N
      (scons union rootEnv) left :=
    ModelSetOrdinalRepCertificate_changeEnv N hleft
  have hright' : ModelSetOrdinalRepCertificate N
      (scons union rootEnv) right :=
    ModelSetOrdinalRepCertificate_changeEnv N hright
  have hcertificate : ModelSetOrdinalRepCertificate N
      (scons union rootEnv) union :=
    ModelSetOrdinalRepCertificate_binUnion M
      hleft' hright' hcompat' hunion
  exact ⟨{
    relation := union
    certificate := hcertificate
    code_injective := by
      intro set₁ set₂ code hset₁ hset₂
      exact hcompat'.2 ((hunion _).mp hset₁) ((hunion _).mp hset₂)
    old_root := (hunion _).mpr (Or.inl holdRoot)
    elem_root := (hunion _).mpr (Or.inr helemRoot)
  }⟩

/-- Uniform cross-certificate compatibility.  This is the exact semantic
uniqueness property left after the finite union construction is factored out. -/
def ModelSetOrdinalRepRelationsCompatibilityLaw
    {α : Type u} (M : FirstOrderAdjunctionModel α) : Prop :=
  ∀ {leftEnv rightEnv : Nat → α} {left right : α},
    ModelSetOrdinalRepCertificate M leftEnv left →
    ModelSetOrdinalRepCertificate M rightEnv right →
      ModelSetOrdinalRepRelationsCompatible M left right

/-- In a finite adjunction model, uniform compatibility closes the published
merge law.  No arithmetic or representation-specific premise remains in the
construction itself. -/
theorem ModelSetOrdinalRepMergeLaw_of_finite_compatibility
    {α : Type u} (M : FirstOrderFiniteAdjunctionModel α)
    (hcompat : ModelSetOrdinalRepRelationsCompatibilityLaw
      M.toFirstOrderAdjunctionModel) :
    ModelSetOrdinalRepMergeLaw M.toFirstOrderAdjunctionModel := by
  intro rootEnv old oldCode elem elemCode hold helem
  apply ModelSetOrdinalRepMergeResult_of_compatible M
    rootEnv old oldCode elem elemCode hold helem
  intro left right hleft hright
  exact hcompat hleft hright

/-- The published merge law already contains code functionality; taking the
two inputs to represent the same set forces their codes to agree. -/
theorem ModelSetOrdinalRep_code_eq_of_mergeLaw
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (hmerge : ModelSetOrdinalRepMergeLaw M)
    {rootEnv : Nat → α} {set code₁ code₂ : α}
    (h₁ : ModelSetOrdinalRep M rootEnv set code₁)
    (h₂ : ModelSetOrdinalRep M rootEnv set code₂) :
    code₁ = code₂ := by
  rcases hmerge rootEnv set code₁ set code₂ h₁ h₂ with ⟨R⟩
  exact R.certificate.1 set code₁ code₂ R.old_root R.elem_root

/-- The published merge law also contains set injectivity; taking the two
inputs to use the same code forces their represented sets to agree. -/
theorem ModelSetOrdinalRep_set_eq_of_mergeLaw
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (hmerge : ModelSetOrdinalRepMergeLaw M)
    {rootEnv : Nat → α} {set₁ set₂ code : α}
    (h₁ : ModelSetOrdinalRep M rootEnv set₁ code)
    (h₂ : ModelSetOrdinalRep M rootEnv set₂ code) :
    set₁ = set₂ := by
  rcases hmerge rootEnv set₁ code set₂ code h₁ h₂ with ⟨R⟩
  exact R.code_injective R.old_root R.elem_root

/-- Global functionality of the semantic representation relation. -/
def ModelSetOrdinalRepCodeFunctionalLaw
    {α : Type u} (M : FirstOrderAdjunctionModel α) : Prop :=
  ∀ (rootEnv : Nat → α) (set code₁ code₂ : α),
    ModelSetOrdinalRep M rootEnv set code₁ →
    ModelSetOrdinalRep M rootEnv set code₂ →
      code₁ = code₂

/-- Global injectivity of the semantic representation relation. -/
def ModelSetOrdinalRepSetInjectiveLaw
    {α : Type u} (M : FirstOrderAdjunctionModel α) : Prop :=
  ∀ (rootEnv : Nat → α) (set₁ set₂ code : α),
    ModelSetOrdinalRep M rootEnv set₁ code →
    ModelSetOrdinalRep M rootEnv set₂ code →
      set₁ = set₂

/-- The two global uniqueness laws imply compatibility of every pair of
certified graphs. -/
theorem ModelSetOrdinalRepRelationsCompatibilityLaw_of_uniqueness
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (hfunctional : ModelSetOrdinalRepCodeFunctionalLaw M)
    (hinjective : ModelSetOrdinalRepSetInjectiveLaw M) :
    ModelSetOrdinalRepRelationsCompatibilityLaw M := by
  intro leftEnv rightEnv left right hleft hright
  let rootEnv : Nat → α := fun _ => M.empty
  have leftRep : ∀ {set code},
      M.mem (FirstOrderAdjunctionModel.kpair M set code) left →
        ModelSetOrdinalRep M rootEnv set code := by
    intro set code hroot
    exact ⟨left, hroot,
      ModelSetOrdinalRepCertificate_changeEnv M hleft⟩
  have rightRep : ∀ {set code},
      M.mem (FirstOrderAdjunctionModel.kpair M set code) right →
        ModelSetOrdinalRep M rootEnv set code := by
    intro set code hroot
    exact ⟨right, hroot,
      ModelSetOrdinalRepCertificate_changeEnv M hright⟩
  refine ⟨?_, ?_⟩
  · intro set leftCode rightCode hleftRoot hrightRoot
    exact hfunctional rootEnv set leftCode rightCode
      (leftRep hleftRoot) (rightRep hrightRoot)
  · intro leftSet rightSet code hleftSet hrightSet
    rcases hleftSet with hleftRoot | hrightRoot <;>
      rcases hrightSet with hleftRoot' | hrightRoot'
    · exact hinjective rootEnv leftSet rightSet code
        (leftRep hleftRoot) (leftRep hleftRoot')
    · exact hinjective rootEnv leftSet rightSet code
        (leftRep hleftRoot) (rightRep hrightRoot')
    · exact hinjective rootEnv leftSet rightSet code
        (rightRep hrightRoot) (leftRep hleftRoot')
    · exact hinjective rootEnv leftSet rightSet code
        (rightRep hrightRoot) (rightRep hrightRoot')

/-- In a finite adjunction model, the published merge law contains exactly the
two global uniqueness directions and no additional representation content. -/
theorem ModelSetOrdinalRepMergeLaw_iff_uniqueness
    {α : Type u} (M : FirstOrderFiniteAdjunctionModel α) :
    ModelSetOrdinalRepMergeLaw M.toFirstOrderAdjunctionModel ↔
      ModelSetOrdinalRepCodeFunctionalLaw
          M.toFirstOrderAdjunctionModel ∧
        ModelSetOrdinalRepSetInjectiveLaw
          M.toFirstOrderAdjunctionModel := by
  let N := M.toFirstOrderAdjunctionModel
  constructor
  · intro hmerge
    constructor
    · intro rootEnv set code₁ code₂ h₁ h₂
      exact ModelSetOrdinalRep_code_eq_of_mergeLaw N
        hmerge h₁ h₂
    · intro rootEnv set₁ set₂ code h₁ h₂
      exact ModelSetOrdinalRep_set_eq_of_mergeLaw N
        hmerge h₁ h₂
  · rintro ⟨hfunctional, hinjective⟩
    apply ModelSetOrdinalRepMergeLaw_of_finite_compatibility M
    exact ModelSetOrdinalRepRelationsCompatibilityLaw_of_uniqueness N
      hfunctional hinjective

/-! ## Deriving set injectivity from certificate recursion -/

/-- Set injectivity needs no arithmetic property of Ackermann membership.
First-order HF induction on the left represented set recursively identifies
the two elements carrying each common child code. -/
theorem ModelSetOrdinalRepSetInjectiveLaw_of_induction
    {α : Type u} (M : FirstOrderAdjunctionModel α) :
    ModelSetOrdinalRepSetInjectiveLaw M := by
  let phi : Form :=
    fAll (fAll
      (fImp (HF_setOrdinalRepAt 2 0)
        (fImp (HF_setOrdinalRepAt 1 0) (fEq 2 1))))
  let tail : Nat → α := mergeCanonicalRepEnv M
  have hind := M.induction_schema phi tail
  have hall : ∀ set₁, Sat M.mem (scons set₁ tail) phi := by
    apply hind
    intro set₁ ih set₂ code hrep₁Sat hrep₂Sat
    let E : Nat → α := scons code (scons set₂ (scons set₁ tail))
    have hrep₁ : ModelSetOrdinalRep M E set₁ code := by
      apply (HF_setOrdinalRepAt_model M E 2 0).mp
      simpa [E, scons] using hrep₁Sat
    have hrep₂ : ModelSetOrdinalRep M E set₂ code := by
      apply (HF_setOrdinalRepAt_model M E 1 0).mp
      simpa [E, scons] using hrep₂Sat
    rcases hrep₁ with ⟨relation₁, hroot₁, hcert₁⟩
    rcases hrep₂ with ⟨relation₂, hroot₂, hcert₂⟩
    have hlocal₁ := hcert₁.2 set₁ code hroot₁
    have hlocal₂ := hcert₂.2 set₂ code hroot₂
    apply M.extensional
    intro member
    constructor
    · intro hmember₁
      rcases (hlocal₁.2.1 member).mp hmember₁ with
        ⟨memberCode, hmemberRoot₁, hcoded₁⟩
      have hmemberCodeOrd : OrdinalLike M.mem memberCode :=
        (hcert₁.2 member memberCode hmemberRoot₁).1
      have hcodedModel : ModelCompositeMem M memberCode code := by
        have hspec := HF_compositeMemAt_02_model M
          (scons memberCode
            (scons member (scons code (scons set₁ (scons relation₁ E)))))
        exact hspec.mp hcoded₁
      have hcoded₂Complete : Sat M.mem
          (scons memberCode (scons code (scons set₂ (scons relation₂ E))))
          (HF_compositeMemAt 0 1) := by
        apply (HF_compositeMemAt_01_model M
          (scons memberCode
            (scons code (scons set₂ (scons relation₂ E))))).mpr
        simpa [scons] using hcodedModel
      rcases hlocal₂.2.2 memberCode hmemberCodeOrd hcoded₂Complete with
        ⟨other, hotherRoot₂⟩
      have hcoded₂Member : Sat M.mem
          (scons memberCode
            (scons other (scons code (scons set₂ (scons relation₂ E)))))
          (HF_compositeMemAt 0 2) := by
        apply (HF_compositeMemAt_02_model M
          (scons memberCode
            (scons other (scons code (scons set₂ (scons relation₂ E)))))).mpr
        simpa [scons] using hcodedModel
      have hother₂ : M.mem other set₂ :=
        (hlocal₂.2.1 other).mpr
          ⟨memberCode, hotherRoot₂, hcoded₂Member⟩
      have hmemberIH : Sat M.mem (scons member tail) phi :=
        (Sat_rename_rSkipParam phi tail set₁ member).mp
          (ih member hmember₁)
      let EI : Nat → α :=
        scons memberCode (scons other (scons member tail))
      have hmemberRep : ModelSetOrdinalRep M EI member memberCode :=
        mergeModelSetOrdinalRep_changeEnv M
          ⟨relation₁, hmemberRoot₁, hcert₁⟩
      have hotherRep : ModelSetOrdinalRep M EI other memberCode :=
        mergeModelSetOrdinalRep_changeEnv M
          ⟨relation₂, hotherRoot₂, hcert₂⟩
      have hmemberRepSat : Sat M.mem EI (HF_setOrdinalRepAt 2 0) :=
        (HF_setOrdinalRepAt_model M EI 2 0).mpr (by
          simpa [EI, scons] using hmemberRep)
      have hotherRepSat : Sat M.mem EI (HF_setOrdinalRepAt 1 0) :=
        (HF_setOrdinalRepAt_model M EI 1 0).mpr (by
          simpa [EI, scons] using hotherRep)
      have heq : member = other := by
        exact hmemberIH other memberCode
          (by simpa [EI] using hmemberRepSat)
          (by simpa [EI] using hotherRepSat)
      simpa [E, scons, ← heq] using hother₂
    · intro hmember₂
      rcases (hlocal₂.2.1 member).mp hmember₂ with
        ⟨memberCode, hmemberRoot₂, hcoded₂⟩
      have hmemberCodeOrd : OrdinalLike M.mem memberCode :=
        (hcert₂.2 member memberCode hmemberRoot₂).1
      have hcodedModel : ModelCompositeMem M memberCode code := by
        have hspec := HF_compositeMemAt_02_model M
          (scons memberCode
            (scons member (scons code (scons set₂ (scons relation₂ E)))))
        exact hspec.mp hcoded₂
      have hcoded₁Complete : Sat M.mem
          (scons memberCode (scons code (scons set₁ (scons relation₁ E))))
          (HF_compositeMemAt 0 1) := by
        apply (HF_compositeMemAt_01_model M
          (scons memberCode
            (scons code (scons set₁ (scons relation₁ E))))).mpr
        simpa [scons] using hcodedModel
      rcases hlocal₁.2.2 memberCode hmemberCodeOrd hcoded₁Complete with
        ⟨other, hotherRoot₁⟩
      have hcoded₁Member : Sat M.mem
          (scons memberCode
            (scons other (scons code (scons set₁ (scons relation₁ E)))))
          (HF_compositeMemAt 0 2) := by
        apply (HF_compositeMemAt_02_model M
          (scons memberCode
            (scons other (scons code (scons set₁ (scons relation₁ E)))))).mpr
        simpa [scons] using hcodedModel
      have hother₁ : M.mem other set₁ :=
        (hlocal₁.2.1 other).mpr
          ⟨memberCode, hotherRoot₁, hcoded₁Member⟩
      have hotherIH : Sat M.mem (scons other tail) phi :=
        (Sat_rename_rSkipParam phi tail set₁ other).mp
          (ih other hother₁)
      let EI : Nat → α :=
        scons memberCode (scons member (scons other tail))
      have hotherRep : ModelSetOrdinalRep M EI other memberCode :=
        mergeModelSetOrdinalRep_changeEnv M
          ⟨relation₁, hotherRoot₁, hcert₁⟩
      have hmemberRep : ModelSetOrdinalRep M EI member memberCode :=
        mergeModelSetOrdinalRep_changeEnv M
          ⟨relation₂, hmemberRoot₂, hcert₂⟩
      have hotherRepSat : Sat M.mem EI (HF_setOrdinalRepAt 2 0) :=
        (HF_setOrdinalRepAt_model M EI 2 0).mpr (by
          simpa [EI, scons] using hotherRep)
      have hmemberRepSat : Sat M.mem EI (HF_setOrdinalRepAt 1 0) :=
        (HF_setOrdinalRepAt_model M EI 1 0).mpr (by
          simpa [EI, scons] using hmemberRep)
      have heq : other = member := by
        exact hotherIH member memberCode
          (by simpa [EI] using hotherRepSat)
          (by simpa [EI] using hmemberRepSat)
      simpa [E, scons, heq] using hother₁
  intro rootEnv set₁ set₂ code hrep₁ hrep₂
  have hmain : Sat M.mem (scons set₁ tail) phi := hall set₁
  let E : Nat → α := scons code (scons set₂ (scons set₁ tail))
  have hrep₁' : ModelSetOrdinalRep M E set₁ code :=
    mergeModelSetOrdinalRep_changeEnv M hrep₁
  have hrep₂' : ModelSetOrdinalRep M E set₂ code :=
    mergeModelSetOrdinalRep_changeEnv M hrep₂
  have hrep₁Sat : Sat M.mem E (HF_setOrdinalRepAt 2 0) :=
    (HF_setOrdinalRepAt_model M E 2 0).mpr (by
      simpa [E, scons] using hrep₁')
  have hrep₂Sat : Sat M.mem E (HF_setOrdinalRepAt 1 0) :=
    (HF_setOrdinalRepAt_model M E 1 0).mpr (by
      simpa [E, scons] using hrep₂')
  exact hmain set₂ code
    (by simpa [E] using hrep₁Sat)
    (by simpa [E] using hrep₂Sat)

/-! ## Deriving code functionality from Ackermann extensionality -/

/-- Arithmetic extensionality of the translated Ackermann-membership
relation, restricted to its ordinal domain. -/
def ModelCompositeMemExtensionalLaw
    {α : Type u} (M : FirstOrderAdjunctionModel α) : Prop :=
  ∀ left right,
    OrdinalLike M.mem left →
    OrdinalLike M.mem right →
    (∀ query, OrdinalLike M.mem query →
      (ModelCompositeMem M query left ↔
        ModelCompositeMem M query right)) →
      left = right

/-- Assuming arithmetic extensionality of Ackermann codes, first-order HF
induction on the represented set makes its ordinal representation functional. -/
theorem ModelSetOrdinalRepCodeFunctionalLaw_of_composite_extensionality
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (hext : ModelCompositeMemExtensionalLaw M) :
    ModelSetOrdinalRepCodeFunctionalLaw M := by
  let phi : Form :=
    fAll (fAll
      (fImp (HF_setOrdinalRepAt 2 1)
        (fImp (HF_setOrdinalRepAt 2 0) (fEq 1 0))))
  let tail : Nat → α := mergeCanonicalRepEnv M
  have hind := M.induction_schema phi tail
  have hall : ∀ set, Sat M.mem (scons set tail) phi := by
    apply hind
    intro set ih code₁ code₂ hrep₁Sat hrep₂Sat
    let E : Nat → α := scons code₂ (scons code₁ (scons set tail))
    have hrep₁ : ModelSetOrdinalRep M E set code₁ := by
      apply (HF_setOrdinalRepAt_model M E 2 1).mp
      simpa [E, scons] using hrep₁Sat
    have hrep₂ : ModelSetOrdinalRep M E set code₂ := by
      apply (HF_setOrdinalRepAt_model M E 2 0).mp
      simpa [E, scons] using hrep₂Sat
    rcases hrep₁ with ⟨relation₁, hroot₁, hcert₁⟩
    rcases hrep₂ with ⟨relation₂, hroot₂, hcert₂⟩
    have hlocal₁ := hcert₁.2 set code₁ hroot₁
    have hlocal₂ := hcert₂.2 set code₂ hroot₂
    apply hext code₁ code₂ hlocal₁.1 hlocal₂.1
    intro query hqueryOrd
    constructor
    · intro hcoded₁Model
      have hcoded₁Complete : Sat M.mem
          (scons query (scons code₁ (scons set (scons relation₁ E))))
          (HF_compositeMemAt 0 1) := by
        apply (HF_compositeMemAt_01_model M
          (scons query
            (scons code₁ (scons set (scons relation₁ E))))).mpr
        simpa [scons] using hcoded₁Model
      rcases hlocal₁.2.2 query hqueryOrd hcoded₁Complete with
        ⟨member, hmemberRoot₁⟩
      have hcoded₁Member : Sat M.mem
          (scons query
            (scons member
              (scons code₁ (scons set (scons relation₁ E)))))
          (HF_compositeMemAt 0 2) := by
        apply (HF_compositeMemAt_02_model M
          (scons query
            (scons member
              (scons code₁ (scons set (scons relation₁ E)))))).mpr
        simpa [scons] using hcoded₁Model
      have hmember : M.mem member set :=
        (hlocal₁.2.1 member).mpr
          ⟨query, hmemberRoot₁, hcoded₁Member⟩
      rcases (hlocal₂.2.1 member).mp hmember with
        ⟨otherCode, hmemberRoot₂, hcoded₂⟩
      have hcoded₂Model : ModelCompositeMem M otherCode code₂ := by
        have hspec := HF_compositeMemAt_02_model M
          (scons otherCode
            (scons member
              (scons code₂ (scons set (scons relation₂ E)))))
        exact hspec.mp hcoded₂
      have hmemberIH : Sat M.mem (scons member tail) phi :=
        (Sat_rename_rSkipParam phi tail set member).mp
          (ih member hmember)
      let EI : Nat → α :=
        scons otherCode (scons query (scons member tail))
      have hqueryRep : ModelSetOrdinalRep M EI member query :=
        mergeModelSetOrdinalRep_changeEnv M
          ⟨relation₁, hmemberRoot₁, hcert₁⟩
      have hotherRep : ModelSetOrdinalRep M EI member otherCode :=
        mergeModelSetOrdinalRep_changeEnv M
          ⟨relation₂, hmemberRoot₂, hcert₂⟩
      have hqueryRepSat : Sat M.mem EI (HF_setOrdinalRepAt 2 1) :=
        (HF_setOrdinalRepAt_model M EI 2 1).mpr (by
          simpa [EI, scons] using hqueryRep)
      have hotherRepSat : Sat M.mem EI (HF_setOrdinalRepAt 2 0) :=
        (HF_setOrdinalRepAt_model M EI 2 0).mpr (by
          simpa [EI, scons] using hotherRep)
      have heq : query = otherCode :=
        hmemberIH query otherCode
          (by simpa [EI] using hqueryRepSat)
          (by simpa [EI] using hotherRepSat)
      simpa [heq] using hcoded₂Model
    · intro hcoded₂Model
      have hcoded₂Complete : Sat M.mem
          (scons query (scons code₂ (scons set (scons relation₂ E))))
          (HF_compositeMemAt 0 1) := by
        apply (HF_compositeMemAt_01_model M
          (scons query
            (scons code₂ (scons set (scons relation₂ E))))).mpr
        simpa [scons] using hcoded₂Model
      rcases hlocal₂.2.2 query hqueryOrd hcoded₂Complete with
        ⟨member, hmemberRoot₂⟩
      have hcoded₂Member : Sat M.mem
          (scons query
            (scons member
              (scons code₂ (scons set (scons relation₂ E)))))
          (HF_compositeMemAt 0 2) := by
        apply (HF_compositeMemAt_02_model M
          (scons query
            (scons member
              (scons code₂ (scons set (scons relation₂ E)))))).mpr
        simpa [scons] using hcoded₂Model
      have hmember : M.mem member set :=
        (hlocal₂.2.1 member).mpr
          ⟨query, hmemberRoot₂, hcoded₂Member⟩
      rcases (hlocal₁.2.1 member).mp hmember with
        ⟨otherCode, hmemberRoot₁, hcoded₁⟩
      have hcoded₁Model : ModelCompositeMem M otherCode code₁ := by
        have hspec := HF_compositeMemAt_02_model M
          (scons otherCode
            (scons member
              (scons code₁ (scons set (scons relation₁ E)))))
        exact hspec.mp hcoded₁
      have hmemberIH : Sat M.mem (scons member tail) phi :=
        (Sat_rename_rSkipParam phi tail set member).mp
          (ih member hmember)
      let EI : Nat → α :=
        scons query (scons otherCode (scons member tail))
      have hotherRep : ModelSetOrdinalRep M EI member otherCode :=
        mergeModelSetOrdinalRep_changeEnv M
          ⟨relation₁, hmemberRoot₁, hcert₁⟩
      have hqueryRep : ModelSetOrdinalRep M EI member query :=
        mergeModelSetOrdinalRep_changeEnv M
          ⟨relation₂, hmemberRoot₂, hcert₂⟩
      have hotherRepSat : Sat M.mem EI (HF_setOrdinalRepAt 2 1) :=
        (HF_setOrdinalRepAt_model M EI 2 1).mpr (by
          simpa [EI, scons] using hotherRep)
      have hqueryRepSat : Sat M.mem EI (HF_setOrdinalRepAt 2 0) :=
        (HF_setOrdinalRepAt_model M EI 2 0).mpr (by
          simpa [EI, scons] using hqueryRep)
      have heq : otherCode = query :=
        hmemberIH otherCode query
          (by simpa [EI] using hotherRepSat)
          (by simpa [EI] using hqueryRepSat)
      simpa [heq] using hcoded₁Model
  intro rootEnv set code₁ code₂ hrep₁ hrep₂
  have hmain : Sat M.mem (scons set tail) phi := hall set
  let E : Nat → α := scons code₂ (scons code₁ (scons set tail))
  have hrep₁' : ModelSetOrdinalRep M E set code₁ :=
    mergeModelSetOrdinalRep_changeEnv M hrep₁
  have hrep₂' : ModelSetOrdinalRep M E set code₂ :=
    mergeModelSetOrdinalRep_changeEnv M hrep₂
  have hrep₁Sat : Sat M.mem E (HF_setOrdinalRepAt 2 1) :=
    (HF_setOrdinalRepAt_model M E 2 1).mpr (by
      simpa [E, scons] using hrep₁')
  have hrep₂Sat : Sat M.mem E (HF_setOrdinalRepAt 2 0) :=
    (HF_setOrdinalRepAt_model M E 2 0).mpr (by
      simpa [E, scons] using hrep₂')
  exact hmain code₁ code₂
    (by simpa [E] using hrep₁Sat)
    (by simpa [E] using hrep₂Sat)

/-- Composite-membership extensionality is the only remaining input needed
for the exact finite-model merge law. -/
theorem ModelSetOrdinalRepMergeLaw_of_composite_extensionality
    {α : Type u} (M : FirstOrderFiniteAdjunctionModel α)
    (hext : ModelCompositeMemExtensionalLaw
      M.toFirstOrderAdjunctionModel) :
    ModelSetOrdinalRepMergeLaw M.toFirstOrderAdjunctionModel := by
  apply (ModelSetOrdinalRepMergeLaw_iff_uniqueness M).mpr
  exact ⟨
    ModelSetOrdinalRepCodeFunctionalLaw_of_composite_extensionality
      M.toFirstOrderAdjunctionModel hext,
    ModelSetOrdinalRepSetInjectiveLaw_of_induction
      M.toFirstOrderAdjunctionModel⟩

/-! ## Semantic finite-HF model and translated Ackermann extensionality -/

/-- A bundled finite adjunction model satisfies every sealed finite-HF axiom. -/
theorem FirstOrderFiniteAdjunctionModel_sat_HFFin
    {α : Type u} (M : FirstOrderFiniteAdjunctionModel α) (v : Nat → α) :
    ∀ g, HFFinAx_s g → Sat M.mem v g := by
  intro g hg
  rcases hg with hg | ⟨phi, rfl⟩
  · rcases hg with rfl | rfl | rfl | ⟨phi, rfl⟩
    · apply (seal_valid (mem := M.mem) HF_empty_form).mpr
      intro e
      exact ⟨M.empty, fun x hx => M.empty_spec x hx⟩
    · apply (seal_valid (mem := M.mem) HF_extensionality_form).mpr
      intro e left right hsame
      apply M.extensional
      intro x
      exact (Sat_fIff (mem := M.mem)
        (e := scons x (scons right (scons left e)))).mp (hsame x)
    · apply (seal_valid (mem := M.mem) HF_adjoin_form).mpr
      intro e left elem
      refine ⟨M.adjoin left elem, fun x => ?_⟩
      apply (Sat_fIff (mem := M.mem)
        (e := scons x
          (scons (M.adjoin left elem) (scons elem (scons left e))))).mpr
      exact M.adjoin_spec x left elem
    · exact (seal_valid (mem := M.mem) (HF_induction_form phi)).mpr
        (fun e => M.induction_schema phi e) v
  · exact (seal_valid (mem := M.mem) (HF_finite_induction_form phi)).mpr
      (fun e => M.finite_induction_schema phi e) v

/-- Relative PA extensionality in the exact one-assumption form needed by the
semantic translation below. -/
theorem PA_BProv_hfMembership_extensional :
    PA.Formula.BProv PA.Formula.Ax_s
      [PA.Formula.all
        (PA.Formula.iffForm
          (PA.Formula.hfMemAt 0 2)
          (PA.Formula.hfMemAt 0 1))]
      (PA.Formula.eq (PA.Term.var 1) (PA.Term.var 0)) := by
  let sameMembers : PA.Formula :=
    PA.Formula.all
      (PA.Formula.iffForm
        (PA.Formula.hfMemAt 0 2)
        (PA.Formula.hfMemAt 0 1))
  have hsame : PA.Formula.BProv PA.Formula.Ax_s [sameMembers] sameMembers :=
    PA.Formula.BProv_ass (by simp)
  apply PA.Formula.BProv_Ax_s_eq_of_hfSameMembersTermAt
    (left := PA.Term.var 1) (right := PA.Term.var 0)
  simpa [sameMembers, PA.Formula.hfMemTermAt_var,
    PA.Term.rename] using hsame

/-- Translated PA extensionality makes `ModelCompositeMem` extensional on the
ordinal domain of every finite first-order HF model. -/
theorem ModelCompositeMemExtensionalLaw_finite
    {α : Type u} (M : FirstOrderFiniteAdjunctionModel α) :
    ModelCompositeMemExtensionalLaw
      M.toFirstOrderAdjunctionModel := by
  let N := M.toFirstOrderAdjunctionModel
  let sameMembers : PA.Formula :=
    PA.Formula.all
      (PA.Formula.iffForm
        (PA.Formula.hfMemAt 0 2)
        (PA.Formula.hfMemAt 0 1))
  rcases PAInHF.BProv_HFFin_formulaAt_of_PA_BProv_domainContext
      PA_BProv_hfMembership_extensional with
    ⟨n, htranslated⟩
  intro left right hleft hright hsame
  let env : Nat → α :=
    scons right (scons left (fun _ => M.empty))
  let ρ : Nat → Nat := fun k => k
  have hord : ∀ k, k < n → OrdinalLike M.mem (env (ρ k)) := by
    intro k _hk
    cases k with
    | zero => simpa [env, ρ, scons] using hright
    | succ k =>
        cases k with
        | zero => simpa [env, ρ, scons] using hleft
        | succ k =>
            simpa [env, ρ, scons] using
              (FirstOrderAdjunctionModel.ordinalLike_empty N)
  have hdomain : ∀ g,
      g ∈ PAInHF.domainContextAt ρ n → Sat M.mem env g :=
    PAInHF.Sat_domainContextAt_of_ordinalLike hord
  have hleftFormula :
      PAInHF.formulaAt (PAInHF.upVarMap ρ) (PA.Formula.hfMemAt 0 2) =
        HF_compositeMemAt 0 2 := by
    have hup : PAInHF.upVarMap ρ = (fun k : Nat => k) := by
      funext k
      cases k <;> rfl
    rw [hup]
    change hfCompositeAt (fun k : Nat => k) (fMem 0 2) =
      HF_compositeMemAt 0 2
    exact hfCompositeAt_mem (fun k : Nat => k) 0 2
  have hrightFormula :
      PAInHF.formulaAt (PAInHF.upVarMap ρ) (PA.Formula.hfMemAt 0 1) =
        HF_compositeMemAt 0 1 := by
    have hup : PAInHF.upVarMap ρ = (fun k : Nat => k) := by
      funext k
      cases k <;> rfl
    rw [hup]
    change hfCompositeAt (fun k : Nat => k) (fMem 0 1) =
      HF_compositeMemAt 0 1
    exact hfCompositeAt_mem (fun k : Nat => k) 0 1
  have hsameSat : Sat M.mem env (PAInHF.formulaAt ρ sameMembers) := by
    intro query hqueryDomain
    have hqueryOrd : OrdinalLike M.mem query :=
      (HF_ordinalLikeAt_spec (scons query env) 0).mp hqueryDomain
    change Sat M.mem (scons query env)
      (fIff
        (PAInHF.formulaAt (PAInHF.upVarMap ρ)
          (PA.Formula.hfMemAt 0 2))
        (PAInHF.formulaAt (PAInHF.upVarMap ρ)
          (PA.Formula.hfMemAt 0 1)))
    rw [Sat_fIff, hleftFormula, hrightFormula]
    constructor
    · intro hqueryLeft
      apply (HF_compositeMemAt_01_model N (scons query env)).mpr
      exact (hsame query hqueryOrd).mp
        ((HF_compositeMemAt_02_model N (scons query env)).mp hqueryLeft)
    · intro hqueryRight
      apply (HF_compositeMemAt_02_model N (scons query env)).mpr
      exact (hsame query hqueryOrd).mpr
        ((HF_compositeMemAt_01_model N (scons query env)).mp hqueryRight)
  have htranslatedSat := soundness_BProv (htranslated ρ) env
    (FirstOrderFiniteAdjunctionModel_sat_HFFin M env) (by
      intro g hg
      simp only [List.mem_append] at hg
      rcases hg with hgDomain | hgContext
      · exact hdomain g hgDomain
      · simp only [PAInHF.translateContextAt, List.map_singleton,
          List.mem_singleton] at hgContext
        subst g
        exact hsameSat)
  have heq : env (ρ 1) = env (ρ 0) :=
    (PAInHF.formulaAt_eq_var_spec ρ 1 0 env).mp htranslatedSat
  simpa [env, ρ, scons] using heq

/-- Every finite first-order adjunction model satisfies the exact published
merge law for set-to-ordinal representation witnesses. -/
theorem ModelSetOrdinalRepMergeLaw_finite
    {α : Type u} (M : FirstOrderFiniteAdjunctionModel α) :
    ModelSetOrdinalRepMergeLaw M.toFirstOrderAdjunctionModel :=
  ModelSetOrdinalRepMergeLaw_of_composite_extensionality M
    (ModelCompositeMemExtensionalLaw_finite M)

/-- Arithmetic/freshness data for extending a common relation by one adjunction
root.  This is separate from `ModelSetOrdinalRepMergeLaw`: the latter merges
graphs, while this package is the PA-in-HF Ackermann-code obligation. -/
structure ModelSetOrdinalRepAdjoinCodeData
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (relation old oldCode elem elemCode newSet newCode : α) : Prop where
  newSet_spec : ∀ x, M.mem x newSet ↔ M.mem x old ∨ x = elem
  newCode_ordinal : OrdinalLike M.mem newCode
  code_adjoin : ∀ query,
    OrdinalLike M.mem query →
      (ModelCompositeMem M query newCode ↔
        ModelCompositeMem M query oldCode ∨ query = elemCode)
  root_compatible : ∀ code,
    M.mem (FirstOrderAdjunctionModel.kpair M newSet code) relation →
      code = newCode
  newCode_not_old_member : ∀ {set code},
    M.mem (FirstOrderAdjunctionModel.kpair M set code) relation →
      ¬ ModelCompositeMem M newCode code
  newCode_irrefl : ¬ ModelCompositeMem M newCode newCode

/-- Once the merge result and PA-side code data are supplied, the new root
representation follows with no further hidden obligation. -/
theorem ModelSetOrdinalRep_adjoin_of_merge
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (rootEnv : Nat → α)
    {old oldCode elem elemCode newSet newCode : α}
    (R : ModelSetOrdinalRepMergeResult M rootEnv
      old oldCode elem elemCode)
    (C : ModelSetOrdinalRepAdjoinCodeData M R.relation
      old oldCode elem elemCode newSet newCode) :
    ModelSetOrdinalRep M rootEnv newSet newCode := by
  let extended := adjoinSetOrdinalRepGraph M
    R.relation newSet newCode
  have hcert : ModelSetOrdinalRepCertificate M
      (scons extended rootEnv) R.relation :=
    ModelSetOrdinalRepCertificate_changeEnv M R.certificate
  let D : ModelSetOrdinalRepAdjoinData M
      (scons extended rootEnv) R.relation
      old oldCode elem elemCode newSet newCode := {
    certificate := hcert
    code_injective := R.code_injective
    old_root := R.old_root
    elem_root := R.elem_root
    newSet_spec := C.newSet_spec
    newCode_ordinal := C.newCode_ordinal
    code_adjoin := C.code_adjoin
    root_compatible := C.root_compatible
    newCode_not_old_member := C.newCode_not_old_member
    newCode_irrefl := C.newCode_irrefl
  }
  refine ⟨extended, ?_, ?_⟩
  · exact adjoinSetOrdinalRepGraph_new M
      R.relation newSet newCode
  · exact ModelSetOrdinalRepCertificate_adjoin M
      (scons extended rootEnv) D

theorem ModelSetOrdinalRep_changeEnv
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    {e e' : Nat → α} {set code : α}
    (h : ModelSetOrdinalRep M e set code) :
    ModelSetOrdinalRep M e' set code := by
  rcases h with ⟨relation, hroot, hcert⟩
  exact ⟨relation, hroot,
    ModelSetOrdinalRepCertificate_changeEnv M hcert⟩

def canonicalRepEnv {α : Type u}
    (M : FirstOrderAdjunctionModel α) : Nat → α :=
  fun _ => M.empty

def HasSetOrdinalRep {α : Type u}
    (M : FirstOrderAdjunctionModel α) (set : α) : Prop :=
  ∃ code,
    ModelSetOrdinalRep M (canonicalRepEnv M) set code

/-- The object-language existential representation formula is exactly the
environment-independent semantic existence predicate. -/
theorem setOrdinalRepExists_model
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (env : Nat → α) :
    Sat M.mem env (fEx (HF_setOrdinalRepAt 1 0)) ↔
      HasSetOrdinalRep M (env 0) := by
  constructor
  · intro h
    rcases h with ⟨code, hrepSat⟩
    have hrep := (HF_setOrdinalRepAt_model M
      (scons code env) 1 0).mp hrepSat
    refine ⟨code, ?_⟩
    apply ModelSetOrdinalRep_changeEnv M hrep
  · intro h
    rcases h with ⟨code, hrep⟩
    refine ⟨code, ?_⟩
    apply (HF_setOrdinalRepAt_model M
      (scons code env) 1 0).mpr
    have hrep' := ModelSetOrdinalRep_changeEnv M
      (e' := scons code env) hrep
    simpa [scons] using hrep'

/-- PA-in-HF code construction boundary once a common certificate relation has
already been chosen. -/
def ModelSetOrdinalRepCodeAdjoinLaw
    {α : Type u} (M : FirstOrderAdjunctionModel α) : Prop :=
  ∀ (old oldCode elem elemCode newSet : α)
    (R : ModelSetOrdinalRepMergeResult M
      (canonicalRepEnv M) old oldCode elem elemCode),
    (∀ x, M.mem x newSet ↔ M.mem x old ∨ x = elem) →
      ∃ newCode,
        ModelSetOrdinalRepAdjoinCodeData M R.relation
          old oldCode elem elemCode newSet newCode

/-- The two isolated boundaries—merging certificate relations and constructing
the PA Ackermann adjunction code—suffice for semantic adjunction closure. -/
theorem HasSetOrdinalRep_adjoin_of_merge_code
    {α : Type u} (M : FirstOrderAdjunctionModel α)
    (hmerge : ModelSetOrdinalRepMergeLaw M)
    (hcode : ModelSetOrdinalRepCodeAdjoinLaw M)
    {old elem newSet : α}
    (hnew : ∀ x, M.mem x newSet ↔ M.mem x old ∨ x = elem)
    (hold : HasSetOrdinalRep M old)
    (helem : HasSetOrdinalRep M elem) :
    HasSetOrdinalRep M newSet := by
  rcases hold with ⟨oldCode, hold⟩
  rcases helem with ⟨elemCode, helem⟩
  rcases hmerge (canonicalRepEnv M)
      old oldCode elem elemCode hold helem with ⟨R⟩
  rcases hcode old oldCode elem elemCode newSet R hnew with
    ⟨newCode, C⟩
  refine ⟨newCode, ?_⟩
  exact ModelSetOrdinalRep_adjoin_of_merge M
    (canonicalRepEnv M) R C

/-! ## Finite-generation closure -/

theorem HF_induction_form_spec
    {α : Type u} {mem : α → α → Prop}
    (phi : Form) (e : Nat → α) :
    Sat mem e (HF_induction_form phi) ↔
      ((∀ set,
          (∀ elem, mem elem set → Sat mem (scons elem e) phi) →
            Sat mem (scons set e) phi) →
        ∀ set, Sat mem (scons set e) phi) := by
  constructor
  · intro h hstep
    apply h
    intro set hmembers
    apply hstep set
    intro elem helem
    exact (Sat_rename_rSkipParam phi e set elem).mp
      (hmembers elem helem)
  · intro h hstep
    apply h
    intro set hmembers
    apply hstep set
    intro elem helem
    exact (Sat_rename_rSkipParam phi e set elem).mpr
      (hmembers elem helem)

/-- Set induction supplies representations of the elements of a target set;
an inner finite-generation induction builds representations of its finite
subsets.  Thus empty and binary-adjunction closure imply totality. -/
theorem HasSetOrdinalRep_total_of_empty_adjoin
    {α : Type u} (M : FirstOrderFiniteAdjunctionModel α)
    (hempty : HasSetOrdinalRep M.toFirstOrderAdjunctionModel M.empty)
    (hadjoin : ∀ {old elem newSet},
      (∀ x, M.mem x newSet ↔ M.mem x old ∨ x = elem) →
      HasSetOrdinalRep M.toFirstOrderAdjunctionModel old →
      HasSetOrdinalRep M.toFirstOrderAdjunctionModel elem →
        HasSetOrdinalRep M.toFirstOrderAdjunctionModel newSet)
    (set : α) :
    HasSetOrdinalRep M.toFirstOrderAdjunctionModel set := by
  let N := M.toFirstOrderAdjunctionModel
  let repForm : Form := fEx (HF_setOrdinalRepAt 1 0)
  let subsetRepForm : Form :=
    fImp (HF_subsetAt 0 1) repForm
  let tail : Nat → α := canonicalRepEnv N
  have houter := M.induction_schema repForm tail
  have hall : ∀ target,
      Sat M.mem (scons target tail) repForm := by
    apply (HF_induction_form_spec repForm tail).mp houter
    intro target hmembers
    let targetEnv : Nat → α := scons target tail
    have hfinite := M.finite_induction_schema subsetRepForm targetEnv
    have hsubsets : ∀ current,
        Sat M.mem (scons current targetEnv) subsetRepForm := by
      apply (HF_finite_induction_form_spec subsetRepForm targetEnv).mp hfinite
      constructor
      · intro emptyLike hemptyLike _hsubset
        have hEmptyEq : emptyLike = M.empty := by
          apply M.extensional
          intro x
          constructor
          · intro hx
            exact False.elim (hemptyLike x hx)
          · intro hx
            exact False.elim (M.empty_spec x hx)
        subst emptyLike
        apply (setOrdinalRepExists_model N
          (scons M.empty targetEnv)).mpr
        exact hempty
      · intro old elem newSet hnew hOld
        intro hsubsetSat
        have hsubset : ∀ x, M.mem x newSet → M.mem x target :=
          (HF_subsetAt_spec (scons newSet targetEnv) 0 1).mp hsubsetSat
        have holdSubset : Sat M.mem (scons old targetEnv)
            (HF_subsetAt 0 1) := by
          apply (HF_subsetAt_spec (scons old targetEnv) 0 1).mpr
          intro x hx
          exact hsubset x ((hnew x).mpr (Or.inl hx))
        have holdSat : Sat M.mem (scons old targetEnv) repForm :=
          hOld holdSubset
        have hold : HasSetOrdinalRep N old :=
          (setOrdinalRepExists_model N
            (scons old targetEnv)).mp holdSat
        have helemTarget : M.mem elem target :=
          hsubset elem ((hnew elem).mpr (Or.inr rfl))
        have helemSat : Sat M.mem (scons elem tail) repForm :=
          hmembers elem helemTarget
        have helem : HasSetOrdinalRep N elem :=
          (setOrdinalRepExists_model N
            (scons elem tail)).mp helemSat
        have hnewRep := hadjoin hnew hold helem
        exact (setOrdinalRepExists_model N
          (scons newSet targetEnv)).mpr hnewRep
    have hselfSubset : Sat M.mem (scons target targetEnv)
        (HF_subsetAt 0 1) := by
      apply (HF_subsetAt_spec (scons target targetEnv) 0 1).mpr
      intro x hx
      exact hx
    have htargetRepAt : Sat M.mem (scons target targetEnv) repForm :=
      hsubsets target hselfSubset
    have htargetRep : HasSetOrdinalRep N target :=
      (setOrdinalRepExists_model N
        (scons target targetEnv)).mp htargetRepAt
    exact (setOrdinalRepExists_model N
      (scons target tail)).mpr htargetRep
  exact (setOrdinalRepExists_model N
    (scons set tail)).mp (hall set)

/-! ## Exact total-field theorem from the two isolated boundaries -/

theorem BProv_HFFin_setOrdinalRep_total_of_merge_code
    (hmerge : ∀ {α : Type} {mem : α → α → Prop}
      (v : Nat → α)
      (hHF : ∀ g, HFFinAx_s g → Sat mem v g),
        let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
        ModelSetOrdinalRepMergeLaw
          M.toFirstOrderAdjunctionModel)
    (hcode : ∀ {α : Type} {mem : α → α → Prop}
      (v : Nat → α)
      (hHF : ∀ g, HFFinAx_s g → Sat mem v g),
        let M := firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
        ModelSetOrdinalRepCodeAdjoinLaw
          M.toFirstOrderAdjunctionModel)
    (G : List Form) (set : Nat) :
    BProv HFFinAx_s G
      (fEx (HF_setOrdinalRepAt (set+1) 0)) := by
  apply completeness_inf_context HFFinAx_s G
    (fEx (HF_setOrdinalRepAt (set+1) 0)) Sentences_HFFin
  intro Dom mem v hHF _hG
  let M : FirstOrderFiniteAdjunctionModel Dom :=
    firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
  let N := M.toFirstOrderAdjunctionModel
  have hempty : HasSetOrdinalRep N M.empty := by
    refine ⟨M.empty, ?_⟩
    exact ModelSetOrdinalRep_empty_of_HFFinAx_s
      v hHF (canonicalRepEnv N)
  have hadjoin : ∀ {old elem newSet},
      (∀ x, M.mem x newSet ↔ M.mem x old ∨ x = elem) →
      HasSetOrdinalRep N old →
      HasSetOrdinalRep N elem →
        HasSetOrdinalRep N newSet := by
    intro old elem newSet hnew hold helem
    exact HasSetOrdinalRep_adjoin_of_merge_code N
      (hmerge v hHF) (hcode v hHF) hnew hold helem
  have htotal := HasSetOrdinalRep_total_of_empty_adjoin
    M hempty hadjoin (v set)
  rcases htotal with ⟨code, hrep⟩
  refine ⟨code, ?_⟩
  apply (HF_setOrdinalRepAt_model N
    (scons code v) (set+1) 0).mpr
  have hrep' := ModelSetOrdinalRep_changeEnv N
    (e' := scons code v) hrep
  simpa [scons] using hrep'

end AckermannHF
end SetTheory
