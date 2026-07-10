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


end AckermannHF
end SetTheory
