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

end AckermannHF
end SetTheory

