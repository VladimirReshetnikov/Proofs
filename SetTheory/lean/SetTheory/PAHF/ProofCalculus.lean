/-
  SetTheory.PAHF.ProofCalculus

  Reusable proof-calculus combinators for opening finite blocks of
  existential witnesses.  The key nuisance is not logical but syntactic:
  after each witness is opened, every older context formula and the target
  must be renamed through one more de Bruijn binder.  Encoding that context
  transformation once avoids bespoke two- and three-witness proofs.
-/
import SetTheory.PAHF.PASyntax

namespace SetTheory
namespace PA
namespace Formula

/-! ### Directed connective and equivalence calculus -/

/-- Build a formula equivalence from its two directed implications. -/
theorem BProv_iffForm_intro
    {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (hab : BProv B G (imp a b))
    (hba : BProv B G (imp b a)) :
    BProv B G (iffForm a b) := by
  simpa [iffForm] using BProv_andI hab hba

theorem BProv_iffForm_forward
    {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (h : BProv B G (iffForm a b)) :
    BProv B G (imp a b) := by
  simpa [iffForm] using BProv_andE1 h

theorem BProv_iffForm_reverse
    {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (h : BProv B G (iffForm a b)) :
    BProv B G (imp b a) := by
  simpa [iffForm] using BProv_andE2 h

/-- Compose two derivable implications. -/
theorem BProv_imp_trans
    {B : Formula → Prop} {G : List Formula} {a b c : Formula}
    (hab : BProv B G (imp a b))
    (hbc : BProv B G (imp b c)) :
    BProv B G (imp a c) := by
  apply BProv_impI
  have ha : BProv B (a :: G) a :=
    BProv_ass_head
  exact BProv_mp B (a :: G) b c (BProv_context_cons hbc)
    (BProv_mp B (a :: G) a b (BProv_context_cons hab) ha)

/-- Implication is contravariant in its premise and covariant in its result. -/
theorem BProv_imp_mono
    {B : Formula → Prop} {G : List Formula} {a a' b b' : Formula}
    (ha : BProv B G (imp a' a))
    (hb : BProv B G (imp b b')) :
    BProv B G (imp (imp a b) (imp a' b')) := by
  apply BProv_impI
  apply BProv_impI
  let C : List Formula := a' :: imp a b :: G
  have ha'C : BProv B C a' :=
    BProv_ass_head
  have haC : BProv B C a :=
    BProv_mp B C a' a
      (PA.Formula.BProv_context_prefix [a', imp a b] ha) ha'C
  have habC : BProv B C (imp a b) :=
    BProv_ass (B := B) (G := C) (by simp [C])
  have hbC : BProv B C b := BProv_mp B C a b habC haC
  exact BProv_mp B C b b'
    (PA.Formula.BProv_context_prefix [a', imp a b] hb) hbC

/-- Conjunction is covariant in both components. -/
theorem BProv_and_mono
    {B : Formula → Prop} {G : List Formula} {a a' b b' : Formula}
    (ha : BProv B G (imp a a'))
    (hb : BProv B G (imp b b')) :
    BProv B G (imp (and a b) (and a' b')) := by
  apply BProv_impI
  let C : List Formula := and a b :: G
  have habC : BProv B C (and a b) :=
    BProv_ass_head
  exact BProv_andI
    (BProv_mp B C a a' (BProv_context_cons ha) (BProv_andE1 habC))
    (BProv_mp B C b b' (BProv_context_cons hb) (BProv_andE2 habC))

/-- Disjunction is covariant in both components. -/
theorem BProv_or_mono
    {B : Formula → Prop} {G : List Formula} {a a' b b' : Formula}
    (ha : BProv B G (imp a a'))
    (hb : BProv B G (imp b b')) :
    BProv B G (imp (or a b) (or a' b')) := by
  apply BProv_impI
  let C : List Formula := or a b :: G
  have horC : BProv B C (or a b) :=
    BProv_ass_head
  apply BProv_orE horC
  · exact BProv_orI1
      (BProv_mp B (a :: C) a a'
        (PA.Formula.BProv_context_prefix [a, or a b] ha)
        BProv_ass_head)
  · exact BProv_orI2
      (BProv_mp B (b :: C) b b'
        (PA.Formula.BProv_context_prefix [b, or a b] hb)
        BProv_ass_head)

theorem BProv_iffForm_refl
    {B : Formula → Prop} {G : List Formula} (a : Formula) :
    BProv B G (iffForm a a) := by
  have haa : BProv B G (imp a a) :=
    BProv_impI BProv_ass_head
  exact BProv_iffForm_intro haa haa

theorem BProv_iffForm_symm
    {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (h : BProv B G (iffForm a b)) :
    BProv B G (iffForm b a) :=
  BProv_iffForm_intro (BProv_iffForm_reverse h) (BProv_iffForm_forward h)

theorem BProv_iffForm_trans
    {B : Formula → Prop} {G : List Formula} {a b c : Formula}
    (hab : BProv B G (iffForm a b))
    (hbc : BProv B G (iffForm b c)) :
    BProv B G (iffForm a c) :=
  BProv_iffForm_intro
    (BProv_imp_trans (BProv_iffForm_forward hab) (BProv_iffForm_forward hbc))
    (BProv_imp_trans (BProv_iffForm_reverse hbc) (BProv_iffForm_reverse hab))

theorem BProv_iffForm_imp_congr
    {B : Formula → Prop} {G : List Formula} {a a' b b' : Formula}
    (ha : BProv B G (iffForm a a'))
    (hb : BProv B G (iffForm b b')) :
    BProv B G (iffForm (imp a b) (imp a' b')) :=
  BProv_iffForm_intro
    (BProv_imp_mono (BProv_iffForm_reverse ha) (BProv_iffForm_forward hb))
    (BProv_imp_mono (BProv_iffForm_forward ha) (BProv_iffForm_reverse hb))

theorem BProv_iffForm_and_congr
    {B : Formula → Prop} {G : List Formula} {a a' b b' : Formula}
    (ha : BProv B G (iffForm a a'))
    (hb : BProv B G (iffForm b b')) :
    BProv B G (iffForm (and a b) (and a' b')) :=
  BProv_iffForm_intro
    (BProv_and_mono (BProv_iffForm_forward ha) (BProv_iffForm_forward hb))
    (BProv_and_mono (BProv_iffForm_reverse ha) (BProv_iffForm_reverse hb))

theorem BProv_iffForm_or_congr
    {B : Formula → Prop} {G : List Formula} {a a' b b' : Formula}
    (ha : BProv B G (iffForm a a'))
    (hb : BProv B G (iffForm b b')) :
    BProv B G (iffForm (or a b) (or a' b')) :=
  BProv_iffForm_intro
    (BProv_or_mono (BProv_iffForm_forward ha) (BProv_iffForm_forward hb))
    (BProv_or_mono (BProv_iffForm_reverse ha) (BProv_iffForm_reverse hb))

/-- Existential quantification is covariant over a sentence theory. -/
theorem BProv_ex_mono_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {a b : Formula}
    (hab : BProv B (G.map (rename Nat.succ)) (imp a b)) :
    BProv B G (imp (ex a) (ex b)) := by
  apply BProv_impI
  let C : List Formula := ex a :: G
  have hexa : BProv B C (ex a) :=
    BProv_ass_head
  refine BProv_exE_of_sentences hB hexa ?_
  let D : List Formula := a :: C.map (rename Nat.succ)
  have ha : BProv B D a :=
    BProv_ass_head
  have habD : BProv B D (imp a b) := by
    simpa [D, C] using
      (BProv_context_two (first := a) (second := rename Nat.succ (ex a)) hab)
  have hb : BProv B D b := BProv_mp B D a b habD ha
  have hinst : BProv B D
      (subst (instTerm (Term.var 0))
        (rename (SetTheory.up Nat.succ) b)) := by
    simpa [subst_instTerm_var_zero_rename_up_succ] using hb
  have hex : BProv B D (ex (rename (SetTheory.up Nat.succ) b)) :=
    BProv_exI hinst
  simpa [D, C, rename] using hex

theorem BProv_iffForm_ex_congr_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {a b : Formula}
    (h : BProv B (G.map (rename Nat.succ)) (iffForm a b)) :
    BProv B G (iffForm (ex a) (ex b)) :=
  BProv_iffForm_intro
    (BProv_ex_mono_of_sentences hB (BProv_iffForm_forward h))
    (BProv_ex_mono_of_sentences hB (BProv_iffForm_reverse h))

/-- Universal quantification is covariant over a sentence theory. -/
theorem BProv_all_mono_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {a b : Formula}
    (hab : BProv B (G.map (rename Nat.succ)) (imp a b)) :
    BProv B G (imp (all a) (all b)) := by
  apply BProv_impI
  let C : List Formula := all a :: G
  apply BProv_allI_of_sentences hB
  let D : List Formula := C.map (rename Nat.succ)
  have halla : BProv B C (all a) :=
    BProv_ass_head
  have hallaRen : BProv B D (rename Nat.succ (all a)) := by
    simpa [D] using BProv_rename_of_sentences hB halla Nat.succ
  have hainst := BProv_allE (B := B) (G := D)
    (t := Term.var 0) hallaRen
  have ha : BProv B D a := by
    simpa [rename, subst_instTerm_var_zero_rename_up_succ] using hainst
  have habD : BProv B D (imp a b) := by
    have hctx := BProv_context_cons (B := B)
      (a := rename Nat.succ (all a)) hab
    simpa [D, C] using hctx
  exact BProv_mp B D a b habD ha

theorem BProv_iffForm_all_congr_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {a b : Formula}
    (h : BProv B (G.map (rename Nat.succ)) (iffForm a b)) :
    BProv B G (iffForm (all a) (all b)) :=
  BProv_iffForm_intro
    (BProv_all_mono_of_sentences hB (BProv_iffForm_forward h))
    (BProv_all_mono_of_sentences hB (BProv_iffForm_reverse h))

end Formula
end PA
end SetTheory
