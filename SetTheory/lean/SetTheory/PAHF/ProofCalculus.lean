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

/-- A relative derivation remains valid after prepending any finite block of
local assumptions.  This packages repeated `BProv_context_cons` chains. -/
theorem BProv_context_prefix {B : Formula → Prop}
    (pre : List Formula) {G : List Formula} {phi : Formula}
    (hphi : BProv B G phi) : BProv B (pre ++ G) phi := by
  induction pre with
  | nil => exact hphi
  | cons head tail ih =>
      exact BProv_context_cons (a := head) ih

/-- Add `n` existential binders around `body`. -/
def iterEx : Nat → Formula → Formula
  | 0, body => body
  | n + 1, body => ex (iterEx n body)

/-- Rename a formula once for every witness binder that has been opened. -/
def iterRenameSucc : Nat → Formula → Formula
  | 0, phi => phi
  | n + 1, phi => iterRenameSucc n (rename Nat.succ phi)

/-- Rename an entire context once for every newly opened binder.  Its
recursive shape matches repeated applications of
`BProv_rename_of_sentences`. -/
def iterRenameContextSucc : Nat → List Formula → List Formula
  | 0, G => G
  | n + 1, G => iterRenameContextSucc n (G.map (rename Nat.succ))

/-- Iterated admissibility of successor renaming.  This packages the common
pattern of naming two or three consecutive one-step renamed derivations. -/
theorem BProv_iterRenameSucc_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    (n : Nat) {G : List Formula} {phi : Formula}
    (hphi : BProv B G phi) :
    BProv B (iterRenameContextSucc n G) (iterRenameSucc n phi) := by
  induction n generalizing G phi with
  | zero => exact hphi
  | succ n ih =>
      simp only [iterRenameContextSucc, iterRenameSucc]
      exact ih (BProv_rename_of_sentences (B := B) hB hphi Nat.succ)

/-- Add freshly opened assumptions in outside-in order.  In particular,
`openedContext [outer, inner] G` is
`inner :: (outer :: G.map (rename Nat.succ)).map (rename Nat.succ)`. -/
def openedContext : List Formula → List Formula → List Formula
  | [], G => G
  | body :: rest, G =>
      openedContext rest (body :: G.map (rename Nat.succ))

/-- Lift through any sequence of freshly opened assumptions.  The bodies may
come from different existential theorems; only their opening order matters. -/
theorem BProv_lift_openedContext_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    (bodies : List Formula) {G : List Formula} {phi : Formula}
    (hphi : BProv B G phi) :
    BProv B (openedContext bodies G)
      (iterRenameSucc bodies.length phi) := by
  induction bodies generalizing G phi with
  | nil => exact hphi
  | cons body rest ih =>
      simp only [openedContext, List.length_cons, iterRenameSucc]
      apply ih
      exact BProv_rename_succ_context_cons_of_sentences
        (B := B) hB (a := body) hphi

/-- The finite context visible after eliminating `iterEx n body` over `G`.

For example, opening two witnesses yields
`body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)`.
The recursive definition follows the actual outside-in elimination order, so
clients do not have to reconstruct the shifts by hand. -/
def openedExContext : Nat → Formula → List Formula → List Formula
  | 0, _, G => G
  | n + 1, body, G =>
      openedExContext n body
        (iterEx n body :: G.map (rename Nat.succ))

/-- Eliminate an arbitrary finite block of existential witnesses in one
step.  All de Bruijn shifting is exposed by `openedExContext` and
`iterRenameSucc`, rather than hidden in a client-specific proof. -/
theorem BProv_iterExE_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    (n : Nat) {G : List Formula} {body target : Formula}
    (hex : BProv B G (iterEx n body))
    (hopened : BProv B (openedExContext n body G)
      (iterRenameSucc n target)) :
    BProv B G target := by
  induction n generalizing G target with
  | zero => exact hopened
  | succ n ih =>
      let C : List Formula :=
        iterEx n body :: G.map (rename Nat.succ)
      have hinner : BProv B C (iterEx n body) :=
        BProv_ass (B := B) (G := C) (by simp [C])
      have htargetC : BProv B C (rename Nat.succ target) :=
        ih (G := C) (target := rename Nat.succ target) hinner
          (by simpa [openedExContext, iterRenameSucc, C] using hopened)
      exact BProv_exE_of_sentences (B := B) hB
        (by simpa [iterEx] using hex)
        (by simpa [C] using htargetC)

/-- Two-witness specialization used by paired graph witnesses. -/
theorem BProv_two_exE_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {body target : Formula}
    (hex : BProv B G (ex (ex body)))
    (hopened : BProv B
      (body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ))
      (rename Nat.succ (rename Nat.succ target))) :
    BProv B G target := by
  exact BProv_iterExE_of_sentences (B := B) hB 2 hex hopened

/-- Three-witness specialization used by multiplication graphs. -/
theorem BProv_three_exE_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {body target : Formula}
    (hex : BProv B G (ex (ex (ex body))))
    (hopened : BProv B
      (body :: List.map (rename Nat.succ)
        (ex body :: List.map (rename Nat.succ)
          (ex (ex body) :: List.map (rename Nat.succ) G)))
      (rename Nat.succ (rename Nat.succ (rename Nat.succ target)))) :
    BProv B G target := by
  exact BProv_iterExE_of_sentences (B := B) hB 3 hex hopened

/-- Lift through the two binders of a paired existential witness. -/
theorem BProv_lift_two_opened_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {body phi : Formula}
    (hphi : BProv B G phi) :
    BProv B
      (body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ))
      (rename Nat.succ (rename Nat.succ phi)) := by
  exact BProv_lift_openedContext_of_sentences
    (B := B) hB [ex body, body] hphi

/-- Two-step specialization for distinct outer and inner witness bodies. -/
theorem BProv_lift_two_contexts_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {outer inner phi : Formula}
    (hphi : BProv B G phi) :
    BProv B
      (inner :: (outer :: G.map (rename Nat.succ)).map (rename Nat.succ))
      (rename Nat.succ (rename Nat.succ phi)) := by
  exact BProv_lift_openedContext_of_sentences
    (B := B) hB [outer, inner] hphi

/-- Three-step specialization for distinct witness bodies. -/
theorem BProv_lift_three_contexts_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {outer middle inner phi : Formula}
    (hphi : BProv B G phi) :
    BProv B
      (inner :: List.map (rename Nat.succ)
        (middle :: List.map (rename Nat.succ)
          (outer :: List.map (rename Nat.succ) G)))
      (rename Nat.succ (rename Nat.succ (rename Nat.succ phi))) := by
  exact BProv_lift_openedContext_of_sentences
    (B := B) hB [outer, middle, inner] hphi

/-- Substituting the three freshly opened witness variables cancels the three
binder-aware successor renamings.  The statement is formula-generic and is
shared by multiplication graph constructions. -/
theorem subst_three_witnesses_rename_three_succ
    (phi : Formula) :
    subst (instTerm (Term.var 0))
        (subst (Term.upSubst (instTerm (Term.var 1)))
          (subst
            (Term.upSubst
              (Term.upSubst (instTerm (Term.var 2))))
            (rename
              (SetTheory.up (SetTheory.up (SetTheory.up Nat.succ)))
              (rename
                (SetTheory.up (SetTheory.up (SetTheory.up Nat.succ)))
                (rename
                  (SetTheory.up (SetTheory.up (SetTheory.up Nat.succ)))
                  phi))))) =
      phi := by
  rw [subst_comp, subst_comp, subst_rename, subst_rename, subst_rename]
  calc
    _ = subst (fun n ↦ Term.var n) phi := by
      apply subst_ext_free
      intro n hn
      rcases n with _ | _ | _ | n <;> rfl
    _ = phi := subst_id phi

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
    BProv_ass (B := B) (G := a :: G) (by simp)
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
    BProv_ass (B := B) (G := C) (by simp [C])
  have haC : BProv B C a :=
    BProv_mp B C a' a
      (BProv_context_cons (BProv_context_cons ha)) ha'C
  have habC : BProv B C (imp a b) :=
    BProv_ass (B := B) (G := C) (by simp [C])
  have hbC : BProv B C b := BProv_mp B C a b habC haC
  exact BProv_mp B C b b'
    (BProv_context_cons (BProv_context_cons hb)) hbC

/-- Conjunction is covariant in both components. -/
theorem BProv_and_mono
    {B : Formula → Prop} {G : List Formula} {a a' b b' : Formula}
    (ha : BProv B G (imp a a'))
    (hb : BProv B G (imp b b')) :
    BProv B G (imp (and a b) (and a' b')) := by
  apply BProv_impI
  let C : List Formula := and a b :: G
  have habC : BProv B C (and a b) :=
    BProv_ass (B := B) (G := C) (by simp [C])
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
    BProv_ass (B := B) (G := C) (by simp [C])
  apply BProv_orE horC
  · exact BProv_orI1
      (BProv_mp B (a :: C) a a'
        (BProv_context_cons (BProv_context_cons ha))
        (BProv_ass (B := B) (by simp)))
  · exact BProv_orI2
      (BProv_mp B (b :: C) b b'
        (BProv_context_cons (BProv_context_cons hb))
        (BProv_ass (B := B) (by simp)))

theorem BProv_iffForm_refl
    {B : Formula → Prop} {G : List Formula} (a : Formula) :
    BProv B G (iffForm a a) := by
  have haa : BProv B G (imp a a) :=
    BProv_impI (BProv_ass (B := B) (G := a :: G) (by simp))
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
    BProv_ass (B := B) (G := C) (by simp [C])
  refine BProv_exE_of_sentences hB hexa ?_
  let D : List Formula := a :: C.map (rename Nat.succ)
  have ha : BProv B D a :=
    BProv_ass (B := B) (G := D) (by simp [D])
  have habD : BProv B D (imp a b) := by
    have hctx := BProv_context_cons (B := B) (a := a)
      (BProv_context_cons (B := B) (a := rename Nat.succ (ex a)) hab)
    simpa [D, C] using hctx
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
    BProv_ass (B := B) (G := C) (by simp [C])
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
