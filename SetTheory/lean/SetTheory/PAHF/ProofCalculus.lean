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

/-- Lift a relative derivation through any finite block of freshly opened
existential witnesses. -/
theorem BProv_lift_openedExContext_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    (n : Nat) {G : List Formula} {body phi : Formula}
    (hphi : BProv B G phi) :
    BProv B (openedExContext n body G) (iterRenameSucc n phi) := by
  induction n generalizing G phi with
  | zero => exact hphi
  | succ n ih =>
      simp only [openedExContext, iterRenameSucc]
      apply ih
      exact BProv_rename_succ_context_cons_of_sentences
        (B := B) hB (a := iterEx n body) hphi

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
  exact BProv_lift_openedExContext_of_sentences
    (B := B) hB 2 (body := body) hphi

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

end Formula
end PA
end SetTheory
