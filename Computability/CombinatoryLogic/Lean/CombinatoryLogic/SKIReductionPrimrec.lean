import CombinatoryLogic.SKIReductionCoding
import Mathlib.Computability.Primrec.List

/-!
# Primitive recursiveness of SKI reduction certificates

`SKIReductionCoding` proves that one-step certificates and finite traces are
sound and complete for the local context-closed SKI reduction.  This module
proves that reconstructing and checking those certificates is primitive
recursive.  Consequently, finite SKI reduction is recursively enumerable and
can be searched with `Nat.Partrec.rfindOpt` in the exact observation semantics.
-/

namespace CombinatoryLogic.SKI.Term.ReductionCoding

open Coding

/-! ## Frames and contexts -/

theorem primrec_leftFrame : Primrec leftFrame :=
  Primrec₂.natPair.comp (Primrec.const 0) Primrec.id

theorem primrec_rightFrame : Primrec rightFrame :=
  Primrec₂.natPair.comp (Primrec.const 1) Primrec.id

theorem primrec_frameTag : Primrec frameTag := by
  exact (Primrec.fst.comp Primrec.unpair).of_eq (fun _ => rfl)

theorem primrec_frameSibling : Primrec frameSibling := by
  exact (Primrec.snd.comp Primrec.unpair).of_eq (fun _ => rfl)

theorem primrec₂_plugFrame : Primrec₂ plugFrame := by
  apply Primrec₂.mk
  have isLeft : PrimrecPred (fun input : Frame × Code => frameTag input.1 = 0) :=
    Primrec.eq.comp (primrec_frameTag.comp Primrec.fst) (Primrec.const 0)
  exact Primrec.ite isLeft
    (Coding.primrec_app.comp Primrec.snd (primrec_frameSibling.comp Primrec.fst))
    (Coding.primrec_app.comp (primrec_frameSibling.comp Primrec.fst) Primrec.snd)

theorem primrec₂_plug : Primrec₂ plug := by
  apply Primrec₂.mk
  have frame : Primrec₂ (fun (_ : List Frame × Code) (state : Code × Frame) => state.2) :=
    Primrec.snd.comp₂ Primrec₂.right
  have hole : Primrec₂ (fun (_ : List Frame × Code) (state : Code × Frame) => state.1) :=
    Primrec.fst.comp₂ Primrec₂.right
  simpa [plug] using
    (Primrec.list_foldl (f := fun input : List Frame × Code => input.1)
      (g := fun input : List Frame × Code => input.2)
      (h := fun _ state => plugFrame state.2 state.1)
      Primrec.fst Primrec.snd (primrec₂_plugFrame.comp₂ frame hole))

/-! ## Root contractions -/

theorem primrec_rootKind : Primrec rootKind := by
  exact (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 3)).of_eq
    (fun _ => rfl)

theorem primrec_rootFirst : Primrec rootFirst := by
  exact (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).of_eq
    (fun _ => rfl)

theorem primrec_rootRest : Primrec rootRest := by
  exact (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).of_eq
    (fun _ => rfl)

theorem primrec_rootSecond : Primrec rootSecond := by
  exact (Primrec.fst.comp (Primrec.unpair.comp primrec_rootRest)).of_eq (fun _ => rfl)

theorem primrec_rootThird : Primrec rootThird := by
  exact (Primrec.snd.comp (Primrec.unpair.comp primrec_rootRest)).of_eq (fun _ => rfl)

theorem primrec_iCertificate : Primrec iCertificate := by
  exact Primrec₂.natPair.comp (Primrec.const 0)
    (Primrec₂.natPair.comp Primrec.id (Primrec.const 0))

theorem primrec₂_kCertificate : Primrec₂ kCertificate := by
  exact Primrec₂.natPair.comp₂ (Primrec₂.const 1)
    (Primrec₂.natPair.comp₂ Primrec₂.left
      (Primrec₂.natPair.comp₂ Primrec₂.right (Primrec₂.const 0)))

theorem primrec_rootSource : Primrec rootSource := by
  have kindIsZero : PrimrecPred (fun certificate : RootCertificate => rootKind certificate = 0) :=
    Primrec.eq.comp primrec_rootKind (Primrec.const 0)
  have kindIsOne : PrimrecPred (fun certificate : RootCertificate => rootKind certificate = 1) :=
    Primrec.eq.comp primrec_rootKind (Primrec.const 1)
  have iSource : Primrec (fun certificate : RootCertificate =>
      Coding.app Coding.i (rootFirst certificate)) :=
    Coding.primrec_app.comp (Primrec.const Coding.i) primrec_rootFirst
  have kHead : Primrec (fun certificate : RootCertificate =>
      Coding.app Coding.k (rootFirst certificate)) :=
    Coding.primrec_app.comp (Primrec.const Coding.k) primrec_rootFirst
  have kSource : Primrec (fun certificate : RootCertificate =>
      Coding.app (Coding.app Coding.k (rootFirst certificate)) (rootSecond certificate)) :=
    Coding.primrec_app.comp kHead primrec_rootSecond
  have sHead : Primrec (fun certificate : RootCertificate =>
      Coding.app Coding.s (rootFirst certificate)) :=
    Coding.primrec_app.comp (Primrec.const Coding.s) primrec_rootFirst
  have sHeadSecond : Primrec (fun certificate : RootCertificate =>
      Coding.app (Coding.app Coding.s (rootFirst certificate)) (rootSecond certificate)) :=
    Coding.primrec_app.comp sHead primrec_rootSecond
  have sSource : Primrec (fun certificate : RootCertificate =>
      Coding.app (Coding.app (Coding.app Coding.s (rootFirst certificate))
        (rootSecond certificate)) (rootThird certificate)) :=
    Coding.primrec_app.comp sHeadSecond primrec_rootThird
  exact Primrec.ite kindIsZero iSource (Primrec.ite kindIsOne kSource sSource)

theorem primrec_rootTarget : Primrec rootTarget := by
  have kindIsZero : PrimrecPred (fun certificate : RootCertificate => rootKind certificate = 0) :=
    Primrec.eq.comp primrec_rootKind (Primrec.const 0)
  have kindIsOne : PrimrecPred (fun certificate : RootCertificate => rootKind certificate = 1) :=
    Primrec.eq.comp primrec_rootKind (Primrec.const 1)
  have firstThird : Primrec (fun certificate : RootCertificate =>
      Coding.app (rootFirst certificate) (rootThird certificate)) :=
    Coding.primrec_app.comp primrec_rootFirst primrec_rootThird
  have secondThird : Primrec (fun certificate : RootCertificate =>
      Coding.app (rootSecond certificate) (rootThird certificate)) :=
    Coding.primrec_app.comp primrec_rootSecond primrec_rootThird
  have sTarget : Primrec (fun certificate : RootCertificate =>
      Coding.app (Coding.app (rootFirst certificate) (rootThird certificate))
        (Coding.app (rootSecond certificate) (rootThird certificate))) :=
    Coding.primrec_app.comp firstThird secondThird
  exact Primrec.ite kindIsZero primrec_rootFirst
    (Primrec.ite kindIsOne primrec_rootFirst sTarget)

/-! ## One-step and trace checking -/

theorem primrec_certificateSource : Primrec certificateSource := by
  exact (primrec₂_plug.comp Primrec.fst (primrec_rootSource.comp Primrec.snd)).of_eq
    (fun _ => rfl)

theorem primrec_certificateTarget : Primrec certificateTarget := by
  exact (primrec₂_plug.comp Primrec.fst (primrec_rootTarget.comp Primrec.snd)).of_eq
    (fun _ => rfl)

theorem primrec₂_applyCertificate : Primrec₂ applyCertificate := by
  apply Primrec₂.mk
  have sourceMatches : PrimrecPred
      (fun input : (Option Code × StepCertificate) × Code =>
        input.2 = certificateSource input.1.2) :=
    Primrec.eq.comp Primrec.snd
      (primrec_certificateSource.comp (Primrec.snd.comp Primrec.fst))
  have success : Primrec
      (fun input : (Option Code × StepCertificate) × Code =>
        some (certificateTarget input.1.2)) :=
    Primrec.option_some.comp
      (primrec_certificateTarget.comp (Primrec.snd.comp Primrec.fst))
  have continuation : Primrec₂
      (fun (input : Option Code × StepCertificate) (source : Code) =>
        if source = certificateSource input.2
        then some (certificateTarget input.2)
        else none) :=
    Primrec₂.mk (Primrec.ite sourceMatches success (Primrec.const none))
  simpa [applyCertificate] using
    (Primrec.option_bind (f := fun input : Option Code × StepCertificate => input.1)
      (g := fun input source =>
        if source = certificateSource input.2
        then some (certificateTarget input.2)
        else none)
      Primrec.fst continuation)

theorem primrec₂_runTrace : Primrec₂ runTrace := by
  apply Primrec₂.mk
  have current : Primrec₂
      (fun (_ : Code × TraceCertificate) (state : Option Code × StepCertificate) =>
        state.1) :=
    Primrec.fst.comp₂ Primrec₂.right
  have certificate : Primrec₂
      (fun (_ : Code × TraceCertificate) (state : Option Code × StepCertificate) =>
        state.2) :=
    Primrec.snd.comp₂ Primrec₂.right
  simpa [runTrace] using
    (Primrec.list_foldl (f := fun input : Code × TraceCertificate => input.2)
      (g := fun input : Code × TraceCertificate => some input.1)
      (h := fun _ state => applyCertificate state.1 state.2)
      Primrec.snd (Primrec.option_some.comp Primrec.fst)
      (primrec₂_applyCertificate.comp₂ current certificate))

/-- Exact trace validity is a primitive-recursive relation between endpoint
pairs and finite trace certificates. -/
theorem primrecRel_traceValid : PrimrecRel
    (fun endpoints : Code × Code => fun trace : TraceCertificate =>
      TraceValid endpoints.1 endpoints.2 trace) := by
  have traceResult : Primrec₂
      (fun endpoints : Code × Code => fun trace : TraceCertificate =>
        runTrace endpoints.1 trace) :=
    primrec₂_runTrace.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  have expected : Primrec₂
      (fun endpoints : Code × Code => fun (_ : TraceCertificate) => some endpoints.2) :=
    Primrec.option_some.comp₂ (Primrec.snd.comp₂ Primrec₂.left)
  simpa [TraceValid] using Primrec.eq.comp₂ traceResult expected

end CombinatoryLogic.SKI.Term.ReductionCoding
