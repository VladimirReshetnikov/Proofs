import CombinatoryLogic.SKICoding
import Mathlib.Tactic

/-!
# Primitive certificates for finite SKI reduction

A one-step certificate consists of a root contraction and a list of
application-context frames.  Frames are stored from the contracted redex
outwards.  Every natural number describes a root contraction and every frame
describes one application context, so malformed certificates are impossible.

This representation avoids recursively deciding the contextual `Step`
relation: checking a certificate only reconstructs its source and target.
Lists of step certificates then verify finite reduction traces.
-/

namespace CombinatoryLogic.SKI.Term.ReductionCoding

open Coding

/-! ## Application contexts -/

/-- Raw frame code; tag zero means `hole · argument`, every other tag means
`function · hole`. -/
abbrev Frame := Nat

/-- A frame placing the hole in function position. -/
def leftFrame (argument : Code) : Frame := Nat.pair 0 argument

/-- A frame placing the hole in argument position. -/
def rightFrame (function : Code) : Frame := Nat.pair 1 function

/-- The frame's orientation tag. -/
def frameTag (frame : Frame) : Nat := frame.unpair.1

/-- The fixed sibling stored by a frame. -/
def frameSibling (frame : Frame) : Code := frame.unpair.2

/-- Plug a code into one application frame. -/
def plugFrame (frame : Frame) (hole : Code) : Code :=
  if frameTag frame = 0 then Coding.app hole (frameSibling frame)
  else Coding.app (frameSibling frame) hole

@[simp] theorem plugFrame_left (argument hole : Code) :
    plugFrame (leftFrame argument) hole = Coding.app hole argument := by
  simp [plugFrame, leftFrame, frameTag, frameSibling]

@[simp] theorem plugFrame_right (function hole : Code) :
    plugFrame (rightFrame function) hole = Coding.app function hole := by
  simp [plugFrame, rightFrame, frameTag, frameSibling]

/-- Plug a code through frames ordered from innermost to outermost. -/
def plug (frames : List Frame) (hole : Code) : Code :=
  frames.foldl (fun term frame => plugFrame frame term) hole

@[simp] theorem plug_nil (hole : Code) : plug [] hole = hole := rfl

@[simp] theorem plug_append (frames : List Frame) (frame : Frame) (hole : Code) :
    plug (frames ++ [frame]) hole = plugFrame frame (plug frames hole) := by
  simp [plug]

/-! ## Root contractions -/

/-- A root certificate is an arbitrary natural number.  Its first component
modulo three chooses `I`, `K`, or `S`; its second component contains three
possible arguments. -/
abbrev RootCertificate := Nat

/-- Root-contraction kind in the range `0..2`. -/
def rootKind (certificate : RootCertificate) : Nat := certificate.unpair.1 % 3

/-- First possible root argument. -/
def rootFirst (certificate : RootCertificate) : Code := certificate.unpair.2.unpair.1

/-- Remaining pair of possible root arguments. -/
def rootRest (certificate : RootCertificate) : Nat := certificate.unpair.2.unpair.2

/-- Second possible root argument. -/
def rootSecond (certificate : RootCertificate) : Code := (rootRest certificate).unpair.1

/-- Third possible root argument. -/
def rootThird (certificate : RootCertificate) : Code := (rootRest certificate).unpair.2

/-- Build a canonical root certificate for `I`. -/
def iCertificate (argument : Code) : RootCertificate :=
  Nat.pair 0 (Nat.pair argument 0)

/-- Build a canonical root certificate for `K`. -/
def kCertificate (first second : Code) : RootCertificate :=
  Nat.pair 1 (Nat.pair first (Nat.pair second 0))

/-- Build a canonical root certificate for `S`. -/
def sCertificate (first second third : Code) : RootCertificate :=
  Nat.pair 2 (Nat.pair first (Nat.pair second third))

/-- Source code named by a root certificate. -/
def rootSource (certificate : RootCertificate) : Code :=
  if rootKind certificate = 0 then Coding.app Coding.i (rootFirst certificate)
  else if rootKind certificate = 1 then
    Coding.app (Coding.app Coding.k (rootFirst certificate)) (rootSecond certificate)
  else
    Coding.app (Coding.app (Coding.app Coding.s (rootFirst certificate)) (rootSecond certificate))
      (rootThird certificate)

/-- Contractum code named by a root certificate. -/
def rootTarget (certificate : RootCertificate) : Code :=
  if rootKind certificate = 0 then rootFirst certificate
  else if rootKind certificate = 1 then rootFirst certificate
  else
    Coding.app (Coding.app (rootFirst certificate) (rootThird certificate))
      (Coding.app (rootSecond certificate) (rootThird certificate))

@[simp] theorem rootSource_i (argument : Code) :
    rootSource (iCertificate argument) = Coding.app Coding.i argument := by
  simp [rootSource, rootKind, rootFirst, iCertificate]

@[simp] theorem rootTarget_i (argument : Code) :
    rootTarget (iCertificate argument) = argument := by
  simp [rootTarget, rootKind, rootFirst, iCertificate]

@[simp] theorem rootSource_k (first second : Code) :
    rootSource (kCertificate first second) =
      Coding.app (Coding.app Coding.k first) second := by
  simp [rootSource, rootKind, rootFirst, rootSecond, rootRest, kCertificate]

@[simp] theorem rootTarget_k (first second : Code) :
    rootTarget (kCertificate first second) = first := by
  simp [rootTarget, rootKind, rootFirst, kCertificate]

@[simp] theorem rootSource_s (first second third : Code) :
    rootSource (sCertificate first second third) =
      Coding.app (Coding.app (Coding.app Coding.s first) second) third := by
  simp [rootSource, rootKind, rootFirst, rootSecond, rootThird, rootRest,
    sCertificate]

@[simp] theorem rootTarget_s (first second third : Code) :
    rootTarget (sCertificate first second third) =
      Coding.app (Coding.app first third) (Coding.app second third) := by
  simp [rootTarget, rootKind, rootFirst, rootSecond, rootThird, rootRest,
    sCertificate]

/-- Every root certificate decodes to one genuine SKI contraction. -/
theorem rootCertificate_sound (certificate : RootCertificate) :
    Step (decode (rootSource certificate)) (decode (rootTarget certificate)) := by
  have kindBound : rootKind certificate < 3 := Nat.mod_lt _ (by decide)
  interval_cases kindEquality : rootKind certificate
  · simpa [rootSource, rootTarget, kindEquality] using
      Step.i (decode (rootFirst certificate))
  · simpa [rootSource, rootTarget, kindEquality] using
      Step.k (decode (rootFirst certificate)) (decode (rootSecond certificate))
  · simpa [rootSource, rootTarget, kindEquality] using
      Step.s (decode (rootFirst certificate)) (decode (rootSecond certificate))
        (decode (rootThird certificate))

/-! ## Certified contextual steps -/

/-- A root contraction paired with its innermost-to-outermost context. -/
abbrev StepCertificate := List Frame × RootCertificate

/-- Source reconstructed from a one-step certificate. -/
def certificateSource (certificate : StepCertificate) : Code :=
  plug certificate.1 (rootSource certificate.2)

/-- Target reconstructed from a one-step certificate. -/
def certificateTarget (certificate : StepCertificate) : Code :=
  plug certificate.1 (rootTarget certificate.2)

/-- Plugging the two sides of a root contraction through the same context is
a genuine contextual SKI step. -/
theorem certificate_sound (certificate : StepCertificate) :
    Step (decode (certificateSource certificate))
      (decode (certificateTarget certificate)) := by
  rcases certificate with ⟨frames, root⟩
  induction frames using List.reverseRecOn with
  | nil => simpa [certificateSource, certificateTarget, plug] using
      rootCertificate_sound root
  | append_singleton frames frame inductionHypothesis =>
      by_cases orientation : frameTag frame = 0
      · simpa [certificateSource, certificateTarget, plug_append, plugFrame,
          orientation, decode_app] using
          Step.appLeft (decode (frameSibling frame)) inductionHypothesis
      · simpa [certificateSource, certificateTarget, plug_append, plugFrame,
          orientation, decode_app] using
          Step.appRight (decode (frameSibling frame)) inductionHypothesis

/-- Every genuine one-step reduction has a certificate with exactly its
encoded endpoints. -/
theorem certificate_complete {source target : Term} (reduction : Step source target) :
    ∃ certificate : StepCertificate,
      certificateSource certificate = encode source ∧
      certificateTarget certificate = encode target := by
  induction reduction with
  | i argument =>
      exact ⟨([], iCertificate (encode argument)), by simp [certificateSource,
        certificateTarget]⟩
  | k first second =>
      exact ⟨([], kCertificate (encode first) (encode second)), by
        simp [certificateSource, certificateTarget]⟩
  | s first second third =>
      exact ⟨([], sCertificate (encode first) (encode second) (encode third)), by
        simp [certificateSource, certificateTarget]⟩
  | appLeft argument _ inductionHypothesis =>
      obtain ⟨⟨frames, root⟩, sourceEquality, targetEquality⟩ := inductionHypothesis
      refine ⟨(frames ++ [leftFrame (encode argument)], root), ?_, ?_⟩
      · simpa [certificateSource, plug_append] using
          congrArg (fun code => Coding.app code (encode argument)) sourceEquality
      · simpa [certificateTarget, plug_append] using
          congrArg (fun code => Coding.app code (encode argument)) targetEquality
  | appRight function _ inductionHypothesis =>
      obtain ⟨⟨frames, root⟩, sourceEquality, targetEquality⟩ := inductionHypothesis
      refine ⟨(frames ++ [rightFrame (encode function)], root), ?_, ?_⟩
      · simpa [certificateSource, plug_append] using
          congrArg (Coding.app (encode function)) sourceEquality
      · simpa [certificateTarget, plug_append] using
          congrArg (Coding.app (encode function)) targetEquality

/-! ## Finite traces -/

/-- A finite sequence of certified contextual contractions. -/
abbrev TraceCertificate := List StepCertificate

/-- Apply one certificate when its reconstructed source matches the current
code; otherwise reject the trace. -/
def applyCertificate (current : Option Code) (certificate : StepCertificate) :
    Option Code :=
  current.bind fun source =>
    if source = certificateSource certificate
    then some (certificateTarget certificate)
    else none

/-- Run a list of step certificates from an initial code. -/
def runTrace (source : Code) (trace : TraceCertificate) : Option Code :=
  trace.foldl applyCertificate (some source)

/-- A trace certificate connects two raw codes. -/
def TraceValid (source target : Code) (trace : TraceCertificate) : Prop :=
  runTrace source trace = some target

instance (source target : Code) (trace : TraceCertificate) :
    Decidable (TraceValid source target trace) :=
  inferInstanceAs (Decidable (runTrace source trace = some target))

@[simp] theorem runTrace_nil (source : Code) : runTrace source [] = some source := rfl

private theorem foldl_applyCertificate_none (trace : TraceCertificate) :
    trace.foldl applyCertificate none = none := by
  induction trace with
  | nil => rfl
  | cons certificate trace inductionHypothesis =>
      simp [List.foldl, applyCertificate, inductionHypothesis]

@[simp] theorem runTrace_cons (source : Code) (certificate : StepCertificate)
    (trace : TraceCertificate) :
    runTrace source (certificate :: trace) =
      if source = certificateSource certificate
      then runTrace (certificateTarget certificate) trace
      else none := by
  by_cases sourceEquality : source = certificateSource certificate
  · simp [runTrace, applyCertificate, sourceEquality]
  · simp [runTrace, applyCertificate, sourceEquality, foldl_applyCertificate_none]

/-- Every accepted trace decodes to an ordinary finite SKI reduction. -/
theorem trace_sound {source target : Code} {trace : TraceCertificate}
    (valid : TraceValid source target trace) : Steps (decode source) (decode target) := by
  induction trace generalizing source with
  | nil =>
      simp [TraceValid] at valid
      subst target
      exact .refl
  | cons certificate trace inductionHypothesis =>
      simp only [TraceValid, runTrace_cons] at valid
      split at valid
      next sourceEquality =>
        have firstStep : Step (decode source) (decode (certificateTarget certificate)) := by
          rw [sourceEquality]
          exact certificate_sound certificate
        exact (Steps.single firstStep).trans (inductionHypothesis valid)
      next => cases valid

/-- Every ordinary finite reduction has a finite certificate trace. -/
theorem trace_complete {source target : Term} (reduction : Steps source target) :
    ∃ trace : TraceCertificate, TraceValid (encode source) (encode target) trace := by
  induction reduction with
  | refl => exact ⟨[], rfl⟩
  | tail _ step inductionHypothesis =>
      obtain ⟨trace, traceValid⟩ := inductionHypothesis
      obtain ⟨certificate, sourceEquality, targetEquality⟩ := certificate_complete step
      refine ⟨trace ++ [certificate], ?_⟩
      unfold TraceValid at traceValid ⊢
      simp only [runTrace, List.foldl_append]
      change applyCertificate (runTrace (encode source) trace) certificate = _
      rw [traceValid]
      simp [applyCertificate, sourceEquality, targetEquality]

end CombinatoryLogic.SKI.Term.ReductionCoding
