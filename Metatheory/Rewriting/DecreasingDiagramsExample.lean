/-
# Decreasing Diagrams Example (Non-Terminating)

This module gives a small non-terminating ARS whose confluence is proved
using decreasing diagrams. The system has a single local peak that is
closed by strictly smaller labels.
-/

import Metatheory.Rewriting.DecreasingDiagramsCertificate

namespace Metatheory.RewritingExample

open Rewriting
open Lean

/-! ## Example System -/

/-- States for the example rewriting system. -/
inductive Node where
  | a : Node
  | b : Node
  | c : Node
  | d : Node
  deriving DecidableEq, Repr, FromJson, ToJson

open Node

/-- Labeled steps for a non-terminating but confluent system. -/
inductive LStep : Nat → Node → Node → Prop where
  | a_to_b : LStep 2 a b
  | a_to_c : LStep 2 a c
  | b_to_d : LStep 1 b d
  | c_to_d : LStep 1 c d
  | d_to_a : LStep 0 d a

private def LStepCode (l : Nat) (x y : Node) : Prop :=
  (l = 2 ∧ x = a ∧ y = b) ∨
  (l = 2 ∧ x = a ∧ y = c) ∨
  (l = 1 ∧ x = b ∧ y = d) ∨
  (l = 1 ∧ x = c ∧ y = d) ∨
  (l = 0 ∧ x = d ∧ y = a)

private theorem lStepCode_iff (l : Nat) (x y : Node) : LStepCode l x y ↔ LStep l x y := by
  constructor
  · intro h
    rcases h with h | h | h | h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact LStep.a_to_b
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact LStep.a_to_c
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact LStep.b_to_d
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact LStep.c_to_d
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact LStep.d_to_a
  · intro h
    cases h with
    | a_to_b => exact Or.inl ⟨rfl, rfl, rfl⟩
    | a_to_c => exact Or.inr <| Or.inl ⟨rfl, rfl, rfl⟩
    | b_to_d => exact Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl, rfl⟩
    | c_to_d => exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl, rfl⟩
    | d_to_a => exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨rfl, rfl, rfl⟩

private instance instDecidableLStepCode (l : Nat) (x y : Node) : Decidable (LStepCode l x y) := by
  unfold LStepCode
  infer_instance

instance instDecidableLStep (l : Nat) (x y : Node) : Decidable (LStep l x y) :=
  decidable_of_iff (LStepCode l x y) (lStepCode_iff l x y)

private instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | Except.error e₁, Except.error e₂ =>
      match decEq e₁ e₂ with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
  | Except.ok a₁, Except.ok a₂ =>
      match decEq a₁ a₂ with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
  | Except.error _, Except.ok _ => isFalse (by intro hEq; cases hEq)
  | Except.ok _, Except.error _ => isFalse (by intro hEq; cases hEq)

/-- Unlabeled step relation. -/
abbrev Step : Node → Node → Prop := LabeledUnion LStep

/-! ## Non-Termination -/

/-- A reduction loop witnessing non-termination. -/
theorem step_loop : Plus Step a a := by
  have hab : Step a b := ⟨2, LStep.a_to_b⟩
  have hbd : Step b d := ⟨1, LStep.b_to_d⟩
  have hda : Step d a := ⟨0, LStep.d_to_a⟩
  exact Plus.tail (Plus.tail (Plus.single hab) hbd) hda

/-- The system is not terminating. -/
theorem step_not_terminating : ¬ Terminating Step := by
  intro hterm
  have hloop : Plus Step a a := step_loop
  have hirrefl : ∀ {x : Node}, Acc (fun u v => Plus Step v u) x → ¬ Plus Step x x := by
    intro x hacc
    induction hacc with
    | intro y _ ih =>
        intro hyy
        exact ih y hyy hyy
  exact hirrefl (hterm.apply a) hloop

/-! ## Local Decreasing -/

private def cert_a_to_b_a_to_b : PeakCertificate LStep (· < ·) where
  source := a
  leftLabel := 2
  leftTarget := b
  rightLabel := 2
  rightTarget := b
  leftStep := LStep.a_to_b
  rightStep := LStep.a_to_b
  valley := ValleyCertificate.refl (r := LStep) (lt := (· < ·)) b 2 2

private def cert_a_to_b_a_to_c : PeakCertificate LStep (· < ·) where
  source := a
  leftLabel := 2
  leftTarget := b
  rightLabel := 2
  rightTarget := c
  leftStep := LStep.a_to_b
  rightStep := LStep.a_to_c
  valley := ValleyCertificate.ofSingleSteps (r := LStep) (lt := (· < ·))
    LStep.b_to_d LStep.c_to_d (by decide) (by decide)

private def cert_a_to_c_a_to_b : PeakCertificate LStep (· < ·) where
  source := a
  leftLabel := 2
  leftTarget := c
  rightLabel := 2
  rightTarget := b
  leftStep := LStep.a_to_c
  rightStep := LStep.a_to_b
  valley := ValleyCertificate.ofSingleSteps (r := LStep) (lt := (· < ·))
    LStep.c_to_d LStep.b_to_d (by decide) (by decide)

private def cert_a_to_c_a_to_c : PeakCertificate LStep (· < ·) where
  source := a
  leftLabel := 2
  leftTarget := c
  rightLabel := 2
  rightTarget := c
  leftStep := LStep.a_to_c
  rightStep := LStep.a_to_c
  valley := ValleyCertificate.refl (r := LStep) (lt := (· < ·)) c 2 2

private def cert_b_to_d_b_to_d : PeakCertificate LStep (· < ·) where
  source := b
  leftLabel := 1
  leftTarget := d
  rightLabel := 1
  rightTarget := d
  leftStep := LStep.b_to_d
  rightStep := LStep.b_to_d
  valley := ValleyCertificate.refl (r := LStep) (lt := (· < ·)) d 1 1

private def cert_c_to_d_c_to_d : PeakCertificate LStep (· < ·) where
  source := c
  leftLabel := 1
  leftTarget := d
  rightLabel := 1
  rightTarget := d
  leftStep := LStep.c_to_d
  rightStep := LStep.c_to_d
  valley := ValleyCertificate.refl (r := LStep) (lt := (· < ·)) d 1 1

private def cert_d_to_a_d_to_a : PeakCertificate LStep (· < ·) where
  source := d
  leftLabel := 0
  leftTarget := a
  rightLabel := 0
  rightTarget := a
  leftStep := LStep.d_to_a
  rightStep := LStep.d_to_a
  valley := ValleyCertificate.refl (r := LStep) (lt := (· < ·)) a 0 0

/-- Finite explicit decreasing-diagram certificate for the example system. -/
private def stepCertificate : CertifiedLocallyDecreasing LStep (· < ·) where
  certs :=
    [ cert_a_to_b_a_to_b
    , cert_a_to_b_a_to_c
    , cert_a_to_c_a_to_b
    , cert_a_to_c_a_to_c
    , cert_b_to_d_b_to_d
    , cert_c_to_d_c_to_d
    , cert_d_to_a_d_to_a
    ]
  complete := by
    intro x y z l1 l2 hxy hxz
    cases hxy <;> cases hxz
    · exact ⟨cert_a_to_b_a_to_b, by simp, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨cert_a_to_b_a_to_c, by simp, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨cert_a_to_c_a_to_b, by simp, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨cert_a_to_c_a_to_c, by simp, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨cert_b_to_d_b_to_d, by simp, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨cert_c_to_d_c_to_d, by simp, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨cert_d_to_a_d_to_a, by simp, rfl, rfl, rfl, rfl, rfl⟩

private def rawSteps : List (StepTriple Node Nat) :=
  [ { label := 2, source := a, target := b }
  , { label := 2, source := a, target := c }
  , { label := 1, source := b, target := d }
  , { label := 1, source := c, target := d }
  , { label := 0, source := d, target := a }
  ]

private def rawCert_a_to_b_a_to_b : RawPeakCertificate Node Nat where
  source := a
  leftLabel := 2
  leftTarget := b
  rightLabel := 2
  rightTarget := b
  valley := RawValleyCertificate.refl b

private def rawCert_a_to_b_a_to_c : RawPeakCertificate Node Nat where
  source := a
  leftLabel := 2
  leftTarget := b
  rightLabel := 2
  rightTarget := c
  valley := RawValleyCertificate.ofSingleSteps d 1 1

private def rawCert_a_to_c_a_to_b : RawPeakCertificate Node Nat where
  source := a
  leftLabel := 2
  leftTarget := c
  rightLabel := 2
  rightTarget := b
  valley := RawValleyCertificate.ofSingleSteps d 1 1

private def rawCert_a_to_c_a_to_c : RawPeakCertificate Node Nat where
  source := a
  leftLabel := 2
  leftTarget := c
  rightLabel := 2
  rightTarget := c
  valley := RawValleyCertificate.refl c

private def rawCert_b_to_d_b_to_d : RawPeakCertificate Node Nat where
  source := b
  leftLabel := 1
  leftTarget := d
  rightLabel := 1
  rightTarget := d
  valley := RawValleyCertificate.refl d

private def rawCert_c_to_d_c_to_d : RawPeakCertificate Node Nat where
  source := c
  leftLabel := 1
  leftTarget := d
  rightLabel := 1
  rightTarget := d
  valley := RawValleyCertificate.refl d

private def rawCert_d_to_a_d_to_a : RawPeakCertificate Node Nat where
  source := d
  leftLabel := 0
  leftTarget := a
  rightLabel := 0
  rightTarget := a
  valley := RawValleyCertificate.refl a

/-- Fully checkable decreasing-diagram certificate for the example system. -/
private def rawStepCertificate : RawCertifiedLocallyDecreasing Node Nat where
  steps := rawSteps
  certs :=
    [ rawCert_a_to_b_a_to_b
    , rawCert_a_to_b_a_to_c
    , rawCert_a_to_c_a_to_b
    , rawCert_a_to_c_a_to_c
    , rawCert_b_to_d_b_to_d
    , rawCert_c_to_d_c_to_d
    , rawCert_d_to_a_d_to_a
    ]

private theorem rawStepCertificate_complete : rawStepCertificate.StepsComplete LStep := by
  intro x y l hxy
  cases hxy <;> simp [rawStepCertificate, rawSteps]

private theorem rawStepCertificate_check :
    rawStepCertificate.check (r := LStep) (lt := (· < ·)) = true := by
  native_decide

/-- Compressed artifact obtained by removing trivial and symmetric duplicate peaks. -/
private def compressedStepCertificate : CompressedRawCertifiedLocallyDecreasing Node Nat :=
  CompressedRawCertifiedLocallyDecreasing.ofRaw rawStepCertificate

private theorem compressedStepCertificate_valid :
    compressedStepCertificate.Valid LStep (· < ·) :=
  CompressedRawCertifiedLocallyDecreasing.valid_of_ofRaw_valid
    (r := LStep) (lt := (· < ·))
    (rawStepCertificate.valid_of_check_eq_true (r := LStep) (lt := (· < ·)) rawStepCertificate_check)

private theorem compressedStepCertificate_complete :
    compressedStepCertificate.StepsComplete LStep := by
  simpa [compressedStepCertificate, rawStepCertificate, CompressedRawCertifiedLocallyDecreasing.ofRaw,
    CompressedRawCertifiedLocallyDecreasing.StepsComplete] using rawStepCertificate_complete

private theorem compressedStepCertificate_check :
    compressedStepCertificate.check (r := LStep) (lt := (· < ·)) = true :=
  compressedStepCertificate.check_eq_true_of_valid (r := LStep) (lt := (· < ·))
    compressedStepCertificate_valid

/-- External compressed JSON artifact for the checked decreasing-diagram certificate. -/
def stepCertificateJson : String :=
  CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed compressedStepCertificate

private theorem stepCertificateJson_parses :
    CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Nat) stepCertificateJson =
      Except.ok compressedStepCertificate := by
  native_decide

theorem stepCertificateJson_checks :
    CompressedRawCertifiedLocallyDecreasing.checkJson (α := Node) (L := Nat)
      (r := LStep) (lt := (· < ·))
      stepCertificateJson = Except.ok true :=
  CompressedRawCertifiedLocallyDecreasing.checkJson_eq_ok_true_of_parseJson_eq_ok
    (r := LStep) (lt := (· < ·)) stepCertificateJson_parses compressedStepCertificate_check

/-- External JSON artifact loaded from the repository artifact bundle. -/
def stepCertificateFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "example.json"

theorem stepCertificateFileJson_eq_stepCertificateJson :
    stepCertificateFileJson = stepCertificateJson := by
  native_decide

private theorem stepCertificateFileJson_parses :
    CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Nat) stepCertificateFileJson =
      Except.ok compressedStepCertificate := by
  simpa [stepCertificateFileJson_eq_stepCertificateJson] using stepCertificateJson_parses

theorem stepCertificateFileJson_checks :
    CompressedRawCertifiedLocallyDecreasing.checkJson (α := Node) (L := Nat)
      (r := LStep) (lt := (· < ·))
      stepCertificateFileJson = Except.ok true := by
  simpa [stepCertificateFileJson_eq_stepCertificateJson] using stepCertificateJson_checks

/-- The labeled system is locally decreasing with respect to `<`. -/
theorem step_locallyDecreasing : LocallyDecreasing LStep (· < ·) :=
  compressedStepCertificate.sound (r := LStep) (lt := (· < ·))
    compressedStepCertificate_valid compressedStepCertificate_complete

/-! ## Confluence -/

/-- Confluence via an external JSON certificate artifact and the decreasing-diagram checker. -/
theorem step_confluent : Confluent Step :=
  CompressedRawCertifiedLocallyDecreasing.confluent_of_parseJson_eq_ok
    (r := LStep) (lt := (· < ·)) Nat.lt_wfRel.wf
    stepCertificateFileJson_parses compressedStepCertificate_valid compressedStepCertificate_complete

end Metatheory.RewritingExample
