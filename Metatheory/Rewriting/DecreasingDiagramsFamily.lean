/-
# Decreasing Diagrams Family (Growing Certified Instances)

This module defines a size-growing family of finite, non-terminating ARSs.
Instance `n` consists of `n + 1` independent peak gadgets. Each gadget has
one genuine two-branch local peak and three single-step sources, so the
certificate family grows linearly while compression removes all trivial peaks
and one symmetric orientation per gadget.
-/

import Metatheory.Rewriting.DecreasingDiagramsCertificate

namespace Metatheory.RewritingFamily

open Rewriting
open Lean

instance {n : Nat} : ToJson (Fin n) where
  toJson i := toJson i.1

instance {n : Nat} : FromJson (Fin n) where
  fromJson? j := do
    let i ← fromJson? (α := Nat) j
    if h : i < n then
      pure ⟨i, h⟩
    else
      throw s!"expected an index in Fin {n}, got {i}"

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

/-- Node type for the `n`th gadget family. -/
inductive Node (n : Nat) where
  | hub : Fin (n + 1) → Node n
  | left : Fin (n + 1) → Node n
  | right : Fin (n + 1) → Node n
  | join : Fin (n + 1) → Node n
  deriving DecidableEq, Repr, FromJson, ToJson

/-- Labels for the `n`th gadget family. -/
inductive Label (n : Nat) where
  | peak : Fin (n + 1) → Label n
  | down : Fin (n + 1) → Label n
  | loop : Label n
  deriving DecidableEq, Repr, FromJson, ToJson

open Node Label

/-- Each gadget contributes two top steps, two strictly smaller joining steps,
and one loop step. -/
inductive LStep (n : Nat) : Label n → Node n → Node n → Prop where
  | hub_to_left (i : Fin (n + 1)) : LStep n (.peak i) (.hub i) (.left i)
  | hub_to_right (i : Fin (n + 1)) : LStep n (.peak i) (.hub i) (.right i)
  | left_to_join (i : Fin (n + 1)) : LStep n (.down i) (.left i) (.join i)
  | right_to_join (i : Fin (n + 1)) : LStep n (.down i) (.right i) (.join i)
  | join_to_hub (i : Fin (n + 1)) : LStep n .loop (.join i) (.hub i)

private def LStepCode (n : Nat) : Label n → Node n → Node n → Prop
  | .peak i, .hub j, .left k => i = j ∧ j = k
  | .peak i, .hub j, .right k => i = j ∧ j = k
  | .down i, .left j, .join k => i = j ∧ j = k
  | .down i, .right j, .join k => i = j ∧ j = k
  | .loop, .join i, .hub j => i = j
  | _, _, _ => False

private theorem lStepCode_iff (n : Nat) (l : Label n) (x y : Node n) :
    LStepCode n l x y ↔ LStep n l x y := by
  constructor
  · intro h
    cases l <;> cases x <;> cases y <;> simp [LStepCode] at h
    · rcases h with ⟨rfl, rfl⟩
      exact LStep.hub_to_left _
    · rcases h with ⟨rfl, rfl⟩
      exact LStep.hub_to_right _
    · rcases h with ⟨rfl, rfl⟩
      exact LStep.left_to_join _
    · rcases h with ⟨rfl, rfl⟩
      exact LStep.right_to_join _
    · rcases h with rfl
      exact LStep.join_to_hub _
  · intro h
    cases h <;> simp [LStepCode]

private instance instDecidableLStepCode (n : Nat) (l : Label n) (x y : Node n) :
    Decidable (LStepCode n l x y) := by
  cases l <;> cases x <;> cases y <;> simp [LStepCode] <;> infer_instance

instance instDecidableLStep (n : Nat) (l : Label n) (x y : Node n) :
    Decidable (LStep n l x y) :=
  decidable_of_iff (LStepCode n l x y) (lStepCode_iff n l x y)

/-- Unlabeled step relation. -/
abbrev Step (n : Nat) : Node n → Node n → Prop := LabeledUnion (LStep n)

/-- Rank used for decreasing-diagram labels. -/
def labelRank {n : Nat} : Label n → Nat
  | .peak i => 2 * i.1 + 2
  | .down i => 2 * i.1 + 1
  | .loop => 0

/-- The strict order on labels induced by `labelRank`. -/
def LabelLt (n : Nat) : Label n → Label n → Prop := fun l₁ l₂ => labelRank l₁ < labelRank l₂

instance instDecidableRelLabelLt (n : Nat) : DecidableRel (LabelLt n) := by
  intro l₁ l₂
  unfold LabelLt
  infer_instance

theorem labelLt_wf (n : Nat) : WellFounded (LabelLt n) :=
  (measure (labelRank (n := n))).wf

private theorem down_lt_peak {n : Nat} (i : Fin (n + 1)) :
    LabelLt n (.down i) (.peak i) := by
  change 2 * i.1 + 1 < 2 * i.1 + 1 + 1
  exact Nat.lt_succ_self (2 * i.1 + 1)

/-! ## Non-Termination -/

/-- Every family instance contains a simple 3-step loop. -/
theorem step_loop (n : Nat) : Plus (Step n) (.hub 0) (.hub 0) := by
  let i : Fin (n + 1) := 0
  have h₁ : Step n (.hub i) (.left i) := ⟨.peak i, LStep.hub_to_left i⟩
  have h₂ : Step n (.left i) (.join i) := ⟨.down i, LStep.left_to_join i⟩
  have h₃ : Step n (.join i) (.hub i) := ⟨.loop, LStep.join_to_hub i⟩
  exact Plus.tail (Plus.tail (Plus.single h₁) h₂) h₃

/-- The family is not terminating for any size parameter. -/
theorem step_not_terminating (n : Nat) : ¬ Terminating (Step n) := by
  intro hterm
  have hloop : Plus (Step n) (.hub 0) (.hub 0) := step_loop n
  have hirrefl : ∀ {x : Node n}, Acc (fun u v => Plus (Step n) v u) x → ¬ Plus (Step n) x x := by
    intro x hacc
    induction hacc with
    | intro y _ ih =>
        intro hyy
        exact ih y hyy hyy
  exact hirrefl (hterm.apply (.hub 0)) hloop

/-! ## Finite Support -/

private def indices (n : Nat) : List (Fin (n + 1)) :=
  List.finRange (n + 1)

private theorem mem_indices (n : Nat) (i : Fin (n + 1)) : i ∈ indices n := by
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- Full node support for the finite family instance. -/
def supportNodes (n : Nat) : List (Node n) :=
  (indices n).map .hub ++
    (indices n).map .left ++
    (indices n).map .right ++
    (indices n).map .join

/-- Full label support for the finite family instance. -/
def supportLabels (n : Nat) : List (Label n) :=
  .loop :: (indices n).map .down ++ (indices n).map .peak

private theorem supportNodes_complete (n : Nat) (node : Node n) :
    node ∈ supportNodes n := by
  cases node with
  | hub i =>
      simp [supportNodes, mem_indices n i]
  | left i =>
      simp [supportNodes, mem_indices n i]
  | right i =>
      simp [supportNodes, mem_indices n i]
  | join i =>
      simp [supportNodes, mem_indices n i]

private theorem supportLabels_complete (n : Nat) (label : Label n) :
    label ∈ supportLabels n := by
  cases label with
  | loop =>
      simp [supportLabels]
  | peak i =>
      simp [supportLabels, mem_indices n i]
  | down i =>
      simp [supportLabels, mem_indices n i]

/-- The finite support used to auto-enumerate every real step. -/
def support (n : Nat) : FiniteLabeledARS (Node n) (Label n) where
  nodes := supportNodes n
  labels := supportLabels n
  nodesComplete := supportNodes_complete n
  labelsComplete := supportLabels_complete n

/-! ## Raw and Compressed Certificates -/

private def reflCert {n : Nat} (label : Label n) (source target : Node n) :
    RawPeakCertificate (Node n) (Label n) where
  source := source
  leftLabel := label
  leftTarget := target
  rightLabel := label
  rightTarget := target
  valley := RawValleyCertificate.refl target

private def peakCertLR {n : Nat} (i : Fin (n + 1)) :
    RawPeakCertificate (Node n) (Label n) where
  source := .hub i
  leftLabel := .peak i
  leftTarget := .left i
  rightLabel := .peak i
  rightTarget := .right i
  valley := RawValleyCertificate.ofSingleSteps (.join i) (.down i) (.down i)

private def peakCertRL {n : Nat} (i : Fin (n + 1)) :
    RawPeakCertificate (Node n) (Label n) where
  source := .hub i
  leftLabel := .peak i
  leftTarget := .right i
  rightLabel := .peak i
  rightTarget := .left i
  valley := RawValleyCertificate.ofSingleSteps (.join i) (.down i) (.down i)

/-- Trivial peak certificates, one for every real step. -/
def trivialCerts (n : Nat) : List (RawPeakCertificate (Node n) (Label n)) :=
  let is := indices n
  (is.map fun i => reflCert (.peak i) (.hub i) (.left i)) ++
  (is.map fun i => reflCert (.peak i) (.hub i) (.right i)) ++
  (is.map fun i => reflCert (.down i) (.left i) (.join i)) ++
  (is.map fun i => reflCert (.down i) (.right i) (.join i)) ++
  (is.map fun i => reflCert .loop (.join i) (.hub i))

/-- Both orientations of the unique non-trivial peak for each gadget. -/
def peakCerts (n : Nat) : List (RawPeakCertificate (Node n) (Label n)) :=
  let is := indices n
  (is.map peakCertLR) ++ (is.map peakCertRL)

/-- Full raw certificate list before compression. -/
def rawCerts (n : Nat) : List (RawPeakCertificate (Node n) (Label n)) :=
  trivialCerts n ++ peakCerts n

private theorem mem_refl_peak_left (n : Nat) (i : Fin (n + 1)) :
    reflCert (.peak i) (.hub i) (.left i) ∈ rawCerts n := by
  unfold rawCerts trivialCerts peakCerts
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  exact List.mem_map.mpr ⟨i, mem_indices n i, rfl⟩

private theorem mem_refl_peak_right (n : Nat) (i : Fin (n + 1)) :
    reflCert (.peak i) (.hub i) (.right i) ∈ rawCerts n := by
  unfold rawCerts trivialCerts peakCerts
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨i, mem_indices n i, rfl⟩

private theorem mem_refl_down_left (n : Nat) (i : Fin (n + 1)) :
    reflCert (.down i) (.left i) (.join i) ∈ rawCerts n := by
  unfold rawCerts trivialCerts peakCerts
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨i, mem_indices n i, rfl⟩

private theorem mem_refl_down_right (n : Nat) (i : Fin (n + 1)) :
    reflCert (.down i) (.right i) (.join i) ∈ rawCerts n := by
  unfold rawCerts trivialCerts peakCerts
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨i, mem_indices n i, rfl⟩

private theorem mem_refl_loop (n : Nat) (i : Fin (n + 1)) :
    reflCert .loop (.join i) (.hub i) ∈ rawCerts n := by
  unfold rawCerts trivialCerts peakCerts
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨i, mem_indices n i, rfl⟩

private theorem mem_peakCertLR (n : Nat) (i : Fin (n + 1)) :
    peakCertLR i ∈ rawCerts n := by
  unfold rawCerts peakCerts
  apply List.mem_append.mpr
  right
  apply List.mem_append.mpr
  left
  exact List.mem_map.mpr ⟨i, mem_indices n i, rfl⟩

private theorem mem_peakCertRL (n : Nat) (i : Fin (n + 1)) :
    peakCertRL i ∈ rawCerts n := by
  unfold rawCerts peakCerts
  apply List.mem_append.mpr
  right
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨i, mem_indices n i, rfl⟩

private theorem reflCert_valid {n : Nat} {label : Label n} {source target : Node n}
    (hstep : LStep n label source target) :
    (reflCert label source target).Valid (LStep n) (LabelLt n) := by
  refine ⟨hstep, hstep, ?_⟩
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [reflCert, RawValleyCertificate.refl]
  · simp [reflCert, RawValleyCertificate.refl]
  · simp [reflCert, RawValleyCertificate.refl]
  · simp [reflCert, RawValleyCertificate.refl]

private theorem peakCertLR_valid {n : Nat} (i : Fin (n + 1)) :
    (peakCertLR i).Valid (LStep n) (LabelLt n) := by
  refine ⟨LStep.hub_to_left i, LStep.hub_to_right i, ?_⟩
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [peakCertLR, RawValleyCertificate.ofSingleSteps, PathData.Valid] using
      (show LStep n (.down i) (.left i) (.join i) ∧ True from ⟨LStep.left_to_join i, trivial⟩)
  · simpa [peakCertLR, RawValleyCertificate.ofSingleSteps, PathData.Valid] using
      (show LStep n (.down i) (.right i) (.join i) ∧ True from ⟨LStep.right_to_join i, trivial⟩)
  · simpa [peakCertLR, RawValleyCertificate.ofSingleSteps, PathData.LabelsSatisfy] using
      (show (LabelLt n (.down i) (.peak i) ∧ LabelLt n (.down i) (.peak i)) ∧ True from
        ⟨⟨down_lt_peak i, down_lt_peak i⟩, trivial⟩)
  · simpa [peakCertLR, RawValleyCertificate.ofSingleSteps, PathData.LabelsSatisfy] using
      (show (LabelLt n (.down i) (.peak i) ∧ LabelLt n (.down i) (.peak i)) ∧ True from
        ⟨⟨down_lt_peak i, down_lt_peak i⟩, trivial⟩)

private theorem peakCertRL_valid {n : Nat} (i : Fin (n + 1)) :
    (peakCertRL i).Valid (LStep n) (LabelLt n) := by
  refine ⟨LStep.hub_to_right i, LStep.hub_to_left i, ?_⟩
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [peakCertRL, RawValleyCertificate.ofSingleSteps, PathData.Valid] using
      (show LStep n (.down i) (.right i) (.join i) ∧ True from ⟨LStep.right_to_join i, trivial⟩)
  · simpa [peakCertRL, RawValleyCertificate.ofSingleSteps, PathData.Valid] using
      (show LStep n (.down i) (.left i) (.join i) ∧ True from ⟨LStep.left_to_join i, trivial⟩)
  · simpa [peakCertRL, RawValleyCertificate.ofSingleSteps, PathData.LabelsSatisfy] using
      (show (LabelLt n (.down i) (.peak i) ∧ LabelLt n (.down i) (.peak i)) ∧ True from
        ⟨⟨down_lt_peak i, down_lt_peak i⟩, trivial⟩)
  · simpa [peakCertRL, RawValleyCertificate.ofSingleSteps, PathData.LabelsSatisfy] using
      (show (LabelLt n (.down i) (.peak i) ∧ LabelLt n (.down i) (.peak i)) ∧ True from
        ⟨⟨down_lt_peak i, down_lt_peak i⟩, trivial⟩)

/-- Raw certificate package with automatically enumerated steps. -/
def rawStepCertificate (n : Nat) : RawCertifiedLocallyDecreasing (Node n) (Label n) :=
  RawCertifiedLocallyDecreasing.ofFinite (r := LStep n) (support n) (rawCerts n)

private theorem rawStepCertificate_valid (n : Nat) :
    (rawStepCertificate n).Valid (LStep n) (LabelLt n) := by
  refine ⟨RawCertifiedLocallyDecreasing.stepsSound_ofFinite (r := LStep n) (support n) (rawCerts n), ?_⟩
  intro s₁ s₂ hs₁ hs₂ hsame
  cases s₁ with
  | mk l₁ source₁ target₁ =>
      cases s₂ with
      | mk l₂ source₂ target₂ =>
          dsimp at hs₁ hs₂ hsame ⊢
          let hsound := RawCertifiedLocallyDecreasing.stepsSound_ofFinite
            (r := LStep n) (support n) (rawCerts n)
          have hstep₁ : LStep n l₁ source₁ target₁ :=
            hsound { label := l₁, source := source₁, target := target₁ } hs₁
          have hstep₂ : LStep n l₂ source₂ target₂ :=
            hsound { label := l₂, source := source₂, target := target₂ } hs₂
          cases hstep₁ with
          | hub_to_left i =>
              cases hstep₂ with
              | hub_to_left j =>
                  cases hsame
                  refine ⟨reflCert (.peak i) (.hub i) (.left i), ?_, ?_,
                    reflCert_valid (n := n) (LStep.hub_to_left i)⟩
                  · simpa [rawStepCertificate, RawCertifiedLocallyDecreasing.ofFinite] using
                      mem_refl_peak_left n i
                  · simp [RawPeakCertificate.MatchesSteps, reflCert]
              | hub_to_right j =>
                  cases hsame
                  refine ⟨peakCertLR i, ?_, ?_, peakCertLR_valid (n := n) i⟩
                  · simpa [rawStepCertificate, RawCertifiedLocallyDecreasing.ofFinite] using
                      mem_peakCertLR n i
                  · simp [RawPeakCertificate.MatchesSteps, peakCertLR]
              | left_to_join _ =>
                  cases hsame
              | right_to_join _ =>
                  cases hsame
              | join_to_hub _ =>
                  cases hsame
          | hub_to_right i =>
              cases hstep₂ with
              | hub_to_left j =>
                  cases hsame
                  refine ⟨peakCertRL i, ?_, ?_, peakCertRL_valid (n := n) i⟩
                  · simpa [rawStepCertificate, RawCertifiedLocallyDecreasing.ofFinite] using
                      mem_peakCertRL n i
                  · simp [RawPeakCertificate.MatchesSteps, peakCertRL]
              | hub_to_right j =>
                  cases hsame
                  refine ⟨reflCert (.peak i) (.hub i) (.right i), ?_, ?_,
                    reflCert_valid (n := n) (LStep.hub_to_right i)⟩
                  · simpa [rawStepCertificate, RawCertifiedLocallyDecreasing.ofFinite] using
                      mem_refl_peak_right n i
                  · simp [RawPeakCertificate.MatchesSteps, reflCert]
              | left_to_join _ =>
                  cases hsame
              | right_to_join _ =>
                  cases hsame
              | join_to_hub _ =>
                  cases hsame
          | left_to_join i =>
              cases hstep₂ with
              | left_to_join j =>
                  cases hsame
                  refine ⟨reflCert (.down i) (.left i) (.join i), ?_, ?_,
                    reflCert_valid (n := n) (LStep.left_to_join i)⟩
                  · simpa [rawStepCertificate, RawCertifiedLocallyDecreasing.ofFinite] using
                      mem_refl_down_left n i
                  · simp [RawPeakCertificate.MatchesSteps, reflCert]
              | hub_to_left _ =>
                  cases hsame
              | hub_to_right _ =>
                  cases hsame
              | right_to_join _ =>
                  cases hsame
              | join_to_hub _ =>
                  cases hsame
          | right_to_join i =>
              cases hstep₂ with
              | right_to_join j =>
                  cases hsame
                  refine ⟨reflCert (.down i) (.right i) (.join i), ?_, ?_,
                    reflCert_valid (n := n) (LStep.right_to_join i)⟩
                  · simpa [rawStepCertificate, RawCertifiedLocallyDecreasing.ofFinite] using
                      mem_refl_down_right n i
                  · simp [RawPeakCertificate.MatchesSteps, reflCert]
              | hub_to_left _ =>
                  cases hsame
              | hub_to_right _ =>
                  cases hsame
              | left_to_join _ =>
                  cases hsame
              | join_to_hub _ =>
                  cases hsame
          | join_to_hub i =>
              cases hstep₂ with
              | join_to_hub j =>
                  cases hsame
                  refine ⟨reflCert .loop (.join i) (.hub i), ?_, ?_,
                    reflCert_valid (n := n) (LStep.join_to_hub i)⟩
                  · simpa [rawStepCertificate, RawCertifiedLocallyDecreasing.ofFinite] using
                      mem_refl_loop n i
                  · simp [RawPeakCertificate.MatchesSteps, reflCert]
              | hub_to_left _ =>
                  cases hsame
              | hub_to_right _ =>
                  cases hsame
              | left_to_join _ =>
                  cases hsame
              | right_to_join _ =>
                  cases hsame

/-- Compact JSON for the uncompressed benchmark artifact. -/
def rawStepCertificateJson (n : Nat) : String :=
  RawCertifiedLocallyDecreasing.toJsonStringCompressed (rawStepCertificate n)

/-- Compressed certificate package used for exported artifacts. -/
def stepCertificate (n : Nat) : CompressedRawCertifiedLocallyDecreasing (Node n) (Label n) :=
  CompressedRawCertifiedLocallyDecreasing.ofRaw (rawStepCertificate n)

private theorem stepCertificate_valid (n : Nat) :
    (stepCertificate n).Valid (LStep n) (LabelLt n) :=
  CompressedRawCertifiedLocallyDecreasing.valid_of_ofRaw_valid
    (r := LStep n) (lt := LabelLt n) (rawStepCertificate_valid n)

private theorem stepCertificate_complete (n : Nat) :
    (stepCertificate n).StepsComplete (LStep n) := by
  simpa [stepCertificate, rawStepCertificate, CompressedRawCertifiedLocallyDecreasing.ofRaw,
    CompressedRawCertifiedLocallyDecreasing.StepsComplete] using
    (RawCertifiedLocallyDecreasing.stepsComplete_ofFinite (r := LStep n) (support n) (rawCerts n))

private theorem stepCertificate_check (n : Nat) :
    (stepCertificate n).check (r := LStep n) (lt := LabelLt n) = true :=
  (stepCertificate n).check_eq_true_of_valid (r := LStep n) (lt := LabelLt n) (stepCertificate_valid n)

/-- Compact JSON for the compressed exported artifact. -/
def stepCertificateJson (n : Nat) : String :=
  CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed (stepCertificate n)

/-- Summary statistics for a family instance. -/
structure FamilyStats where
  steps : Nat
  rawCerts : Nat
  compressedCerts : Nat
  rawJsonBytes : Nat
  compressedJsonBytes : Nat
  deriving Repr

/-- Exact artifact sizes for instance `n`. -/
def stats (n : Nat) : FamilyStats where
  steps := (stepCertificate n).steps.length
  rawCerts := (rawStepCertificate n).certs.length
  compressedCerts := (stepCertificate n).certs.length
  rawJsonBytes := (rawStepCertificateJson n).utf8ByteSize
  compressedJsonBytes := (stepCertificateJson n).utf8ByteSize

private theorem stepCertificateJson0_parses :
    CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node 0) (L := Label 0)
      (stepCertificateJson 0) = Except.ok (stepCertificate 0) := by
  native_decide

theorem stepCertificateJson0_checks :
    CompressedRawCertifiedLocallyDecreasing.checkJson (α := Node 0) (L := Label 0)
      (r := LStep 0) (lt := LabelLt 0) (stepCertificateJson 0) = Except.ok true :=
  CompressedRawCertifiedLocallyDecreasing.checkJson_eq_ok_true_of_parseJson_eq_ok
    (r := LStep 0) (lt := LabelLt 0) stepCertificateJson0_parses (stepCertificate_check 0)

private theorem stepCertificateJson5_parses :
    CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node 5) (L := Label 5)
      (stepCertificateJson 5) = Except.ok (stepCertificate 5) := by
  native_decide

theorem stepCertificateJson5_checks :
    CompressedRawCertifiedLocallyDecreasing.checkJson (α := Node 5) (L := Label 5)
      (r := LStep 5) (lt := LabelLt 5) (stepCertificateJson 5) = Except.ok true :=
  CompressedRawCertifiedLocallyDecreasing.checkJson_eq_ok_true_of_parseJson_eq_ok
    (r := LStep 5) (lt := LabelLt 5) stepCertificateJson5_parses (stepCertificate_check 5)

/-- External compressed JSON artifact for the `n = 0` family instance. -/
def stepCertificateFileJson0 : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "family-0.json"

theorem stepCertificateFileJson0_eq_stepCertificateJson :
    stepCertificateFileJson0 = stepCertificateJson 0 := by
  native_decide

private theorem stepCertificateFileJson0_parses :
    CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node 0) (L := Label 0)
      stepCertificateFileJson0 = Except.ok (stepCertificate 0) := by
  simpa [stepCertificateFileJson0_eq_stepCertificateJson] using stepCertificateJson0_parses

theorem stepCertificateFileJson0_checks :
    CompressedRawCertifiedLocallyDecreasing.checkJson (α := Node 0) (L := Label 0)
      (r := LStep 0) (lt := LabelLt 0) stepCertificateFileJson0 = Except.ok true := by
  simpa [stepCertificateFileJson0_eq_stepCertificateJson] using stepCertificateJson0_checks

/-- External compressed JSON artifact for the `n = 5` family instance. -/
def stepCertificateFileJson5 : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "family-5.json"

theorem stepCertificateFileJson5_eq_stepCertificateJson :
    stepCertificateFileJson5 = stepCertificateJson 5 := by
  native_decide

private theorem stepCertificateFileJson5_parses :
    CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node 5) (L := Label 5)
      stepCertificateFileJson5 = Except.ok (stepCertificate 5) := by
  simpa [stepCertificateFileJson5_eq_stepCertificateJson] using stepCertificateJson5_parses

theorem stepCertificateFileJson5_checks :
    CompressedRawCertifiedLocallyDecreasing.checkJson (α := Node 5) (L := Label 5)
      (r := LStep 5) (lt := LabelLt 5) stepCertificateFileJson5 = Except.ok true := by
  simpa [stepCertificateFileJson5_eq_stepCertificateJson] using stepCertificateJson5_checks

/-! ## Confluence -/

/-- The family is locally decreasing with respect to `LabelLt`. -/
theorem step_locallyDecreasing (n : Nat) : LocallyDecreasing (LStep n) (LabelLt n) :=
  (stepCertificate n).sound (r := LStep n) (lt := LabelLt n)
    (stepCertificate_valid n) (stepCertificate_complete n)

/-- Confluence via the compressed decreasing-diagram certificate family. -/
theorem step_confluent (n : Nat) : Confluent (Step n) :=
  (stepCertificate n).confluent_of_valid (r := LStep n) (lt := LabelLt n)
    (labelLt_wf n) (stepCertificate_valid n) (stepCertificate_complete n)

/-- Confluence of the `n = 0` family instance via the checked repository artifact. -/
theorem step0_confluent_via_file : Confluent (Step 0) :=
  CompressedRawCertifiedLocallyDecreasing.confluent_of_parseJson_eq_ok
    (r := LStep 0) (lt := LabelLt 0) (labelLt_wf 0)
    stepCertificateFileJson0_parses (stepCertificate_valid 0) (stepCertificate_complete 0)

/-- Confluence of the `n = 5` family instance via the checked repository artifact. -/
theorem step5_confluent_via_file : Confluent (Step 5) :=
  CompressedRawCertifiedLocallyDecreasing.confluent_of_parseJson_eq_ok
    (r := LStep 5) (lt := LabelLt 5) (labelLt_wf 5)
    stepCertificateFileJson5_parses (stepCertificate_valid 5) (stepCertificate_complete 5)

end Metatheory.RewritingFamily
