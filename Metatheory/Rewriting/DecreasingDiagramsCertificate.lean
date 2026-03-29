/- 
# Decreasing Diagrams Certificates

This module adds an explicit certification layer on top of
`Metatheory.Rewriting.DecreasingDiagrams`.

The core objects are:

- `PathData`: concrete labeled paths recorded as lists of `(label, target)` pairs
- `ValleyCertificate`: an explicit decreasing valley for one local peak
- `PeakCertificate`: one certified local peak
- `CertifiedLocallyDecreasing`: a finite family of certified peaks covering every
  one-step peak of the labeled system
- `RawValleyCertificate` / `RawPeakCertificate`: proof-free certificate data
- `RawCertifiedLocallyDecreasing`: finite raw data plus a boolean checker

The main soundness theorem turns a finite family of explicit local certificates
into `LocallyDecreasing`, and hence confluence of the unlabeled relation.

For raw certificates, the executable checker only validates finite data:
the listed steps are real, and every local peak over the listed step set is
covered by a valid raw certificate. A separate `StepsComplete` proof states that
the chosen step list actually enumerates every real one-step reduction. This
split is essential because generic step completeness is not decidable on
infinite state spaces.
-/

import Lean.Data.Json
import Metatheory.Rewriting.DecreasingDiagrams

namespace Rewriting

universe u v

open Lean

/-- Concrete path data: each entry stores a label and the next node reached by that step. -/
abbrev PathData (α : Type u) (L : Type v) := List (L × α)

namespace PathData

variable {α : Type u} {L : Type v}

/-- Endpoint of a concrete path, starting from `start`. -/
def target (start : α) : PathData α L → α
  | [] => start
  | (_, next) :: rest => target next rest

/-- Concrete path validity with respect to a labeled relation. -/
def Valid (r : LabeledARS α L) : α → PathData α L → Prop
  | _, [] => True
  | start, (l, next) :: rest => r l start next ∧ Valid r next rest

/-- All labels in the path satisfy predicate `P`. -/
def LabelsSatisfy (P : L → Prop) : PathData α L → Prop
  | [] => True
  | (l, _) :: rest => P l ∧ LabelsSatisfy P rest

@[simp] theorem target_nil (start : α) :
    target start ([] : PathData α L) = start :=
  rfl

@[simp] theorem target_cons (start : α) (l : L) (next : α) (rest : PathData α L) :
    target start ((l, next) :: rest) = target next rest :=
  rfl

@[simp] theorem valid_nil (r : LabeledARS α L) (start : α) :
    Valid r start ([] : PathData α L) :=
  trivial

@[simp] theorem valid_cons (r : LabeledARS α L) (start : α) (l : L) (next : α)
    (rest : PathData α L) :
    Valid r start ((l, next) :: rest) ↔ r l start next ∧ Valid r next rest :=
  Iff.rfl

@[simp] theorem labelsSatisfy_nil (P : L → Prop) :
    LabelsSatisfy P ([] : PathData α L) :=
  trivial

@[simp] theorem labelsSatisfy_cons (P : L → Prop) (l : L) (next : α)
    (rest : PathData α L) :
    LabelsSatisfy P ((l, next) :: rest) ↔ P l ∧ LabelsSatisfy P rest :=
  Iff.rfl

instance instDecidableValid {r : LabeledARS α L} [∀ l a b, Decidable (r l a b)] :
    ∀ (start : α) (path : PathData α L), Decidable (Valid r start path)
  | _, [] => isTrue trivial
  | start, (l, next) :: rest =>
      match (inferInstance : Decidable (r l start next)), instDecidableValid next rest with
      | isTrue hstep, isTrue hrest => isTrue ⟨hstep, hrest⟩
      | isFalse hstep, _ => isFalse (fun h => hstep h.1)
      | _, isFalse hrest => isFalse (fun h => hrest h.2)

instance instDecidableLabelsSatisfy {P : L → Prop} [DecidablePred P] :
    ∀ (path : PathData α L), Decidable (LabelsSatisfy P path)
  | [] => isTrue trivial
  | (l, _) :: rest =>
      match (inferInstance : Decidable (P l)), instDecidableLabelsSatisfy rest with
      | isTrue hl, isTrue hrest => isTrue ⟨hl, hrest⟩
      | isFalse hl, _ => isFalse (fun h => hl h.1)
      | _, isFalse hrest => isFalse (fun h => hrest h.2)

/-- Soundness of explicit path data: a valid decreasing path yields `StarPred`. -/
theorem toStarPred {r : LabeledARS α L} {P : L → Prop} :
    ∀ {start : α} (path : PathData α L),
      Valid r start path →
      LabelsSatisfy P path →
      StarPred r P start (target start path)
  | start, [] => by
      intro _ _
      exact StarPred.refl start
  | start, (l, next) :: rest => by
      intro hvalid hlabels
      rcases hvalid with ⟨hstep, hvalidRest⟩
      rcases hlabels with ⟨hl, hlabelsRest⟩
      have hhead : StarPred r P start next := StarPred.single l hl hstep
      have hrest : StarPred r P next (target next rest) :=
        toStarPred rest hvalidRest hlabelsRest
      simpa using StarPred.trans hhead hrest

/-- Forgetting label restrictions turns a concrete valid path into `Star`. -/
theorem toStar {r : LabeledARS α L} :
    ∀ {start : α} (path : PathData α L),
      Valid r start path →
      Star (LabeledUnion r) start (target start path)
  | start, [] => by
      intro _
      exact Star.refl start
  | start, (l, next) :: rest => by
      intro hvalid
      rcases hvalid with ⟨hstep, hvalidRest⟩
      have hhead : Star (LabeledUnion r) start next := Star.single ⟨l, hstep⟩
      have hrest : Star (LabeledUnion r) next (target next rest) := toStar rest hvalidRest
      simpa using Star.trans hhead hrest

/-- Swap the two conjuncts in a path-wide label constraint. -/
theorem labelsSatisfy_swapConj {lt : L → L → Prop} {l₁ l₂ : L} :
    ∀ {path : PathData α L},
      LabelsSatisfy (fun l => lt l l₁ ∧ lt l l₂) path →
      LabelsSatisfy (fun l => lt l l₂ ∧ lt l l₁) path
  | [] => by
      intro _
      trivial
  | (_, _) :: rest => by
      intro h
      rcases h with ⟨hhead, hrest⟩
      exact ⟨And.symm hhead, labelsSatisfy_swapConj hrest⟩

end PathData

/-- An explicit decreasing valley closing one local peak. -/
structure ValleyCertificate {α : Type u} {L : Type v}
    (r : LabeledARS α L) (lt : L → L → Prop)
    (leftStart rightStart : α) (l₁ l₂ : L) where
  join : α
  leftPath : PathData α L
  rightPath : PathData α L
  leftTarget : PathData.target leftStart leftPath = join
  rightTarget : PathData.target rightStart rightPath = join
  leftValid : PathData.Valid r leftStart leftPath
  rightValid : PathData.Valid r rightStart rightPath
  leftSmall : PathData.LabelsSatisfy (fun l => lt l l₁ ∧ lt l l₂) leftPath
  rightSmall : PathData.LabelsSatisfy (fun l => lt l l₁ ∧ lt l l₂) rightPath

namespace ValleyCertificate

variable {α : Type u} {L : Type v}
variable {r : LabeledARS α L} {lt : L → L → Prop}

/-- Trivial valley certificate: both sides are already at the common join. -/
def refl (a : α) (l₁ l₂ : L) : ValleyCertificate r lt a a l₁ l₂ where
  join := a
  leftPath := []
  rightPath := []
  leftTarget := rfl
  rightTarget := rfl
  leftValid := by simp [PathData.Valid]
  rightValid := by simp [PathData.Valid]
  leftSmall := by simp [PathData.LabelsSatisfy]
  rightSmall := by simp [PathData.LabelsSatisfy]

/-- One-step decreasing valley certificate on each side. -/
def ofSingleSteps {b c d : α} {m n l₁ l₂ : L}
    (hbd : r m b d) (hcd : r n c d)
    (hmSmall : lt m l₁ ∧ lt m l₂) (hnSmall : lt n l₁ ∧ lt n l₂) :
    ValleyCertificate r lt b c l₁ l₂ where
  join := d
  leftPath := [(m, d)]
  rightPath := [(n, d)]
  leftTarget := rfl
  rightTarget := rfl
  leftValid := by
    exact ⟨hbd, by simp [PathData.Valid]⟩
  rightValid := by
    exact ⟨hcd, by simp [PathData.Valid]⟩
  leftSmall := by
    exact ⟨hmSmall, by simp [PathData.LabelsSatisfy]⟩
  rightSmall := by
    exact ⟨hnSmall, by simp [PathData.LabelsSatisfy]⟩

/-- Soundness of a certified valley. -/
theorem sound {leftStart rightStart : α} {l₁ l₂ : L}
    (cert : ValleyCertificate r lt leftStart rightStart l₁ l₂) :
    ∃ d, StarPred r (fun l => lt l l₁ ∧ lt l l₂) leftStart d ∧
         StarPred r (fun l => lt l l₁ ∧ lt l l₂) rightStart d := by
  refine ⟨cert.join, ?_, ?_⟩
  ·
    have hleft :=
      PathData.toStarPred (r := r) (P := fun l => lt l l₁ ∧ lt l l₂)
        (start := leftStart) cert.leftPath cert.leftValid cert.leftSmall
    simpa [cert.leftTarget] using hleft
  ·
    have hright :=
      PathData.toStarPred (r := r) (P := fun l => lt l l₁ ∧ lt l l₂)
        (start := rightStart) cert.rightPath cert.rightValid cert.rightSmall
    simpa [cert.rightTarget] using hright

end ValleyCertificate

/-- One certified local peak together with its explicit decreasing valley. -/
structure PeakCertificate {α : Type u} {L : Type v}
    (r : LabeledARS α L) (lt : L → L → Prop) where
  source : α
  leftLabel : L
  leftTarget : α
  rightLabel : L
  rightTarget : α
  leftStep : r leftLabel source leftTarget
  rightStep : r rightLabel source rightTarget
  valley : ValleyCertificate r lt leftTarget rightTarget leftLabel rightLabel

namespace PeakCertificate

variable {α : Type u} {L : Type v}
variable {r : LabeledARS α L} {lt : L → L → Prop}

/-- Soundness of one certified peak. -/
theorem sound (cert : PeakCertificate r lt) :
    ∃ d, StarPred r (fun l => lt l cert.leftLabel ∧ lt l cert.rightLabel) cert.leftTarget d ∧
         StarPred r (fun l => lt l cert.leftLabel ∧ lt l cert.rightLabel) cert.rightTarget d :=
  cert.valley.sound

end PeakCertificate

/-- A finite family of explicit decreasing-diagram certificates covering all local peaks. -/
structure CertifiedLocallyDecreasing {α : Type u} {L : Type v}
    (r : LabeledARS α L) (lt : L → L → Prop) where
  certs : List (PeakCertificate r lt)
  complete :
    ∀ a b c l₁ l₂, r l₁ a b → r l₂ a c →
      ∃ cert ∈ certs,
        cert.source = a ∧
        cert.leftLabel = l₁ ∧
        cert.leftTarget = b ∧
        cert.rightLabel = l₂ ∧
        cert.rightTarget = c

namespace CertifiedLocallyDecreasing

variable {α : Type u} {L : Type v}
variable {r : LabeledARS α L} {lt : L → L → Prop}

/-- A complete family of certified peaks yields local decreasing. -/
theorem sound (cert : CertifiedLocallyDecreasing r lt) : LocallyDecreasing r lt := by
  intro a b c l₁ l₂ hab hac
  rcases cert.complete a b c l₁ l₂ hab hac with
    ⟨peakCert, _, hSource, hLeftLabel, hLeftTarget, hRightLabel, hRightTarget⟩
  subst hSource
  subst hLeftLabel
  subst hLeftTarget
  subst hRightLabel
  subst hRightTarget
  exact peakCert.valley.sound

end CertifiedLocallyDecreasing

/-- Confluence from an explicit decreasing-diagram certificate family. -/
theorem confluent_of_certificate {α : Type u} {L : Type v}
    {r : LabeledARS α L} {lt : L → L → Prop}
    (wf : WellFounded lt) (cert : CertifiedLocallyDecreasing r lt) :
    Confluent (LabeledUnion r) :=
  confluent_of_locallyDecreasing (r := r) (lt := lt) wf cert.sound

/-- Church-Rosser phrasing of certified decreasing diagrams confluence. -/
theorem church_rosser_of_certificate {α : Type u} {L : Type v}
    {r : LabeledARS α L} {lt : L → L → Prop}
    (wf : WellFounded lt) (cert : CertifiedLocallyDecreasing r lt) :
    Metatheory (LabeledUnion r) :=
  confluent_of_certificate (r := r) (lt := lt) wf cert

/-! ## Raw Checkable Certificates -/

/-- One concrete labeled step, used to enumerate all local peaks of a finite system. -/
structure StepTriple (α : Type u) (L : Type v) where
  label : L
  source : α
  target : α
  deriving DecidableEq, Repr

instance {α : Type} {L : Type} [FromJson α] [FromJson L] : FromJson (StepTriple α L) where
  fromJson? j := do
    let label ← j.getObjValAs? L "label"
    let source ← j.getObjValAs? α "source"
    let target ← j.getObjValAs? α "target"
    pure { label, source, target }

instance {α : Type} {L : Type} [ToJson α] [ToJson L] : ToJson (StepTriple α L) where
  toJson step := Json.mkObj [
    ("label", toJson step.label),
    ("source", toJson step.source),
    ("target", toJson step.target)
  ]

/-- Finite support for the nodes and labels of a labeled ARS. -/
structure FiniteLabeledARS (α : Type u) (L : Type v) where
  nodes : List α
  labels : List L
  nodesComplete : ∀ a, a ∈ nodes
  labelsComplete : ∀ l, l ∈ labels

namespace FiniteLabeledARS

variable {α : Type u} {L : Type v}

/-- Enumerate all targets reachable from a fixed labeled source step. -/
def enumerateTargets (r : LabeledARS α L) [∀ l a b, Decidable (r l a b)]
    (l : L) (source : α) : List α → List (StepTriple α L)
  | [] => []
  | target :: targets =>
      if _h : r l source target then
        { label := l, source := source, target := target } :: enumerateTargets r l source targets
      else
        enumerateTargets r l source targets

/-- Enumerate all labeled steps with a fixed label. -/
def enumerateSources (r : LabeledARS α L) [∀ l a b, Decidable (r l a b)]
    (l : L) : List α → List α → List (StepTriple α L)
  | [], _ => []
  | source :: sources, nodes =>
      enumerateTargets r l source nodes ++ enumerateSources r l sources nodes

/-- Enumerate all labeled steps of a finite labeled ARS. -/
def enumerateLabels (r : LabeledARS α L) [∀ l a b, Decidable (r l a b)]
    : List L → List α → List (StepTriple α L)
  | [], _ => []
  | l :: labels, nodes =>
      enumerateSources r l nodes nodes ++ enumerateLabels r labels nodes

/-- Full step enumeration induced by the finite node and label support. -/
def enumerateSteps (support : FiniteLabeledARS α L) (r : LabeledARS α L)
    [∀ l a b, Decidable (r l a b)] : List (StepTriple α L) :=
  enumerateLabels r support.labels support.nodes

section EnumerationProofs

variable {r : LabeledARS α L}
variable [∀ l a b, Decidable (r l a b)]

theorem enumerateTargets_sound {l : L} {source : α} {targets : List α}
    {step : StepTriple α L} :
    step ∈ enumerateTargets r l source targets →
      r step.label step.source step.target := by
  induction targets with
  | nil =>
      simp [enumerateTargets]
  | cons target targets ih =>
      by_cases hstep : r l source target
      · simp [enumerateTargets, hstep]
        intro hmem
        rcases hmem with rfl | hmem
        · exact hstep
        · exact ih hmem
      · simp [enumerateTargets, hstep]
        exact ih

theorem mem_enumerateTargets {l : L} {source target : α} {targets : List α}
    (htarget : target ∈ targets) (hstep : r l source target) :
    { label := l, source := source, target := target } ∈ enumerateTargets r l source targets := by
  induction targets with
  | nil =>
      cases htarget
  | cons target' targets ih =>
      simp at htarget
      rcases htarget with rfl | htarget
      · simp [enumerateTargets, hstep]
      · by_cases hhead : r l source target'
        · simp [enumerateTargets, hhead, ih htarget]
        · simp [enumerateTargets, hhead, ih htarget]

theorem enumerateSources_sound {l : L} {sources nodes : List α}
    {step : StepTriple α L} :
    step ∈ enumerateSources r l sources nodes →
      r step.label step.source step.target := by
  induction sources with
  | nil =>
      simp [enumerateSources]
  | cons source sources ih =>
      simp [enumerateSources]
      intro hmem
      rcases hmem with hmem | hmem
      · exact enumerateTargets_sound (r := r) hmem
      · exact ih hmem

theorem mem_enumerateSources {l : L} {source target : α} {sources nodes : List α}
    (hsource : source ∈ sources) (htarget : target ∈ nodes) (hstep : r l source target) :
    { label := l, source := source, target := target } ∈ enumerateSources r l sources nodes := by
  induction sources with
  | nil =>
      cases hsource
  | cons source' sources ih =>
      simp at hsource
      rcases hsource with rfl | hsource
      · simp [enumerateSources, mem_enumerateTargets (r := r) htarget hstep]
      · simp [enumerateSources, ih hsource]

theorem enumerateLabels_sound {labels : List L} {nodes : List α} {step : StepTriple α L} :
    step ∈ enumerateLabels r labels nodes →
      r step.label step.source step.target := by
  induction labels with
  | nil =>
      simp [enumerateLabels]
  | cons l labels ih =>
      simp [enumerateLabels]
      intro hmem
      rcases hmem with hmem | hmem
      · exact enumerateSources_sound (r := r) hmem
      · exact ih hmem

theorem mem_enumerateLabels {l : L} {source target : α} {labels : List L} {nodes : List α}
    (hl : l ∈ labels) (hsource : source ∈ nodes) (htarget : target ∈ nodes)
    (hstep : r l source target) :
    { label := l, source := source, target := target } ∈ enumerateLabels r labels nodes := by
  induction labels with
  | nil =>
      cases hl
  | cons l' labels ih =>
      simp at hl
      rcases hl with rfl | hl
      · simp [enumerateLabels, mem_enumerateSources (r := r) hsource htarget hstep]
      · simp [enumerateLabels, ih hl]

end EnumerationProofs

theorem enumerateSteps_sound {support : FiniteLabeledARS α L} {r : LabeledARS α L}
    [∀ l a b, Decidable (r l a b)] {step : StepTriple α L}
    (hmem : step ∈ support.enumerateSteps r) :
    r step.label step.source step.target :=
  enumerateLabels_sound (r := r) hmem

theorem mem_enumerateSteps {support : FiniteLabeledARS α L} {r : LabeledARS α L}
    [∀ l a b, Decidable (r l a b)] {a b : α} {l : L}
    (hstep : r l a b) :
    { label := l, source := a, target := b } ∈ support.enumerateSteps r :=
  mem_enumerateLabels (r := r) (support.labelsComplete l)
    (support.nodesComplete a) (support.nodesComplete b) hstep

end FiniteLabeledARS

/-- Raw decreasing valley data with no proof fields. -/
structure RawValleyCertificate (α : Type u) (L : Type v) where
  join : α
  leftPath : PathData α L
  rightPath : PathData α L
  deriving DecidableEq, Repr

instance {α : Type} {L : Type} [FromJson α] [FromJson L] :
    FromJson (RawValleyCertificate α L) where
  fromJson? j := do
    let join ← j.getObjValAs? α "join"
    let leftPath ← j.getObjValAs? (PathData α L) "leftPath"
    let rightPath ← j.getObjValAs? (PathData α L) "rightPath"
    pure { join, leftPath, rightPath }

instance {α : Type} {L : Type} [ToJson α] [ToJson L] :
    ToJson (RawValleyCertificate α L) where
  toJson cert := Json.mkObj [
    ("join", toJson cert.join),
    ("leftPath", toJson cert.leftPath),
    ("rightPath", toJson cert.rightPath)
  ]

namespace RawValleyCertificate

variable {α : Type u} {L : Type v}
variable {r : LabeledARS α L} {lt : L → L → Prop}

/-- Swap the two sides of a raw valley certificate. -/
def swap (cert : RawValleyCertificate α L) : RawValleyCertificate α L where
  join := cert.join
  leftPath := cert.rightPath
  rightPath := cert.leftPath

/-- Raw valley certificates are valid when their paths meet at the claimed join
    and all labels are strictly smaller than both peak labels. -/
def Valid (cert : RawValleyCertificate α L)
    (r : LabeledARS α L) (lt : L → L → Prop)
    (leftStart rightStart : α) (l₁ l₂ : L) : Prop :=
  PathData.target leftStart cert.leftPath = cert.join ∧
  PathData.target rightStart cert.rightPath = cert.join ∧
  PathData.Valid r leftStart cert.leftPath ∧
  PathData.Valid r rightStart cert.rightPath ∧
  PathData.LabelsSatisfy (fun l => lt l l₁ ∧ lt l l₂) cert.leftPath ∧
  PathData.LabelsSatisfy (fun l => lt l l₁ ∧ lt l l₂) cert.rightPath

instance instDecidableValid [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (cert : RawValleyCertificate α L) (leftStart rightStart : α) (l₁ l₂ : L) :
    Decidable (cert.Valid r lt leftStart rightStart l₁ l₂) := by
  unfold RawValleyCertificate.Valid
  infer_instance

/-- Empty raw valley on both sides. -/
def refl (a : α) : RawValleyCertificate α L where
  join := a
  leftPath := []
  rightPath := []

/-- One-step raw valley on each side. -/
def ofSingleSteps (d : α) (m n : L) : RawValleyCertificate α L where
  join := d
  leftPath := [(m, d)]
  rightPath := [(n, d)]

/-- Turn raw valley data plus its validator proof into a proof-carrying certificate. -/
def toCertificate {leftStart rightStart : α} {l₁ l₂ : L}
    (cert : RawValleyCertificate α L)
    (hvalid : cert.Valid r lt leftStart rightStart l₁ l₂) :
    ValleyCertificate r lt leftStart rightStart l₁ l₂ := by
  rcases hvalid with ⟨hleftTarget, hrightTarget, hleftValid, hrightValid, hleftSmall, hrightSmall⟩
  exact
    { join := cert.join
      leftPath := cert.leftPath
      rightPath := cert.rightPath
      leftTarget := hleftTarget
      rightTarget := hrightTarget
      leftValid := hleftValid
      rightValid := hrightValid
      leftSmall := hleftSmall
      rightSmall := hrightSmall }

/-- Soundness of a raw valley certificate. -/
theorem sound {leftStart rightStart : α} {l₁ l₂ : L}
    (cert : RawValleyCertificate α L)
    (hvalid : cert.Valid r lt leftStart rightStart l₁ l₂) :
    ∃ d, StarPred r (fun l => lt l l₁ ∧ lt l l₂) leftStart d ∧
         StarPred r (fun l => lt l l₁ ∧ lt l l₂) rightStart d :=
  (cert.toCertificate (r := r) (lt := lt) hvalid).sound

/-- Boolean checker for raw valley certificates. -/
def check [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (cert : RawValleyCertificate α L) (leftStart rightStart : α) (l₁ l₂ : L) : Bool :=
  decide (cert.Valid r lt leftStart rightStart l₁ l₂)

theorem valid_of_check_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {cert : RawValleyCertificate α L} {leftStart rightStart : α} {l₁ l₂ : L}
    (hcheck : cert.check (r := r) (lt := lt) leftStart rightStart l₁ l₂ = true) :
    cert.Valid r lt leftStart rightStart l₁ l₂ := by
  have hdec : decide (cert.Valid r lt leftStart rightStart l₁ l₂) = true := by
    simpa [RawValleyCertificate.check] using hcheck
  exact of_decide_eq_true hdec

theorem check_eq_true_of_valid [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {cert : RawValleyCertificate α L} {leftStart rightStart : α} {l₁ l₂ : L}
    (hvalid : cert.Valid r lt leftStart rightStart l₁ l₂) :
    cert.check (r := r) (lt := lt) leftStart rightStart l₁ l₂ = true := by
  exact decide_eq_true_eq.mpr hvalid

/-- Swapping the two sides preserves raw valley validity. -/
theorem valid_swap {cert : RawValleyCertificate α L} {leftStart rightStart : α} {l₁ l₂ : L}
    (hvalid : cert.Valid r lt leftStart rightStart l₁ l₂) :
    cert.swap.Valid r lt rightStart leftStart l₂ l₁ := by
  rcases hvalid with ⟨hleftTarget, hrightTarget, hleftValid, hrightValid, hleftSmall, hrightSmall⟩
  exact ⟨hrightTarget, hleftTarget, hrightValid, hleftValid,
    PathData.labelsSatisfy_swapConj hrightSmall,
    PathData.labelsSatisfy_swapConj hleftSmall⟩

end RawValleyCertificate

/-- Raw local-peak certificate with no embedded proofs. -/
structure RawPeakCertificate (α : Type u) (L : Type v) where
  source : α
  leftLabel : L
  leftTarget : α
  rightLabel : L
  rightTarget : α
  valley : RawValleyCertificate α L
  deriving DecidableEq, Repr

instance {α : Type} {L : Type} [FromJson α] [FromJson L] :
    FromJson (RawPeakCertificate α L) where
  fromJson? j := do
    let source ← j.getObjValAs? α "source"
    let leftLabel ← j.getObjValAs? L "leftLabel"
    let leftTarget ← j.getObjValAs? α "leftTarget"
    let rightLabel ← j.getObjValAs? L "rightLabel"
    let rightTarget ← j.getObjValAs? α "rightTarget"
    let valley ← j.getObjValAs? (RawValleyCertificate α L) "valley"
    pure { source, leftLabel, leftTarget, rightLabel, rightTarget, valley }

instance {α : Type} {L : Type} [ToJson α] [ToJson L] :
    ToJson (RawPeakCertificate α L) where
  toJson cert := Json.mkObj [
    ("source", toJson cert.source),
    ("leftLabel", toJson cert.leftLabel),
    ("leftTarget", toJson cert.leftTarget),
    ("rightLabel", toJson cert.rightLabel),
    ("rightTarget", toJson cert.rightTarget),
    ("valley", toJson cert.valley)
  ]

namespace RawPeakCertificate

variable {α : Type u} {L : Type v}
variable {r : LabeledARS α L} {lt : L → L → Prop}

/-- The left source step encoded by a raw peak certificate. -/
def leftStep (cert : RawPeakCertificate α L) : StepTriple α L :=
  { label := cert.leftLabel, source := cert.source, target := cert.leftTarget }

/-- The right source step encoded by a raw peak certificate. -/
def rightStep (cert : RawPeakCertificate α L) : StepTriple α L :=
  { label := cert.rightLabel, source := cert.source, target := cert.rightTarget }

/-- Swap the two sides of a raw peak certificate. -/
def swap (cert : RawPeakCertificate α L) : RawPeakCertificate α L where
  source := cert.source
  leftLabel := cert.rightLabel
  leftTarget := cert.rightTarget
  rightLabel := cert.leftLabel
  rightTarget := cert.leftTarget
  valley := cert.valley.swap

/-- Field-by-field match between a raw certificate and a concrete pair of steps. -/
def MatchesSteps (cert : RawPeakCertificate α L) (s₁ s₂ : StepTriple α L) : Prop :=
  cert.source = s₁.source ∧
  cert.leftLabel = s₁.label ∧
  cert.leftTarget = s₁.target ∧
  cert.rightLabel = s₂.label ∧
  cert.rightTarget = s₂.target

theorem leftStep_eq_of_matches {cert : RawPeakCertificate α L} {s₁ s₂ : StepTriple α L}
    (hmatch : cert.MatchesSteps s₁ s₂) :
    cert.leftStep = s₁ := by
  cases s₁ with
  | mk label source target =>
      rcases hmatch with ⟨hsource, hleftLabel, hleftTarget, _, _⟩
      cases hsource
      cases hleftLabel
      cases hleftTarget
      rfl

theorem rightStep_eq_of_matches {cert : RawPeakCertificate α L} {s₁ s₂ : StepTriple α L}
    (hsame : s₁.source = s₂.source)
    (hmatch : cert.MatchesSteps s₁ s₂) :
    cert.rightStep = s₂ := by
  cases s₂ with
  | mk label source target =>
      rcases hmatch with ⟨hsource, _, _, hrightLabel, hrightTarget⟩
      have hsource' : cert.source = source := hsource.trans hsame
      cases hsource'
      cases hrightLabel
      cases hrightTarget
      rfl

theorem matches_swap {cert : RawPeakCertificate α L} {s₁ s₂ : StepTriple α L}
    (hsame : s₁.source = s₂.source)
    (hmatch : cert.MatchesSteps s₁ s₂) :
    cert.swap.MatchesSteps s₂ s₁ := by
  rcases hmatch with ⟨hsource, hleftLabel, hleftTarget, hrightLabel, hrightTarget⟩
  exact ⟨hsource.trans hsame, hrightLabel, hrightTarget, hleftLabel, hleftTarget⟩

instance instDecidableMatchesSteps [DecidableEq α] [DecidableEq L]
    (cert : RawPeakCertificate α L) (s₁ s₂ : StepTriple α L) :
    Decidable (cert.MatchesSteps s₁ s₂) := by
  unfold RawPeakCertificate.MatchesSteps
  infer_instance

/-- Raw peak validity: both source steps are real and the closing valley is valid. -/
def Valid (cert : RawPeakCertificate α L) (r : LabeledARS α L) (lt : L → L → Prop) : Prop :=
  r cert.leftLabel cert.source cert.leftTarget ∧
  r cert.rightLabel cert.source cert.rightTarget ∧
  cert.valley.Valid r lt cert.leftTarget cert.rightTarget cert.leftLabel cert.rightLabel

instance instDecidableValid [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (cert : RawPeakCertificate α L) :
    Decidable (cert.Valid r lt) := by
  unfold RawPeakCertificate.Valid
  infer_instance

/-- Turn raw peak data plus its validator proof into a proof-carrying certificate. -/
def toCertificate (cert : RawPeakCertificate α L) (hvalid : cert.Valid r lt) :
    PeakCertificate r lt := by
  rcases hvalid with ⟨hleftStep, hrightStep, hvalley⟩
  exact
    { source := cert.source
      leftLabel := cert.leftLabel
      leftTarget := cert.leftTarget
      rightLabel := cert.rightLabel
      rightTarget := cert.rightTarget
      leftStep := hleftStep
      rightStep := hrightStep
      valley := cert.valley.toCertificate (r := r) (lt := lt) hvalley }

/-- Soundness of raw peak certificates. -/
theorem sound (cert : RawPeakCertificate α L) (hvalid : cert.Valid r lt) :
    ∃ d, StarPred r (fun l => lt l cert.leftLabel ∧ lt l cert.rightLabel) cert.leftTarget d ∧
         StarPred r (fun l => lt l cert.leftLabel ∧ lt l cert.rightLabel) cert.rightTarget d := by
  rcases hvalid with ⟨_, _, hvalley⟩
  exact cert.valley.sound (r := r) (lt := lt) hvalley

/-- Boolean checker for raw peak certificates. -/
def check [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (cert : RawPeakCertificate α L) : Bool :=
  decide (cert.Valid r lt)

theorem valid_of_check_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {cert : RawPeakCertificate α L}
    (hcheck : cert.check (r := r) (lt := lt) = true) :
    cert.Valid r lt := by
  have hdec : decide (cert.Valid r lt) = true := by
    simpa [RawPeakCertificate.check] using hcheck
  exact of_decide_eq_true hdec

theorem check_eq_true_of_valid [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {cert : RawPeakCertificate α L}
    (hvalid : cert.Valid r lt) :
    cert.check (r := r) (lt := lt) = true := by
  exact decide_eq_true_eq.mpr hvalid

/-- Swapping the two sides preserves raw peak validity. -/
theorem valid_swap {cert : RawPeakCertificate α L}
    (hvalid : cert.Valid r lt) :
    cert.swap.Valid r lt := by
  rcases hvalid with ⟨hleftStep, hrightStep, hvalley⟩
  exact ⟨hrightStep, hleftStep, RawValleyCertificate.valid_swap (r := r) (lt := lt) hvalley⟩

end RawPeakCertificate

/-- Proof-free decreasing-diagram data: an enumerated step list plus raw peak certificates. -/
structure RawCertifiedLocallyDecreasing (α : Type u) (L : Type v) where
  steps : List (StepTriple α L)
  certs : List (RawPeakCertificate α L)
  deriving DecidableEq, Repr

instance {α : Type} {L : Type} [FromJson α] [FromJson L] :
    FromJson (RawCertifiedLocallyDecreasing α L) where
  fromJson? j := do
    let steps ← j.getObjValAs? (List (StepTriple α L)) "steps"
    let certs ← j.getObjValAs? (List (RawPeakCertificate α L)) "certs"
    pure { steps, certs }

instance {α : Type} {L : Type} [ToJson α] [ToJson L] :
    ToJson (RawCertifiedLocallyDecreasing α L) where
  toJson raw := Json.mkObj [
    ("steps", toJson raw.steps),
    ("certs", toJson raw.certs)
  ]

namespace RawCertifiedLocallyDecreasing

variable {α : Type u} {L : Type v}
variable {r : LabeledARS α L} {lt : L → L → Prop}

/-- Build raw certification data from a finite support by auto-enumerating all real steps. -/
def ofFinite [∀ l a b, Decidable (r l a b)]
    (support : FiniteLabeledARS α L) (certs : List (RawPeakCertificate α L)) :
    RawCertifiedLocallyDecreasing α L where
  steps := support.enumerateSteps r
  certs := certs

/-- Every enumerated step is a real step of the underlying relation. -/
def StepsSound (raw : RawCertifiedLocallyDecreasing α L) (r : LabeledARS α L) : Prop :=
  ∀ s, s ∈ raw.steps → r s.label s.source s.target

/-- The enumeration contains every real labeled step. -/
def StepsComplete (raw : RawCertifiedLocallyDecreasing α L) (r : LabeledARS α L) : Prop :=
  ∀ a b l, r l a b → { label := l, source := a, target := b } ∈ raw.steps

/-- The auto-enumerated step list is sound by construction. -/
theorem stepsSound_ofFinite [∀ l a b, Decidable (r l a b)]
    (support : FiniteLabeledARS α L) (certs : List (RawPeakCertificate α L)) :
    ((RawCertifiedLocallyDecreasing.ofFinite (r := r) support certs).StepsSound r) := by
  intro step hmem
  exact FiniteLabeledARS.enumerateSteps_sound (r := r) hmem

/-- The auto-enumerated step list is complete over the given finite support. -/
theorem stepsComplete_ofFinite [∀ l a b, Decidable (r l a b)]
    (support : FiniteLabeledARS α L) (certs : List (RawPeakCertificate α L)) :
    ((RawCertifiedLocallyDecreasing.ofFinite (r := r) support certs).StepsComplete r) := by
  intro a b l hstep
  exact FiniteLabeledARS.mem_enumerateSteps (r := r) (support := support) hstep

/-- Every local peak over the enumerated step list is matched by a valid raw certificate. -/
def CoversAllPeaks (raw : RawCertifiedLocallyDecreasing α L)
    (r : LabeledARS α L) (lt : L → L → Prop) : Prop :=
  ∀ s₁ s₂, s₁ ∈ raw.steps → s₂ ∈ raw.steps → s₁.source = s₂.source →
    ∃ cert ∈ raw.certs, RawPeakCertificate.MatchesSteps cert s₁ s₂ ∧
      RawPeakCertificate.Valid cert r lt

/-- Full validity condition for a raw decreasing-diagram certificate package. -/
def Valid (raw : RawCertifiedLocallyDecreasing α L)
    (r : LabeledARS α L) (lt : L → L → Prop) : Prop :=
  raw.StepsSound r ∧ raw.CoversAllPeaks r lt

/-- Boolean check that every listed step is valid in `r`. -/
def stepsSoundB [DecidableEq α] [DecidableEq L]
    [∀ l a b, Decidable (r l a b)]
    (raw : RawCertifiedLocallyDecreasing α L) : Bool :=
  raw.steps.all (fun s => decide (r s.label s.source s.target))

/-- Boolean check that a concrete peak is covered by some valid certificate. -/
def coversPairB [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (raw : RawCertifiedLocallyDecreasing α L) (s₁ s₂ : StepTriple α L) : Bool :=
  if _ : s₁.source = s₂.source then
    raw.certs.any (fun cert => decide (RawPeakCertificate.MatchesSteps cert s₁ s₂ ∧
      RawPeakCertificate.Valid cert r lt))
  else
    true

/-- Boolean check that every local peak over the step list is covered. -/
def coversAllPeaksB [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (raw : RawCertifiedLocallyDecreasing α L) : Bool :=
  raw.steps.all (fun s₁ => raw.steps.all (fun s₂ => raw.coversPairB (r := r) (lt := lt) s₁ s₂))

/-- Main boolean checker for raw decreasing-diagram certificates. -/
def check [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (raw : RawCertifiedLocallyDecreasing α L) : Bool :=
  raw.stepsSoundB (r := r) && raw.coversAllPeaksB (r := r) (lt := lt)

/-- Render a raw certificate package as a pretty-printed JSON artifact. -/
def toJsonString {α : Type} {L : Type} [ToJson α] [ToJson L]
    (raw : RawCertifiedLocallyDecreasing α L) : String :=
  Lean.Json.pretty (toJson raw)

/-- Render a raw certificate package as compact JSON. -/
def toJsonStringCompressed {α : Type} {L : Type} [ToJson α] [ToJson L]
    (raw : RawCertifiedLocallyDecreasing α L) : String :=
  (toJson raw).compress

/-- Parse a JSON artifact into raw certificate data. -/
def parseJson? {α : Type} {L : Type} [FromJson α] [FromJson L]
    (artifact : String) : Except String (RawCertifiedLocallyDecreasing α L) := do
  let json : Json ← Json.parse artifact
  fromJson? (α := RawCertifiedLocallyDecreasing α L) json

/-- Parse a JSON artifact and run the raw decreasing-diagram checker on it. -/
def checkJson {α : Type} {L : Type} {r : LabeledARS α L} {lt : L → L → Prop}
    [FromJson α] [FromJson L]
    [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (artifact : String) : Except String Bool := do
  let raw ← RawCertifiedLocallyDecreasing.parseJson? (α := α) (L := L) artifact
  pure (raw.check (r := r) (lt := lt))

theorem stepsSound_of_stepsSoundB_eq_true [DecidableEq α] [DecidableEq L]
    [∀ l a b, Decidable (r l a b)]
    {raw : RawCertifiedLocallyDecreasing α L}
    (hcheck : raw.stepsSoundB (r := r) = true) :
    raw.StepsSound r := by
  intro s hs
  have hsound : decide (r s.label s.source s.target) = true :=
    (List.all_eq_true.mp hcheck) s hs
  exact of_decide_eq_true hsound

theorem stepsSoundB_eq_true_of_stepsSound [DecidableEq α] [DecidableEq L]
    [∀ l a b, Decidable (r l a b)]
    {raw : RawCertifiedLocallyDecreasing α L}
    (hsound : raw.StepsSound r) :
    raw.stepsSoundB (r := r) = true := by
  apply List.all_eq_true.mpr
  intro s hs
  exact decide_eq_true_eq.mpr (hsound s hs)

theorem coversPair_of_coversPairB_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : RawCertifiedLocallyDecreasing α L} {s₁ s₂ : StepTriple α L}
    (hsame : s₁.source = s₂.source)
    (hcheck : raw.coversPairB (r := r) (lt := lt) s₁ s₂ = true) :
    ∃ cert ∈ raw.certs, RawPeakCertificate.MatchesSteps cert s₁ s₂ ∧
      RawPeakCertificate.Valid cert r lt := by
  simpa [RawCertifiedLocallyDecreasing.coversPairB, hsame] using hcheck

theorem coversPairB_eq_true_of_coversPair [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : RawCertifiedLocallyDecreasing α L} {s₁ s₂ : StepTriple α L}
    (hsame : s₁.source = s₂.source)
    (hcover : ∃ cert ∈ raw.certs, RawPeakCertificate.MatchesSteps cert s₁ s₂ ∧
      RawPeakCertificate.Valid cert r lt) :
    raw.coversPairB (r := r) (lt := lt) s₁ s₂ = true := by
  rcases hcover with ⟨cert, hmem, hmatch, hvalid⟩
  unfold RawCertifiedLocallyDecreasing.coversPairB
  rw [dif_pos hsame]
  exact List.any_eq_true.mpr ⟨cert, hmem, decide_eq_true_eq.mpr ⟨hmatch, hvalid⟩⟩

theorem coversAllPeaks_of_coversAllPeaksB_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : RawCertifiedLocallyDecreasing α L}
    (hcheck : raw.coversAllPeaksB (r := r) (lt := lt) = true) :
    raw.CoversAllPeaks r lt := by
  intro s₁ s₂ hs₁ hs₂ hsame
  have hrow : raw.steps.all (fun s₂ => raw.coversPairB (r := r) (lt := lt) s₁ s₂) = true :=
    (List.all_eq_true.mp hcheck) s₁ hs₁
  have hpair : raw.coversPairB (r := r) (lt := lt) s₁ s₂ = true :=
    (List.all_eq_true.mp hrow) s₂ hs₂
  exact raw.coversPair_of_coversPairB_eq_true (r := r) (lt := lt) hsame hpair

theorem coversAllPeaksB_eq_true_of_coversAllPeaks [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : RawCertifiedLocallyDecreasing α L}
    (hcover : raw.CoversAllPeaks r lt) :
    raw.coversAllPeaksB (r := r) (lt := lt) = true := by
  apply List.all_eq_true.mpr
  intro s₁ hs₁
  apply List.all_eq_true.mpr
  intro s₂ hs₂
  by_cases hsame : s₁.source = s₂.source
  · exact raw.coversPairB_eq_true_of_coversPair (r := r) (lt := lt) hsame
      (hcover s₁ s₂ hs₁ hs₂ hsame)
  · unfold RawCertifiedLocallyDecreasing.coversPairB
    rw [dif_neg hsame]

/-- Soundness of a raw checked package. -/
theorem sound (raw : RawCertifiedLocallyDecreasing α L)
    (hvalid : raw.Valid r lt) (hcomplete : raw.StepsComplete r) :
    LocallyDecreasing r lt := by
  rcases hvalid with ⟨hstepsSound, hcovers⟩
  intro a b c l₁ l₂ hab hac
  let s₁ : StepTriple α L := { label := l₁, source := a, target := b }
  let s₂ : StepTriple α L := { label := l₂, source := a, target := c }
  have hs₁ : s₁ ∈ raw.steps := hcomplete a b l₁ hab
  have hs₂ : s₂ ∈ raw.steps := hcomplete a c l₂ hac
  have hsame : s₁.source = s₂.source := rfl
  rcases hcovers s₁ s₂ hs₁ hs₂ hsame with ⟨cert, _, hmatch, hcertValid⟩
  rcases hmatch with ⟨hsrc, hleftLabel, hleftTarget, hrightLabel, hrightTarget⟩
  subst hsrc
  subst hleftLabel
  subst hleftTarget
  subst hrightLabel
  subst hrightTarget
  exact cert.sound (r := r) (lt := lt) hcertValid

theorem valid_of_check_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : RawCertifiedLocallyDecreasing α L}
    (hcheck : raw.check (r := r) (lt := lt) = true) :
    raw.Valid r lt := by
  have hand : raw.stepsSoundB (r := r) = true ∧ raw.coversAllPeaksB (r := r) (lt := lt) = true := by
    simpa [RawCertifiedLocallyDecreasing.check, Bool.and_eq_true] using hcheck
  exact ⟨raw.stepsSound_of_stepsSoundB_eq_true (r := r) hand.1,
    raw.coversAllPeaks_of_coversAllPeaksB_eq_true (r := r) (lt := lt) hand.2⟩

theorem check_eq_true_of_valid [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : RawCertifiedLocallyDecreasing α L}
    (hvalid : raw.Valid r lt) :
    raw.check (r := r) (lt := lt) = true := by
  rcases hvalid with ⟨hstepsSound, hcoversAllPeaks⟩
  unfold RawCertifiedLocallyDecreasing.check
  rw [raw.stepsSoundB_eq_true_of_stepsSound (r := r) hstepsSound,
    raw.coversAllPeaksB_eq_true_of_coversAllPeaks (r := r) (lt := lt) hcoversAllPeaks]
  rfl

/-- Confluence from a successful raw certificate check. -/
theorem confluent_of_check_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (wf : WellFounded lt) {raw : RawCertifiedLocallyDecreasing α L}
    (hcomplete : raw.StepsComplete r)
    (hcheck : raw.check (r := r) (lt := lt) = true) :
    Confluent (LabeledUnion r) :=
  confluent_of_locallyDecreasing (r := r) (lt := lt) wf
    (raw.sound (r := r) (lt := lt) (raw.valid_of_check_eq_true (r := r) (lt := lt) hcheck) hcomplete)

/-- Confluence from a successful raw check over an automatically enumerated finite system. -/
theorem confluent_of_ofFinite_check_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (support : FiniteLabeledARS α L) (wf : WellFounded lt)
    {certs : List (RawPeakCertificate α L)}
    (hcheck :
      (RawCertifiedLocallyDecreasing.ofFinite (r := r) support certs).check (r := r) (lt := lt) = true) :
    Confluent (LabeledUnion r) :=
  (RawCertifiedLocallyDecreasing.ofFinite (r := r) support certs).confluent_of_check_eq_true
    (r := r) (lt := lt) wf
    ((RawCertifiedLocallyDecreasing.stepsComplete_ofFinite (r := r) support certs))
    hcheck

/-- Confluence from a successfully parsed JSON artifact whose checker returns `true`. -/
theorem confluent_of_parseJson_eq_ok {α : Type} {L : Type} {r : LabeledARS α L}
    {lt : L → L → Prop} [FromJson α] [FromJson L]
    [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (wf : WellFounded lt) {artifact : String} {raw : RawCertifiedLocallyDecreasing α L}
    (hparse : RawCertifiedLocallyDecreasing.parseJson? (α := α) (L := L) artifact = Except.ok raw)
    (hcomplete : raw.StepsComplete r)
    (hcheck : raw.check (r := r) (lt := lt) = true) :
    Confluent (LabeledUnion r) := by
  let _ := hparse
  exact raw.confluent_of_check_eq_true (r := r) (lt := lt) wf hcomplete hcheck

theorem checkJson_eq_ok_true_of_parseJson_eq_ok {α : Type} {L : Type} {r : LabeledARS α L}
    {lt : L → L → Prop} [FromJson α] [FromJson L]
    [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {artifact : String} {raw : RawCertifiedLocallyDecreasing α L}
    (hparse : RawCertifiedLocallyDecreasing.parseJson? (α := α) (L := L) artifact = Except.ok raw)
    (hcheck : raw.check (r := r) (lt := lt) = true) :
    RawCertifiedLocallyDecreasing.checkJson (α := α) (L := L) (r := r) (lt := lt) artifact =
      Except.ok true := by
  unfold RawCertifiedLocallyDecreasing.checkJson
  rw [hparse]
  change Except.ok (raw.check (r := r) (lt := lt)) = Except.ok true
  exact congrArg Except.ok hcheck

end RawCertifiedLocallyDecreasing

/-- Raw decreasing-diagram data stored only for non-trivial canonical peaks. -/
structure CompressedRawCertifiedLocallyDecreasing (α : Type u) (L : Type v) where
  steps : List (StepTriple α L)
  certs : List (RawPeakCertificate α L)
  deriving DecidableEq, Repr

instance {α : Type} {L : Type} [FromJson α] [FromJson L] :
    FromJson (CompressedRawCertifiedLocallyDecreasing α L) where
  fromJson? j := do
    let steps ← j.getObjValAs? (List (StepTriple α L)) "steps"
    let certs ← j.getObjValAs? (List (RawPeakCertificate α L)) "certs"
    pure { steps, certs }

instance {α : Type} {L : Type} [ToJson α] [ToJson L] :
    ToJson (CompressedRawCertifiedLocallyDecreasing α L) where
  toJson raw := Json.mkObj [
    ("steps", toJson raw.steps),
    ("certs", toJson raw.certs)
  ]

namespace CompressedRawCertifiedLocallyDecreasing

variable {α : Type u} {L : Type v}
variable {r : LabeledARS α L} {lt : L → L → Prop}

/-- First occurrence index of a step inside a finite step list. -/
def stepIndex? [DecidableEq α] [DecidableEq L] :
    List (StepTriple α L) → StepTriple α L → Option Nat
  | [], _ => none
  | step :: steps, target =>
      if _ : step = target then
        some 0
      else
        Option.map Nat.succ (stepIndex? steps target)

/-- Canonical orientation for a non-trivial peak, induced by the step enumeration order. -/
def CanonicalPair [DecidableEq α] [DecidableEq L]
    (steps : List (StepTriple α L)) (s₁ s₂ : StepTriple α L) : Prop :=
  ∃ i j, stepIndex? steps s₁ = some i ∧ stepIndex? steps s₂ = some j ∧ i < j

section CanonicalProofs

variable [DecidableEq α] [DecidableEq L]

theorem stepIndex?_of_mem {steps : List (StepTriple α L)} {step : StepTriple α L}
    (hmem : step ∈ steps) :
    ∃ i, stepIndex? steps step = some i := by
  induction steps with
  | nil =>
      cases hmem
  | cons step' steps ih =>
      simp at hmem
      rcases hmem with rfl | hmem
      · exact ⟨0, by simp [stepIndex?]⟩
      · by_cases hhead : step' = step
        · exact ⟨0, by simp [stepIndex?, hhead]⟩
        · rcases ih hmem with ⟨i, hi⟩
          exact ⟨i + 1, by simp [stepIndex?, hhead, hi]⟩

theorem getElem?_of_stepIndex? {steps : List (StepTriple α L)} {step : StepTriple α L} {i : Nat}
    (hindex : stepIndex? steps step = some i) :
    steps[i]? = some step := by
  induction steps generalizing i with
  | nil =>
      cases hindex
  | cons step' steps ih =>
      by_cases hhead : step' = step
      · have hindex' : some 0 = some i := by
          simpa [stepIndex?, hhead] using hindex
        simp at hindex'
        subst i
        simp [hhead]
      · have hindex' : Option.map Nat.succ (stepIndex? steps step) = some i := by
          simpa [stepIndex?, hhead] using hindex
        rcases htail : stepIndex? steps step with _ | j
        · simp [htail] at hindex'
        · have hindex'' : some (Nat.succ j) = some i := by
            simpa [htail] using hindex'
          simp at hindex''
          subst i
          simp [ih (i := j) htail]

theorem eq_of_stepIndex?_eq {steps : List (StepTriple α L)} {s₁ s₂ : StepTriple α L} {i : Nat}
    (h₁ : stepIndex? steps s₁ = some i) (h₂ : stepIndex? steps s₂ = some i) :
    s₁ = s₂ := by
  have hs₁ : steps[i]? = some s₁ := getElem?_of_stepIndex? h₁
  have hs₂ : steps[i]? = some s₂ := getElem?_of_stepIndex? h₂
  rw [hs₁] at hs₂
  exact Option.some.inj hs₂

theorem canonicalPair_or_symm {steps : List (StepTriple α L)} {s₁ s₂ : StepTriple α L}
    (hs₁ : s₁ ∈ steps) (hs₂ : s₂ ∈ steps) (hneq : s₁ ≠ s₂) :
    CanonicalPair steps s₁ s₂ ∨ CanonicalPair steps s₂ s₁ := by
  rcases stepIndex?_of_mem hs₁ with ⟨i, hi⟩
  rcases stepIndex?_of_mem hs₂ with ⟨j, hj⟩
  have hij : i ≠ j := by
    intro hijEq
    apply hneq
    exact eq_of_stepIndex?_eq (by simpa [hijEq] using hi) hj
  rcases Nat.lt_trichotomy i j with hijLt | hijEq | hijGt
  · exact Or.inl ⟨i, j, hi, hj, hijLt⟩
  · exact False.elim (hij hijEq)
  · exact Or.inr ⟨j, i, hj, hi, hijGt⟩

theorem not_canonicalPair_symm {steps : List (StepTriple α L)} {s₁ s₂ : StepTriple α L}
    (hcanon : CanonicalPair steps s₁ s₂) :
    ¬ CanonicalPair steps s₂ s₁ := by
  intro hsymm
  rcases hcanon with ⟨i, j, hi, hj, hij⟩
  rcases hsymm with ⟨j', i', hj', hi', hji⟩
  have hjEq : j = j' := by
    rw [hj] at hj'
    exact Option.some.inj hj'
  have hiEq : i = i' := by
    rw [hi] at hi'
    exact Option.some.inj hi'
  subst hjEq
  subst hiEq
  exact Nat.lt_asymm hij hji

end CanonicalProofs

instance instDecidableCanonicalPair [DecidableEq α] [DecidableEq L]
    (steps : List (StepTriple α L)) (s₁ s₂ : StepTriple α L) :
    Decidable (CanonicalPair steps s₁ s₂) := by
  unfold CanonicalPair
  cases h₁ : stepIndex? steps s₁ with
  | none =>
      exact isFalse <| by
        intro h
        rcases h with ⟨i, _, hi, _, _⟩
        cases hi
  | some i =>
      cases h₂ : stepIndex? steps s₂ with
      | none =>
          exact isFalse <| by
            intro h
            rcases h with ⟨_, j, _, hj, _⟩
            cases hj
      | some j =>
          by_cases hij : i < j
          · exact isTrue ⟨i, j, rfl, rfl, hij⟩
          · exact isFalse <| by
              intro h
              rcases h with ⟨i', j', hi, hj, hlt⟩
              have hiEq : i' = i := by
                exact Option.some.inj hi |>.symm
              have hjEq : j' = j := by
                exact Option.some.inj hj |>.symm
              have : i < j := by
                simpa [hiEq, hjEq] using hlt
              exact hij this

/-- Keep only non-trivial certificates in canonical orientation. -/
def shouldKeep [DecidableEq α] [DecidableEq L]
    (steps : List (StepTriple α L)) (cert : RawPeakCertificate α L) : Bool :=
  let left := cert.leftStep
  let right := cert.rightStep
  if _ : left = right then
    false
  else
    decide (CanonicalPair steps left right)

theorem shouldKeep_eq_true_of_matches [DecidableEq α] [DecidableEq L]
    {steps : List (StepTriple α L)} {cert : RawPeakCertificate α L}
    {s₁ s₂ : StepTriple α L}
    (hsame : s₁.source = s₂.source)
    (hmatch : RawPeakCertificate.MatchesSteps cert s₁ s₂)
    (hneq : s₁ ≠ s₂) (hcanon : CanonicalPair steps s₁ s₂) :
    shouldKeep steps cert = true := by
  have hleft : cert.leftStep = s₁ := RawPeakCertificate.leftStep_eq_of_matches hmatch
  have hright : cert.rightStep = s₂ := RawPeakCertificate.rightStep_eq_of_matches hsame hmatch
  simp [shouldKeep, hleft, hright, hneq, hcanon]

/-- Compress a raw certificate family by dropping trivial peaks and symmetric duplicates. -/
def ofRaw [DecidableEq α] [DecidableEq L]
    (raw : RawCertifiedLocallyDecreasing α L) :
    CompressedRawCertifiedLocallyDecreasing α L where
  steps := raw.steps
  certs := raw.certs.filter (shouldKeep raw.steps)

/-- Every enumerated step is a real step of the underlying relation. -/
def StepsSound (raw : CompressedRawCertifiedLocallyDecreasing α L) (r : LabeledARS α L) : Prop :=
  ∀ s, s ∈ raw.steps → r s.label s.source s.target

/-- The enumeration contains every real labeled step. -/
def StepsComplete (raw : CompressedRawCertifiedLocallyDecreasing α L) (r : LabeledARS α L) : Prop :=
  ∀ a b l, r l a b → { label := l, source := a, target := b } ∈ raw.steps

/-- Every local peak is either trivial, covered canonically, or covered via the stored symmetric orientation. -/
def CoversAllPeaks [DecidableEq α] [DecidableEq L]
    (raw : CompressedRawCertifiedLocallyDecreasing α L)
    (r : LabeledARS α L) (lt : L → L → Prop) : Prop :=
  ∀ s₁ s₂, s₁ ∈ raw.steps → s₂ ∈ raw.steps → s₁.source = s₂.source →
    if _ : s₁ = s₂ then
      True
    else if _ : CanonicalPair raw.steps s₁ s₂ then
      ∃ cert ∈ raw.certs, RawPeakCertificate.MatchesSteps cert s₁ s₂ ∧
        RawPeakCertificate.Valid cert r lt
    else
      ∃ cert ∈ raw.certs, RawPeakCertificate.MatchesSteps cert s₂ s₁ ∧
        RawPeakCertificate.Valid cert r lt

/-- Full validity condition for compressed decreasing-diagram data. -/
def Valid [DecidableEq α] [DecidableEq L]
    (raw : CompressedRawCertifiedLocallyDecreasing α L)
    (r : LabeledARS α L) (lt : L → L → Prop) : Prop :=
  raw.StepsSound r ∧ raw.CoversAllPeaks r lt

/-- Boolean check that every listed step is valid in `r`. -/
def stepsSoundB [DecidableEq α] [DecidableEq L]
    [∀ l a b, Decidable (r l a b)]
    (raw : CompressedRawCertifiedLocallyDecreasing α L) : Bool :=
  raw.steps.all (fun s => decide (r s.label s.source s.target))

/-- Boolean check for the canonical orientation predicate. -/
def canonicalPairB [DecidableEq α] [DecidableEq L]
    (steps : List (StepTriple α L)) (s₁ s₂ : StepTriple α L) : Bool :=
  match stepIndex? steps s₁, stepIndex? steps s₂ with
  | some i, some j => decide (i < j)
  | _, _ => false

/-- Boolean check that one local peak is covered in compressed form. -/
def coversPairB [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (raw : CompressedRawCertifiedLocallyDecreasing α L) (s₁ s₂ : StepTriple α L) : Bool :=
  if _ : s₁.source = s₂.source then
    if _ : s₁ = s₂ then
      true
    else if canonicalPairB raw.steps s₁ s₂ then
      raw.certs.any (fun cert => decide (RawPeakCertificate.MatchesSteps cert s₁ s₂ ∧
        RawPeakCertificate.Valid cert r lt))
    else
      raw.certs.any (fun cert => decide (RawPeakCertificate.MatchesSteps cert s₂ s₁ ∧
        RawPeakCertificate.Valid cert r lt))
  else
    true

/-- Boolean check that every local peak over the step list is covered. -/
def coversAllPeaksB [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (raw : CompressedRawCertifiedLocallyDecreasing α L) : Bool :=
  raw.steps.all (fun s₁ => raw.steps.all (fun s₂ => raw.coversPairB (r := r) (lt := lt) s₁ s₂))

/-- Main boolean checker for compressed decreasing-diagram certificates. -/
def check [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (raw : CompressedRawCertifiedLocallyDecreasing α L) : Bool :=
  raw.stepsSoundB (r := r) && raw.coversAllPeaksB (r := r) (lt := lt)

/-- Render a compressed raw certificate package as pretty-printed JSON. -/
def toJsonString {α : Type} {L : Type} [ToJson α] [ToJson L]
    (raw : CompressedRawCertifiedLocallyDecreasing α L) : String :=
  Lean.Json.pretty (toJson raw)

/-- Render a compressed raw certificate package as compact JSON. -/
def toJsonStringCompressed {α : Type} {L : Type} [ToJson α] [ToJson L]
    (raw : CompressedRawCertifiedLocallyDecreasing α L) : String :=
  (toJson raw).compress

/-- Parse a compressed raw certificate package from JSON. -/
def parseJson? {α : Type} {L : Type} [FromJson α] [FromJson L]
    (artifact : String) : Except String (CompressedRawCertifiedLocallyDecreasing α L) := do
  let json : Json ← Json.parse artifact
  fromJson? (α := CompressedRawCertifiedLocallyDecreasing α L) json

/-- Parse a compressed artifact and run its checker. -/
def checkJson {α : Type} {L : Type} {r : LabeledARS α L} {lt : L → L → Prop}
    [FromJson α] [FromJson L]
    [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (artifact : String) : Except String Bool := do
  let raw ← CompressedRawCertifiedLocallyDecreasing.parseJson? (α := α) (L := L) artifact
  pure (raw.check (r := r) (lt := lt))

theorem canonicalPair_of_canonicalPairB_eq_true [DecidableEq α] [DecidableEq L]
    {steps : List (StepTriple α L)} {s₁ s₂ : StepTriple α L}
    (hcheck : canonicalPairB steps s₁ s₂ = true) :
    CanonicalPair steps s₁ s₂ := by
  unfold canonicalPairB at hcheck
  cases h₁ : stepIndex? steps s₁ with
  | none =>
      simp [h₁] at hcheck
  | some i =>
      cases h₂ : stepIndex? steps s₂ with
      | none =>
          simp [h₁, h₂] at hcheck
      | some j =>
          simp [h₁, h₂] at hcheck
          exact ⟨i, j, h₁, h₂, hcheck⟩

theorem canonicalPairB_eq_true_of_canonicalPair [DecidableEq α] [DecidableEq L]
    {steps : List (StepTriple α L)} {s₁ s₂ : StepTriple α L}
    (hcanon : CanonicalPair steps s₁ s₂) :
    canonicalPairB steps s₁ s₂ = true := by
  rcases hcanon with ⟨i, j, hi, hj, hij⟩
  simp [canonicalPairB, hi, hj, hij]

theorem stepsSound_of_stepsSoundB_eq_true [DecidableEq α] [DecidableEq L]
    [∀ l a b, Decidable (r l a b)]
    {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (hcheck : raw.stepsSoundB (r := r) = true) :
    raw.StepsSound r := by
  intro s hs
  have hsound : decide (r s.label s.source s.target) = true :=
    (List.all_eq_true.mp hcheck) s hs
  exact of_decide_eq_true hsound

theorem stepsSoundB_eq_true_of_stepsSound [DecidableEq α] [DecidableEq L]
    [∀ l a b, Decidable (r l a b)]
    {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (hsound : raw.StepsSound r) :
    raw.stepsSoundB (r := r) = true := by
  apply List.all_eq_true.mpr
  intro s hs
  exact decide_eq_true_eq.mpr (hsound s hs)

theorem coversPair_of_coversPairB_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : CompressedRawCertifiedLocallyDecreasing α L} {s₁ s₂ : StepTriple α L}
    (hsame : s₁.source = s₂.source)
    (hcheck : raw.coversPairB (r := r) (lt := lt) s₁ s₂ = true) :
    if _ : s₁ = s₂ then
      True
    else if _ : CanonicalPair raw.steps s₁ s₂ then
      ∃ cert ∈ raw.certs, RawPeakCertificate.MatchesSteps cert s₁ s₂ ∧
        RawPeakCertificate.Valid cert r lt
    else
      ∃ cert ∈ raw.certs, RawPeakCertificate.MatchesSteps cert s₂ s₁ ∧
        RawPeakCertificate.Valid cert r lt := by
  by_cases htriv : s₁ = s₂
  · simp [htriv]
  · by_cases hcanon : CanonicalPair raw.steps s₁ s₂
    · have hcanonB : canonicalPairB raw.steps s₁ s₂ = true :=
        canonicalPairB_eq_true_of_canonicalPair hcanon
      simpa [CompressedRawCertifiedLocallyDecreasing.coversPairB, hsame, htriv, hcanon, hcanonB]
        using hcheck
    · have hcanonB : canonicalPairB raw.steps s₁ s₂ = false := by
        cases hB : canonicalPairB raw.steps s₁ s₂ with
        | false =>
            rfl
        | true =>
            exact False.elim (hcanon (canonicalPair_of_canonicalPairB_eq_true hB))
      simpa [CompressedRawCertifiedLocallyDecreasing.coversPairB, hsame, htriv, hcanon, hcanonB]
        using hcheck

theorem coversPairB_eq_true_of_coversPair [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : CompressedRawCertifiedLocallyDecreasing α L} {s₁ s₂ : StepTriple α L}
    (hsame : s₁.source = s₂.source)
    (hcover :
      if _ : s₁ = s₂ then
        True
      else if _ : CanonicalPair raw.steps s₁ s₂ then
        ∃ cert ∈ raw.certs, RawPeakCertificate.MatchesSteps cert s₁ s₂ ∧
          RawPeakCertificate.Valid cert r lt
      else
        ∃ cert ∈ raw.certs, RawPeakCertificate.MatchesSteps cert s₂ s₁ ∧
          RawPeakCertificate.Valid cert r lt) :
    raw.coversPairB (r := r) (lt := lt) s₁ s₂ = true := by
  by_cases htriv : s₁ = s₂
  · simp [CompressedRawCertifiedLocallyDecreasing.coversPairB, htriv]
  · by_cases hcanon : CanonicalPair raw.steps s₁ s₂
    · have hcanonB : canonicalPairB raw.steps s₁ s₂ = true :=
        canonicalPairB_eq_true_of_canonicalPair hcanon
      rcases (by simpa [htriv, hcanon] using hcover) with ⟨cert, hmem, hmatch, hvalid⟩
      have hany :
          raw.certs.any (fun cert => decide (RawPeakCertificate.MatchesSteps cert s₁ s₂ ∧
            RawPeakCertificate.Valid cert r lt)) = true :=
        List.any_eq_true.mpr ⟨cert, hmem, decide_eq_true_eq.mpr ⟨hmatch, hvalid⟩⟩
      simpa [CompressedRawCertifiedLocallyDecreasing.coversPairB, hsame, htriv, hcanonB] using hany
    · have hcanonB : canonicalPairB raw.steps s₁ s₂ = false := by
        cases hB : canonicalPairB raw.steps s₁ s₂ with
        | false =>
            rfl
        | true =>
            exact False.elim (hcanon (canonicalPair_of_canonicalPairB_eq_true hB))
      rcases (by simpa [htriv, hcanon] using hcover) with ⟨cert, hmem, hmatch, hvalid⟩
      have hany :
          raw.certs.any (fun cert => decide (RawPeakCertificate.MatchesSteps cert s₂ s₁ ∧
            RawPeakCertificate.Valid cert r lt)) = true :=
        List.any_eq_true.mpr ⟨cert, hmem, decide_eq_true_eq.mpr ⟨hmatch, hvalid⟩⟩
      simpa [CompressedRawCertifiedLocallyDecreasing.coversPairB, hsame, htriv, hcanonB] using hany

theorem coversAllPeaks_of_coversAllPeaksB_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (hcheck : raw.coversAllPeaksB (r := r) (lt := lt) = true) :
    raw.CoversAllPeaks r lt := by
  intro s₁ s₂ hs₁ hs₂ hsame
  have hrow : raw.steps.all (fun s₂ => raw.coversPairB (r := r) (lt := lt) s₁ s₂) = true :=
    (List.all_eq_true.mp hcheck) s₁ hs₁
  have hpair : raw.coversPairB (r := r) (lt := lt) s₁ s₂ = true :=
    (List.all_eq_true.mp hrow) s₂ hs₂
  exact raw.coversPair_of_coversPairB_eq_true (r := r) (lt := lt) hsame hpair

theorem coversAllPeaksB_eq_true_of_coversAllPeaks [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (hcover : raw.CoversAllPeaks r lt) :
    raw.coversAllPeaksB (r := r) (lt := lt) = true := by
  apply List.all_eq_true.mpr
  intro s₁ hs₁
  apply List.all_eq_true.mpr
  intro s₂ hs₂
  by_cases hsame : s₁.source = s₂.source
  · exact raw.coversPairB_eq_true_of_coversPair (r := r) (lt := lt) hsame
      (hcover s₁ s₂ hs₁ hs₂ hsame)
  · unfold CompressedRawCertifiedLocallyDecreasing.coversPairB
    rw [dif_neg hsame]

/-- Compression preserves step soundness because the step list is unchanged. -/
theorem stepsSound_of_ofRaw [DecidableEq α] [DecidableEq L]
    {raw : RawCertifiedLocallyDecreasing α L}
    (hsound : raw.StepsSound r) :
    (CompressedRawCertifiedLocallyDecreasing.ofRaw raw).StepsSound r := by
  simpa [CompressedRawCertifiedLocallyDecreasing.ofRaw, StepsSound] using hsound

/-- Compression preserves local-peak coverage by keeping one certificate per non-trivial symmetric pair. -/
theorem coversAllPeaks_of_ofRaw [DecidableEq α] [DecidableEq L]
    {raw : RawCertifiedLocallyDecreasing α L}
    (hcover : raw.CoversAllPeaks r lt) :
    (CompressedRawCertifiedLocallyDecreasing.ofRaw raw).CoversAllPeaks r lt := by
  intro s₁ s₂ hs₁ hs₂ hsame
  by_cases htriv : s₁ = s₂
  · simp [htriv]
  · have horient :=
      canonicalPair_or_symm (steps := raw.steps) hs₁ hs₂ htriv
    dsimp [CompressedRawCertifiedLocallyDecreasing.ofRaw]
    cases horient with
    | inl hcanon =>
        have hbranch :
            ∃ cert ∈ raw.certs, RawPeakCertificate.MatchesSteps cert s₁ s₂ ∧
              RawPeakCertificate.Valid cert r lt :=
          hcover s₁ s₂ hs₁ hs₂ hsame
        have : ∃ cert ∈ List.filter (shouldKeep raw.steps) raw.certs,
            RawPeakCertificate.MatchesSteps cert s₁ s₂ ∧
              RawPeakCertificate.Valid cert r lt := by
          rcases hbranch with ⟨cert, hmem, hmatch, hvalid⟩
          refine ⟨cert, List.mem_filter.mpr ⟨hmem, ?_⟩, hmatch, hvalid⟩
          exact shouldKeep_eq_true_of_matches hsame hmatch htriv hcanon
        simpa [CompressedRawCertifiedLocallyDecreasing.CoversAllPeaks, htriv, hcanon] using this
    | inr hcanon =>
        have hnot : ¬ CanonicalPair raw.steps s₁ s₂ :=
          not_canonicalPair_symm hcanon
        have hbranch :
            ∃ cert ∈ raw.certs, RawPeakCertificate.MatchesSteps cert s₂ s₁ ∧
              RawPeakCertificate.Valid cert r lt :=
          hcover s₂ s₁ hs₂ hs₁ hsame.symm
        have : ∃ cert ∈ List.filter (shouldKeep raw.steps) raw.certs,
            RawPeakCertificate.MatchesSteps cert s₂ s₁ ∧
              RawPeakCertificate.Valid cert r lt := by
          rcases hbranch with ⟨cert, hmem, hmatch, hvalid⟩
          refine ⟨cert, List.mem_filter.mpr ⟨hmem, ?_⟩, hmatch, hvalid⟩
          exact shouldKeep_eq_true_of_matches hsame.symm hmatch (Ne.symm htriv) hcanon
        simpa [CompressedRawCertifiedLocallyDecreasing.CoversAllPeaks, htriv, hnot] using this

/-- Compression preserves validity. -/
theorem valid_of_ofRaw_valid [DecidableEq α] [DecidableEq L]
    {raw : RawCertifiedLocallyDecreasing α L}
    (hvalid : raw.Valid r lt) :
    (CompressedRawCertifiedLocallyDecreasing.ofRaw raw).Valid r lt := by
  rcases hvalid with ⟨hsound, hcover⟩
  exact ⟨stepsSound_of_ofRaw (r := r) hsound,
    coversAllPeaks_of_ofRaw (r := r) (lt := lt) hcover⟩

theorem valid_of_check_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (hcheck : raw.check (r := r) (lt := lt) = true) :
    raw.Valid r lt := by
  have hand : raw.stepsSoundB (r := r) = true ∧ raw.coversAllPeaksB (r := r) (lt := lt) = true := by
    simpa [CompressedRawCertifiedLocallyDecreasing.check, Bool.and_eq_true] using hcheck
  exact ⟨raw.stepsSound_of_stepsSoundB_eq_true (r := r) hand.1,
    raw.coversAllPeaks_of_coversAllPeaksB_eq_true (r := r) (lt := lt) hand.2⟩

theorem check_eq_true_of_valid [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (hvalid : raw.Valid r lt) :
    raw.check (r := r) (lt := lt) = true := by
  rcases hvalid with ⟨hstepsSound, hcoversAllPeaks⟩
  unfold CompressedRawCertifiedLocallyDecreasing.check
  rw [raw.stepsSoundB_eq_true_of_stepsSound (r := r) hstepsSound,
    raw.coversAllPeaksB_eq_true_of_coversAllPeaks (r := r) (lt := lt) hcoversAllPeaks]
  rfl

/-- Soundness of compressed checked data. -/
theorem sound [DecidableEq α] [DecidableEq L]
    (raw : CompressedRawCertifiedLocallyDecreasing α L)
    (hvalid : raw.Valid r lt) (hcomplete : raw.StepsComplete r) :
    LocallyDecreasing r lt := by
  rcases hvalid with ⟨_, hcovers⟩
  intro a b c l₁ l₂ hab hac
  let s₁ : StepTriple α L := { label := l₁, source := a, target := b }
  let s₂ : StepTriple α L := { label := l₂, source := a, target := c }
  have hs₁ : s₁ ∈ raw.steps := hcomplete a b l₁ hab
  have hs₂ : s₂ ∈ raw.steps := hcomplete a c l₂ hac
  have hsame : s₁.source = s₂.source := rfl
  have hcover := hcovers s₁ s₂ hs₁ hs₂ hsame
  by_cases htriv : s₁ = s₂
  · have hbc : b = c := by
      simpa [s₁, s₂] using congrArg StepTriple.target htriv
    subst hbc
    exact ⟨b, StarPred.refl b, StarPred.refl b⟩
  · by_cases hcanon : CanonicalPair raw.steps s₁ s₂
    · have hbranch :
          ∃ cert ∈ raw.certs, RawPeakCertificate.MatchesSteps cert s₁ s₂ ∧
            RawPeakCertificate.Valid cert r lt := by
          simpa [htriv, hcanon] using hcover
      rcases hbranch with ⟨cert, _, hmatch, hcertValid⟩
      rcases hmatch with ⟨hsrc, hleftLabel, hleftTarget, hrightLabel, hrightTarget⟩
      subst hsrc
      subst hleftLabel
      subst hleftTarget
      subst hrightLabel
      subst hrightTarget
      exact cert.sound (r := r) (lt := lt) hcertValid
    · have hbranch :
          ∃ cert ∈ raw.certs, RawPeakCertificate.MatchesSteps cert s₂ s₁ ∧
            RawPeakCertificate.Valid cert r lt := by
          simpa [htriv, hcanon] using hcover
      rcases hbranch with ⟨cert, _, hmatch, hcertValid⟩
      have hswapValid : cert.swap.Valid r lt :=
        RawPeakCertificate.valid_swap (r := r) (lt := lt) hcertValid
      have hswapMatch : cert.swap.MatchesSteps s₁ s₂ :=
        RawPeakCertificate.matches_swap hsame.symm hmatch
      rcases hswapMatch with ⟨hsrc, hleftLabel, hleftTarget, hrightLabel, hrightTarget⟩
      subst hsrc
      subst hleftLabel
      subst hleftTarget
      subst hrightLabel
      subst hrightTarget
      exact cert.swap.sound (r := r) (lt := lt) hswapValid

/-- Confluence from a valid compressed decreasing-diagram certificate package. -/
theorem confluent_of_valid [DecidableEq α] [DecidableEq L]
    {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (wf : WellFounded lt) (hvalid : raw.Valid r lt) (hcomplete : raw.StepsComplete r) :
    Confluent (LabeledUnion r) :=
  confluent_of_locallyDecreasing (r := r) (lt := lt) wf (raw.sound (r := r) (lt := lt) hvalid hcomplete)

/-- Confluence from a successful compressed certificate check. -/
theorem confluent_of_check_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (wf : WellFounded lt) {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (hcomplete : raw.StepsComplete r)
    (hcheck : raw.check (r := r) (lt := lt) = true) :
    Confluent (LabeledUnion r) :=
  confluent_of_locallyDecreasing (r := r) (lt := lt) wf
    (raw.sound (r := r) (lt := lt) (raw.valid_of_check_eq_true (r := r) (lt := lt) hcheck) hcomplete)

/-- Confluence from a successfully parsed compressed JSON artifact. -/
theorem confluent_of_parseJson_eq_ok {α : Type} {L : Type} {r : LabeledARS α L}
    {lt : L → L → Prop} [FromJson α] [FromJson L]
    [DecidableEq α] [DecidableEq L]
    {artifact : String} {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (wf : WellFounded lt)
    (hparse : CompressedRawCertifiedLocallyDecreasing.parseJson? (α := α) (L := L) artifact =
      Except.ok raw)
    (hvalid : raw.Valid r lt) (hcomplete : raw.StepsComplete r) :
    Confluent (LabeledUnion r) := by
  let _ := hparse
  exact raw.confluent_of_valid (r := r) (lt := lt) wf hvalid hcomplete

theorem checkJson_eq_ok_true_of_parseJson_eq_ok {α : Type} {L : Type} {r : LabeledARS α L}
    {lt : L → L → Prop} [FromJson α] [FromJson L]
    [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {artifact : String} {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (hparse : CompressedRawCertifiedLocallyDecreasing.parseJson? (α := α) (L := L) artifact =
      Except.ok raw)
    (hcheck : raw.check (r := r) (lt := lt) = true) :
    CompressedRawCertifiedLocallyDecreasing.checkJson (α := α) (L := L) (r := r) (lt := lt)
      artifact = Except.ok true := by
  unfold CompressedRawCertifiedLocallyDecreasing.checkJson
  rw [hparse]
  change Except.ok (raw.check (r := r) (lt := lt)) = Except.ok true
  exact congrArg Except.ok hcheck

/-- Confluence after compressing a valid uncompressed certificate package. -/
theorem confluent_of_ofRaw_valid [DecidableEq α] [DecidableEq L]
    {raw : RawCertifiedLocallyDecreasing α L}
    (wf : WellFounded lt) (hvalid : raw.Valid r lt) (hcomplete : raw.StepsComplete r) :
    Confluent (LabeledUnion r) :=
  (CompressedRawCertifiedLocallyDecreasing.ofRaw raw).confluent_of_valid (r := r) (lt := lt) wf
    ((CompressedRawCertifiedLocallyDecreasing.valid_of_ofRaw_valid (r := r) (lt := lt) hvalid))
    (by simpa [CompressedRawCertifiedLocallyDecreasing.ofRaw, StepsComplete] using hcomplete)

end CompressedRawCertifiedLocallyDecreasing

end Rewriting
