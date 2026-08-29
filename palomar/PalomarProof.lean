import PalomarCommon

/-!
# Proof-only certificate development

This module contains the proof-side implementation of the generic certificate
soundness theorem. It is intentionally separate from `Challenge.lean`: the
Challenge is core-only, while Comparator permits the Solution to use this
larger local development.
-/

namespace Metatheory.Palomar433.Certificate

universe u v

structure Edge (α : Type u) (L : Type v) where
  label : L
  source : α
  target : α
  deriving DecidableEq

structure PeakCertificate (α : Type u) (L : Type v) where
  leftStep : Edge α L
  rightStep : Edge α L
  join : α
  leftPath : List (Edge α L)
  rightPath : List (Edge α L)
  deriving DecidableEq

def RouteValid {α : Type u} {L : Type v} (r : LabeledARS α L)
    (start finish : α) : List (Edge α L) → Prop
  | [] => start = finish
  | s :: rest =>
      s.source = start ∧ r s.label s.source s.target ∧
        RouteValid r s.target finish rest

def RouteDecreasing {α : Type u} {L : Type v} (lt : L → L → Prop)
    (l₁ l₂ : L) : List (Edge α L) → Prop
  | [] => True
  | s :: rest => lt s.label l₁ ∧ lt s.label l₂ ∧
      RouteDecreasing lt l₁ l₂ rest

def Matches {α : Type u} {L : Type v} (cert : PeakCertificate α L)
    (s₁ s₂ : Edge α L) : Prop :=
  cert.leftStep = s₁ ∧ cert.rightStep = s₂

def CertificateValid {α : Type u} {L : Type v}
    (r : LabeledARS α L) (lt : L → L → Prop)
    (cert : PeakCertificate α L) : Prop :=
  cert.leftStep.source = cert.rightStep.source ∧
    RouteValid r cert.leftStep.target cert.join cert.leftPath ∧
    RouteValid r cert.rightStep.target cert.join cert.rightPath ∧
    RouteDecreasing lt cert.leftStep.label cert.rightStep.label cert.leftPath ∧
    RouteDecreasing lt cert.leftStep.label cert.rightStep.label cert.rightPath

def StepsSound {α : Type u} {L : Type v} (steps : List (Edge α L))
    (r : LabeledARS α L) : Prop :=
  ∀ s, s ∈ steps → r s.label s.source s.target

def StepsComplete {α : Type u} {L : Type v} (steps : List (Edge α L))
    (r : LabeledARS α L) : Prop :=
  ∀ l a b, r l a b → { label := l, source := a, target := b } ∈ steps

def CoversAllPeaks {α : Type u} {L : Type v}
    (steps : List (Edge α L)) (certs : List (PeakCertificate α L))
    (r : LabeledARS α L) (lt : L → L → Prop) : Prop :=
  ∀ s₁ s₂, s₁ ∈ steps → s₂ ∈ steps → s₁.source = s₂.source →
    s₁ = s₂ ∨ ∃ cert ∈ certs,
      (Matches cert s₁ s₂ ∨ Matches cert s₂ s₁) ∧ CertificateValid r lt cert

def PackageValid {α : Type u} {L : Type v}
    (steps : List (Edge α L)) (certs : List (PeakCertificate α L))
    (r : LabeledARS α L) (lt : L → L → Prop) : Prop :=
  StepsSound steps r ∧ CoversAllPeaks steps certs r lt

def canonicalCertificateB {α : Type u} {L : Type v}
    [DecidableEq α] [DecidableEq L]
    (key : Edge α L → Nat) (cert : PeakCertificate α L) : Bool :=
  decide (cert.leftStep ≠ cert.rightStep ∧
    key cert.leftStep < key cert.rightStep)

def routeValidB {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    (stepB : L → α → α → Bool) (start finish : α) :
    List (Edge α L) → Bool
  | [] => decide (start = finish)
  | s :: rest =>
      decide (s.source = start) &&
        stepB s.label s.source s.target &&
        routeValidB stepB s.target finish rest

def routeDecreasingB {L : Type v}
    (ltB : L → L → Bool) (l₁ l₂ : L) : List (Edge α L) → Bool
  | [] => true
  | s :: rest =>
      ltB s.label l₁ && ltB s.label l₂ && routeDecreasingB ltB l₁ l₂ rest

def matchesB {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    (cert : PeakCertificate α L) (s₁ s₂ : Edge α L) : Bool :=
  decide (cert.leftStep = s₁ ∧ cert.rightStep = s₂)

def certificateValidB {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    (stepB : L → α → α → Bool) (ltB : L → L → Bool)
    (cert : PeakCertificate α L) : Bool :=
  decide (cert.leftStep.source = cert.rightStep.source) &&
    routeValidB stepB cert.leftStep.target cert.join cert.leftPath &&
    routeValidB stepB cert.rightStep.target cert.join cert.rightPath &&
    routeDecreasingB ltB cert.leftStep.label cert.rightStep.label cert.leftPath &&
    routeDecreasingB ltB cert.leftStep.label cert.rightStep.label cert.rightPath

def coversPairB {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    (stepB : L → α → α → Bool) (ltB : L → L → Bool)
    (certs : List (PeakCertificate α L)) (s₁ s₂ : Edge α L) : Bool :=
  if _ : s₁.source = s₂.source then
    if _ : s₁ = s₂ then
      true
    else
      certs.any (fun cert =>
        (matchesB cert s₁ s₂ || matchesB cert s₂ s₁) &&
          certificateValidB stepB ltB cert)
  else
    true

def checkB {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    (stepB : L → α → α → Bool) (ltB : L → L → Bool)
    (key : Edge α L → Nat) (steps : List (Edge α L))
    (certs : List (PeakCertificate α L)) : Bool :=
  certs.all (canonicalCertificateB key) &&
    (steps.all (fun s => stepB s.label s.source s.target) &&
      steps.all (fun s₁ => steps.all (coversPairB stepB ltB certs s₁)))

theorem routeValid_of_routeValidB
    {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    {r : LabeledARS α L} {stepB : L → α → α → Bool}
    (hstep : ∀ l a b, stepB l a b = true ↔ r l a b)
    {start finish : α} {path : List (Edge α L)}
    (h : routeValidB stepB start finish path = true) :
    RouteValid r start finish path := by
  induction path generalizing start with
  | nil =>
      change start = finish
      simpa [routeValidB] using h
  | cons s rest ih =>
      simp only [routeValidB, Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true h.1.1,
        (hstep s.label s.source s.target).mp h.1.2,
        ih h.2⟩

theorem routeDecreasing_of_routeDecreasingB
    {α : Type u} {L : Type v} {lt : L → L → Prop} {ltB : L → L → Bool}
    (hlt : ∀ l₁ l₂, ltB l₁ l₂ = true ↔ lt l₁ l₂)
    {l₁ l₂ : L} {path : List (Edge α L)}
    (h : routeDecreasingB ltB l₁ l₂ path = true) :
    RouteDecreasing lt l₁ l₂ path := by
  induction path with
  | nil => trivial
  | cons s rest ih =>
      simp only [routeDecreasingB, Bool.and_eq_true] at h
      exact ⟨(hlt s.label l₁).mp h.1.1,
        (hlt s.label l₂).mp h.1.2,
        ih h.2⟩

theorem certificateValid_of_certificateValidB
    {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    {r : LabeledARS α L} {lt : L → L → Prop}
    {stepB : L → α → α → Bool} {ltB : L → L → Bool}
    (hstep : ∀ l a b, stepB l a b = true ↔ r l a b)
    (hlt : ∀ l₁ l₂, ltB l₁ l₂ = true ↔ lt l₁ l₂)
    {cert : PeakCertificate α L}
    (h : certificateValidB stepB ltB cert = true) :
    CertificateValid r lt cert := by
  simp only [certificateValidB, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1.1.1,
    routeValid_of_routeValidB hstep h.1.1.1.2,
    routeValid_of_routeValidB hstep h.1.1.2,
    routeDecreasing_of_routeDecreasingB hlt h.1.2,
    routeDecreasing_of_routeDecreasingB hlt h.2⟩

theorem canonicalCertificate_of_canonicalCertificateB
    {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    {key : Edge α L → Nat} {cert : PeakCertificate α L}
    (h : canonicalCertificateB key cert = true) :
    cert.leftStep ≠ cert.rightStep ∧ key cert.leftStep < key cert.rightStep := by
  unfold canonicalCertificateB at h
  exact of_decide_eq_true h

theorem matches_of_matchesB
    {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    {cert : PeakCertificate α L} {s₁ s₂ : Edge α L}
    (h : matchesB cert s₁ s₂ = true) : Matches cert s₁ s₂ := by
  unfold matchesB at h
  change cert.leftStep = s₁ ∧ cert.rightStep = s₂
  exact of_decide_eq_true h

theorem coversPair_of_coversPairB
    {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    {r : LabeledARS α L} {lt : L → L → Prop}
    {stepB : L → α → α → Bool} {ltB : L → L → Bool}
    (hstep : ∀ l a b, stepB l a b = true ↔ r l a b)
    (hlt : ∀ l₁ l₂, ltB l₁ l₂ = true ↔ lt l₁ l₂)
    {certs : List (PeakCertificate α L)} {s₁ s₂ : Edge α L}
    (hsame : s₁.source = s₂.source)
    (h : coversPairB stepB ltB certs s₁ s₂ = true) :
    s₁ = s₂ ∨ ∃ cert ∈ certs,
      (Matches cert s₁ s₂ ∨ Matches cert s₂ s₁) ∧ CertificateValid r lt cert := by
  by_cases heq : s₁ = s₂
  · exact Or.inl heq
  · unfold coversPairB at h
    rw [dif_pos hsame, dif_neg heq] at h
    rcases List.any_eq_true.mp h with ⟨cert, hmem, hcert⟩
    simp only [Bool.and_eq_true] at hcert
    have hmatch : matchesB cert s₁ s₂ = true ∨ matchesB cert s₂ s₁ = true := by
      cases hm : matchesB cert s₁ s₂ with
      | false =>
          right
          simpa [hm] using hcert.1
      | true => exact Or.inl rfl
    exact Or.inr ⟨cert, hmem,
      hmatch.elim (fun hm => Or.inl (matches_of_matchesB hm))
        (fun hm => Or.inr (matches_of_matchesB hm)),
      certificateValid_of_certificateValidB hstep hlt hcert.2⟩

theorem stepsSound_of_stepsSoundB
    {α : Type u} {L : Type v} {r : LabeledARS α L}
    {stepB : L → α → α → Bool} (hstep : ∀ l a b,
      stepB l a b = true ↔ r l a b)
    {steps : List (Edge α L)}
    (h : steps.all (fun s => stepB s.label s.source s.target) = true) :
    StepsSound steps r := by
  intro s hs
  exact (hstep s.label s.source s.target).mp ((List.all_eq_true.mp h) s hs)

theorem coversAllPeaks_of_coversAllPeaksB
    {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    {r : LabeledARS α L} {lt : L → L → Prop}
    {stepB : L → α → α → Bool} {ltB : L → L → Bool}
    (hstep : ∀ l a b, stepB l a b = true ↔ r l a b)
    (hlt : ∀ l₁ l₂, ltB l₁ l₂ = true ↔ lt l₁ l₂)
    {steps : List (Edge α L)} {certs : List (PeakCertificate α L)}
    (h : steps.all (fun s₁ => steps.all (coversPairB stepB ltB certs s₁)) = true) :
    CoversAllPeaks steps certs r lt := by
  intro s₁ s₂ hs₁ hs₂ hsame
  have hrow : steps.all (coversPairB stepB ltB certs s₁) = true :=
    (List.all_eq_true.mp h) s₁ hs₁
  exact coversPair_of_coversPairB hstep hlt hsame
    ((List.all_eq_true.mp hrow) s₂ hs₂)

theorem packageValid_of_checkB
    {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    {r : LabeledARS α L} {lt : L → L → Prop}
    {stepB : L → α → α → Bool} {ltB : L → L → Bool}
    {key : Edge α L → Nat}
    {steps : List (Edge α L)} {certs : List (PeakCertificate α L)}
    (hstep : ∀ l a b, stepB l a b = true ↔ r l a b)
    (hlt : ∀ l₁ l₂, ltB l₁ l₂ = true ↔ lt l₁ l₂)
    (h : checkB stepB ltB key steps certs = true) :
    PackageValid steps certs r lt := by
  have h' : certs.all (canonicalCertificateB key) = true ∧
      (steps.all (fun s => stepB s.label s.source s.target) = true ∧
        steps.all (fun s₁ => steps.all (coversPairB stepB ltB certs s₁)) = true) := by
    simpa [checkB, Bool.and_eq_true] using h
  exact ⟨stepsSound_of_stepsSoundB hstep h'.2.1,
    coversAllPeaks_of_coversAllPeaksB hstep hlt h'.2.2⟩

theorem routeDecreasing_swap
    {α : Type u} {L : Type v} {lt : L → L → Prop} {l₁ l₂ : L}
    {path : List (Edge α L)}
    (h : RouteDecreasing lt l₁ l₂ path) :
    RouteDecreasing lt l₂ l₁ path := by
  induction path with
  | nil => trivial
  | cons s rest ih =>
      simp only [RouteDecreasing] at h ⊢
      exact ⟨h.2.1, h.1, ih h.2.2⟩

theorem routeValid_to_starPred
    {α : Type u} {L : Type v} {r : LabeledARS α L} {lt : L → L → Prop}
    {l₁ l₂ : L} {start finish : α} {path : List (Edge α L)}
    (hpath : RouteValid r start finish path)
    (hlabels : RouteDecreasing lt l₁ l₂ path) :
    StarPred r (fun l => lt l l₁ ∧ lt l l₂) start finish := by
  induction path generalizing start with
  | nil =>
      simp only [RouteValid] at hpath
      subst finish
      exact StarPred.refl _
  | cons s rest ih =>
      simp only [RouteValid, RouteDecreasing] at hpath hlabels
      rcases hpath with ⟨hsource, hstep, hrest⟩
      subst start
      rcases hlabels with ⟨hl₁, hl₂, hlabels⟩
      exact StarPred.trans
        (StarPred.tail (StarPred.refl s.source) s.label ⟨hl₁, hl₂⟩ hstep)
        (ih hrest hlabels)

theorem packageValid_locallyDecreasing
    {α : Type u} {L : Type v} {r : LabeledARS α L} {lt : L → L → Prop}
    {steps : List (Edge α L)} {certs : List (PeakCertificate α L)}
    (hvalid : PackageValid steps certs r lt)
    (hcomplete : StepsComplete steps r) :
    LocallyDecreasing r lt := by
  rcases hvalid with ⟨hsound, hcover⟩
  intro a b c l₁ l₂ hab hac
  let s₁ : Edge α L := ⟨l₁, a, b⟩
  let s₂ : Edge α L := ⟨l₂, a, c⟩
  have hs₁ : s₁ ∈ steps := hcomplete l₁ a b hab
  have hs₂ : s₂ ∈ steps := hcomplete l₂ a c hac
  rcases hcover s₁ s₂ hs₁ hs₂ rfl with hsame | ⟨cert, hcert, hmatches, hcertvalid⟩
  · have hbc : b = c := by
      simpa [s₁, s₂] using congrArg Edge.target hsame
    subst c
    exact ⟨b, StarPred.refl b, StarPred.refl b⟩
  · rcases hcertvalid with ⟨hsource, hleft, hright, hleftLabels, hrightLabels⟩
    rcases hmatches with hforward | hreverse
    · rcases hforward with ⟨hleftStep, hrightStep⟩
      have hleftStep' : cert.leftStep = { label := l₁, source := a, target := b } := by
        simpa [s₁] using hleftStep
      have hrightStep' : cert.rightStep = { label := l₂, source := a, target := c } := by
        simpa [s₂] using hrightStep
      have hleftLabels' : RouteDecreasing lt l₁ l₂ cert.leftPath := by
        simpa [hleftStep', hrightStep'] using hleftLabels
      have hrightLabels' : RouteDecreasing lt l₁ l₂ cert.rightPath := by
        simpa [hleftStep', hrightStep'] using hrightLabels
      rw [hleftStep'] at hleft
      rw [hrightStep'] at hright
      exact ⟨cert.join,
        routeValid_to_starPred hleft hleftLabels',
        routeValid_to_starPred hright hrightLabels'⟩
    · rcases hreverse with ⟨hrightStep, hleftStep⟩
      have hrightStep' : cert.rightStep = { label := l₁, source := a, target := b } := by
        simpa [s₁] using hleftStep
      have hleftStep' : cert.leftStep = { label := l₂, source := a, target := c } := by
        simpa [s₂] using hrightStep
      have hleftLabels' : RouteDecreasing lt l₁ l₂ cert.leftPath := by
        exact routeDecreasing_swap (by
          simpa [hleftStep', hrightStep'] using hleftLabels)
      have hrightLabels' : RouteDecreasing lt l₁ l₂ cert.rightPath := by
        exact routeDecreasing_swap (by
          simpa [hleftStep', hrightStep'] using hrightLabels)
      rw [hleftStep'] at hleft
      rw [hrightStep'] at hright
      exact ⟨cert.join,
        routeValid_to_starPred hright hrightLabels',
        routeValid_to_starPred hleft hleftLabels'⟩

theorem checked_complete_confluence
    {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    {r : LabeledARS α L} {lt : L → L → Prop}
    {stepB : L → α → α → Bool} {ltB : L → L → Bool}
    {key : Edge α L → Nat}
    {steps : List (Edge α L)} {certs : List (PeakCertificate α L)}
    (hstep : ∀ l a b, stepB l a b = true ↔ r l a b)
    (hlt : ∀ l₁ l₂, ltB l₁ l₂ = true ↔ lt l₁ l₂)
    (hcheck : checkB stepB ltB key steps certs = true)
    (hcomplete : StepsComplete steps r)
    (wf : WellFounded lt) :
    Confluent (LabeledUnion r) := by
  exact Metatheory.Palomar433.confluent_of_locallyDecreasing wf
    (packageValid_locallyDecreasing
      (packageValid_of_checkB hstep hlt hcheck) hcomplete)

end Metatheory.Palomar433.Certificate
