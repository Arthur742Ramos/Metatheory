import Std

/-!
# Proof-carrying decreasing-diagram certificates

This is the complete statement surface for the certificate-soundness result.
It intentionally imports only the Lean standard library. A finite artifact
lists every step of a labeled abstract rewriting system and supplies explicit
decreasing valleys for its local peaks; the Boolean checker accepts only
canonically oriented, valid certificates.
-/

namespace Metatheory.Palomar433

universe u v

abbrev Relation (α : Type u) := α → α → Prop

abbrev LabeledARS (α : Type u) (L : Type v) := L → α → α → Prop

def LabeledUnion {α : Type u} {L : Type v} (r : LabeledARS α L) : Relation α :=
  fun a b => ∃ l, r l a b

inductive Star {α : Type u} (r : Relation α) : α → α → Prop where
  | refl (a : α) : Star r a a
  | tail {a b c : α} : Star r a b → r b c → Star r a c

def Joinable {α : Type u} (r : Relation α) (a b : α) : Prop :=
  ∃ c, Star r a c ∧ Star r b c

def Confluent {α : Type u} (r : Relation α) : Prop :=
  ∀ a b c, Star r a b → Star r a c → Joinable r b c

namespace Certificate

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

end Certificate

/-!
The result is generic: it says that an accepted finite certificate, together
with a proof that its step table is complete for the semantic relation, gives
confluence. The completeness premise prevents the checker from certifying a
finite fragment while silently omitting a real rewrite step.
-/
theorem checked_complete_confluence
    {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    {r : LabeledARS α L} {lt : L → L → Prop}
    {stepB : L → α → α → Bool} {ltB : L → L → Bool}
    {key : Certificate.Edge α L → Nat}
    {steps : List (Certificate.Edge α L)}
    {certs : List (Certificate.PeakCertificate α L)}
    (hstep : ∀ l a b, stepB l a b = true ↔ r l a b)
    (hlt : ∀ l₁ l₂, ltB l₁ l₂ = true ↔ lt l₁ l₂)
    (hcheck : Certificate.checkB stepB ltB key steps certs = true)
    (hcomplete : Certificate.StepsComplete steps r)
    (wf : WellFounded lt) :
    Confluent (LabeledUnion r) := by
  sorry

end Metatheory.Palomar433
