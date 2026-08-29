import Std

/-!
# A self-contained decreasing-diagram certificate surface

This file is the shared, standard-library-only core of the Palomar artifact.
It deliberately does not import the parent Metatheory project: the selected
theorem must be auditable from its own source closure.
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

namespace Star

theorem single {α : Type u} {r : Relation α} {a b : α} (h : r a b) : Star r a b :=
  Star.tail (Star.refl a) h

theorem trans {α : Type u} {r : Relation α} {a b c : α}
    (h₁ : Star r a b) (h₂ : Star r b c) : Star r a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hstep ih => exact Star.tail ih hstep

end Star

theorem star_cases {α : Type u} {r : Relation α} {a b : α} (h : Star r a b) :
    a = b ∨ ∃ c, r a c ∧ Star r c b := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hab hbc ih =>
      rcases ih with hEq | ⟨d, had, hdb⟩
      · cases hEq
        exact Or.inr ⟨_, hbc, Star.refl _⟩
      · exact Or.inr ⟨d, had, Star.tail hdb hbc⟩

inductive StarPred {α : Type u} {L : Type v} (r : LabeledARS α L)
    (P : L → Prop) : α → α → Prop where
  | refl (a : α) : StarPred r P a a
  | tail {a b c : α} : StarPred r P a b → (l : L) → P l → r l b c → StarPred r P a c

namespace StarPred

theorem trans {α : Type u} {L : Type v} {r : LabeledARS α L} {P : L → Prop}
    {a b c : α} (h₁ : StarPred r P a b) (h₂ : StarPred r P b c) :
    StarPred r P a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ l hl hstep ih => exact StarPred.tail ih l hl hstep

theorem mono {α : Type u} {L : Type v} {r : LabeledARS α L}
    {P Q : L → Prop} (hPQ : ∀ l, P l → Q l)
    {a b : α} (h : StarPred r P a b) : StarPred r Q a b := by
  induction h with
  | refl => exact StarPred.refl _
  | tail _ l hl hstep ih => exact StarPred.tail ih l (hPQ l hl) hstep

end StarPred

theorem starPred_to_star {α : Type u} {L : Type v} {r : LabeledARS α L}
    {P : L → Prop} {a b : α} (h : StarPred r P a b) :
    Star (LabeledUnion r) a b := by
  induction h with
  | refl => exact Star.refl _
  | tail _ l _ hstep ih => exact Star.tail ih ⟨l, hstep⟩

theorem starPred_and_left {α : Type u} {L : Type v} {r : LabeledARS α L}
    {P Q : L → Prop} {a b : α}
    (h : StarPred r (fun l => P l ∧ Q l) a b) : StarPred r P a b :=
  StarPred.mono (fun _ h => h.1) h

def Joinable {α : Type u} (r : Relation α) (a b : α) : Prop :=
  ∃ c, Star r a c ∧ Star r b c

def Confluent {α : Type u} (r : Relation α) : Prop :=
  ∀ a b c, Star r a b → Star r a c → Joinable r b c

def SemiConfluent {α : Type u} (r : Relation α) : Prop :=
  ∀ a b c, r a b → Star r a c → Joinable r b c

def LocallyDecreasing {α : Type u} {L : Type v}
    (r : LabeledARS α L) (lt : L → L → Prop) : Prop :=
  ∀ a b c l₁ l₂, r l₁ a b → r l₂ a c →
    ∃ d,
      StarPred r (fun l => lt l l₁ ∧ lt l l₂) b d ∧
      StarPred r (fun l => lt l l₁ ∧ lt l l₂) c d

theorem joinable_of_starPred_lt {α : Type u} {L : Type v}
    {r : LabeledARS α L} {lt : L → L → Prop} {l₀ : L}
    (hsemi : ∀ l, lt l l₀ → ∀ {a b c : α}, r l a b →
      Star (LabeledUnion r) a c → Joinable (LabeledUnion r) b c)
    {a b c : α} (hab : StarPred r (fun l => lt l l₀) a b)
    (hac : Star (LabeledUnion r) a c) : Joinable (LabeledUnion r) b c := by
  induction hab with
  | refl => exact ⟨c, hac, Star.refl c⟩
  | tail _ l hl hstep ih =>
      obtain ⟨d, hbd, hcd⟩ := ih
      obtain ⟨e, hbe, hde⟩ := hsemi l hl hstep hbd
      exact ⟨e, hbe, Star.trans hcd hde⟩

theorem semiConfluent_of_locallyDecreasing {α : Type u} {L : Type v}
    {r : LabeledARS α L} {lt : L → L → Prop}
    (wf : WellFounded lt) (hld : LocallyDecreasing r lt) :
    SemiConfluent (LabeledUnion r) := by
  intro a b c hab hac
  obtain ⟨l₀, hab⟩ := hab
  have hlabel : ∀ l : L, ∀ {a b c : α},
      r l a b → Star (LabeledUnion r) a c →
        Joinable (LabeledUnion r) b c := by
    intro l
    refine WellFounded.induction (r := lt) wf (C := fun l => ∀ {a b c : α},
      r l a b → Star (LabeledUnion r) a c → Joinable (LabeledUnion r) b c) l ?_
    intro l ih a b c hab hac
    cases star_cases hac with
    | inl hEq =>
        subst c
        exact ⟨b, Star.refl b, Star.single ⟨l, hab⟩⟩
    | inr h =>
        obtain ⟨c₁, hac₁, hc₁c⟩ := h
        obtain ⟨l₂, hac₁⟩ := hac₁
        obtain ⟨d, hbd, hc₁d⟩ := hld a b c₁ l l₂ hab hac₁
        have hb_d : Star (LabeledUnion r) b d := starPred_to_star hbd
        have hc₁d_lt : StarPred r (fun l' => lt l' l) c₁ d :=
          starPred_and_left hc₁d
        obtain ⟨e, hde, hce⟩ :=
          joinable_of_starPred_lt (r := r) (lt := lt) (l₀ := l)
            (fun l' hl => ih l' hl) hc₁d_lt hc₁c
        exact ⟨e, Star.trans hb_d hde, hce⟩
  exact hlabel l₀ hab hac

theorem confluent_of_semiConfluent {α : Type u} {r : Relation α}
    (hsemi : SemiConfluent r) : Confluent r := by
  intro a b c hab hac
  induction hab generalizing c with
  | refl => exact ⟨c, hac, Star.refl c⟩
  | tail hab hstep ih =>
      obtain ⟨d, hbd, hcd⟩ := ih (c := c) hac
      obtain ⟨e, hbe, hde⟩ := hsemi _ _ _ hstep hbd
      exact ⟨e, hbe, Star.trans hcd hde⟩

theorem confluent_of_locallyDecreasing {α : Type u} {L : Type v}
    {r : LabeledARS α L} {lt : L → L → Prop}
    (wf : WellFounded lt) (hld : LocallyDecreasing r lt) :
    Confluent (LabeledUnion r) :=
  confluent_of_semiConfluent (semiConfluent_of_locallyDecreasing wf hld)

/-! ## Independently specified finite rewrite system -/

inductive Node where
  | root
  | left
  | right
  | join
  deriving DecidableEq, Repr, Inhabited

open Node

inductive SemanticStep : LabeledARS Node Nat where
  | rootLeft : SemanticStep 3 root left
  | rootRight : SemanticStep 3 root right
  | leftJoin : SemanticStep 2 left join
  | rightJoin : SemanticStep 2 right join
  | joinRoot : SemanticStep 1 join root

def semanticStepB (l : Nat) (a b : Node) : Bool :=
  decide ((l = 3 ∧ a = root ∧ b = left) ∨
    (l = 3 ∧ a = root ∧ b = right) ∨
    (l = 2 ∧ a = left ∧ b = join) ∨
    (l = 2 ∧ a = right ∧ b = join) ∨
    (l = 1 ∧ a = join ∧ b = root))

structure StepTriple where
  label : Nat
  source : Node
  target : Node
  deriving DecidableEq, Repr

structure PeakCertificate where
  leftStep : StepTriple
  rightStep : StepTriple
  join : Node
  leftPath : List StepTriple
  rightPath : List StepTriple
  deriving DecidableEq, Repr

def semanticSteps : List StepTriple :=
  [ ⟨3, root, left⟩
  , ⟨3, root, right⟩
  , ⟨2, left, join⟩
  , ⟨2, right, join⟩
  , ⟨1, join, root⟩ ]

def semanticCertificates : List PeakCertificate :=
  [ { leftStep := ⟨3, root, left⟩
      rightStep := ⟨3, root, right⟩
      join := join
      leftPath := [⟨2, left, join⟩]
      rightPath := [⟨2, right, join⟩] } ]

def RouteValid (r : LabeledARS Node Nat) (start finish : Node) :
    List StepTriple → Prop
  | [] => start = finish
  | s :: rest =>
      s.source = start ∧ r s.label s.source s.target ∧
        RouteValid r s.target finish rest

def RouteDecreasing (lt : Nat → Nat → Prop) (l₁ l₂ : Nat) :
    List StepTriple → Prop
  | [] => True
  | s :: rest => lt s.label l₁ ∧ lt s.label l₂ ∧ RouteDecreasing lt l₁ l₂ rest

theorem routeDecreasing_swap {lt : Nat → Nat → Prop} {l₁ l₂ : Nat}
    {path : List StepTriple} (h : RouteDecreasing lt l₁ l₂ path) :
    RouteDecreasing lt l₂ l₁ path := by
  induction path with
  | nil => trivial
  | cons s rest ih =>
      simp only [RouteDecreasing] at h ⊢
      exact ⟨h.2.1, h.1, ih h.2.2⟩

def Matches (cert : PeakCertificate) (s₁ s₂ : StepTriple) : Prop :=
  cert.leftStep = s₁ ∧ cert.rightStep = s₂

def CertificateValid (r : LabeledARS Node Nat) (lt : Nat → Nat → Prop)
    (cert : PeakCertificate) : Prop :=
  cert.leftStep.source = cert.rightStep.source ∧
    RouteValid r cert.leftStep.target cert.join cert.leftPath ∧
    RouteValid r cert.rightStep.target cert.join cert.rightPath ∧
    RouteDecreasing lt cert.leftStep.label cert.rightStep.label cert.leftPath ∧
    RouteDecreasing lt cert.leftStep.label cert.rightStep.label cert.rightPath

def StepsSound (steps : List StepTriple) (r : LabeledARS Node Nat) : Prop :=
  ∀ s, s ∈ steps → r s.label s.source s.target

def StepsComplete (steps : List StepTriple) (r : LabeledARS Node Nat) : Prop :=
  ∀ l a b, r l a b → { label := l, source := a, target := b } ∈ steps

def CoversAllPeaks (steps : List StepTriple) (certs : List PeakCertificate)
    (r : LabeledARS Node Nat) (lt : Nat → Nat → Prop) : Prop :=
  ∀ s₁ s₂, s₁ ∈ steps → s₂ ∈ steps → s₁.source = s₂.source →
    s₁ = s₂ ∨ ∃ cert ∈ certs,
      (Matches cert s₁ s₂ ∨ Matches cert s₂ s₁) ∧ CertificateValid r lt cert

def PackageValid (steps : List StepTriple) (certs : List PeakCertificate)
    (r : LabeledARS Node Nat) (lt : Nat → Nat → Prop) : Prop :=
  StepsSound steps r ∧ CoversAllPeaks steps certs r lt

def nodeOrdinal : Node → Nat
  | root => 0
  | left => 1
  | right => 2
  | join => 3

def stepOrdinal (s : StepTriple) : Nat :=
  100 * (4 * nodeOrdinal s.source + nodeOrdinal s.target) + s.label

def CanonicalCerts (certs : List PeakCertificate) : Prop :=
  ∀ cert, cert ∈ certs → cert.leftStep ≠ cert.rightStep ∧
    stepOrdinal cert.leftStep < stepOrdinal cert.rightStep

def StrictPackageValid (steps : List StepTriple) (certs : List PeakCertificate)
    (r : LabeledARS Node Nat) (lt : Nat → Nat → Prop) : Prop :=
  PackageValid steps certs r lt ∧ CanonicalCerts certs

/-! ## Executable certificate checking -/

def routeValidB (start finish : Node) : List StepTriple → Bool
  | [] => decide (start = finish)
  | s :: rest =>
      decide (s.source = start) && semanticStepB s.label s.source s.target &&
        routeValidB s.target finish rest

def routeDecreasingB (l₁ l₂ : Nat) : List StepTriple → Bool
  | [] => true
  | s :: rest =>
      decide (s.label < l₁) && decide (s.label < l₂) && routeDecreasingB l₁ l₂ rest

def matchesB (cert : PeakCertificate) (s₁ s₂ : StepTriple) : Bool :=
  decide (cert.leftStep = s₁ ∧ cert.rightStep = s₂)

def canonicalCertificateB (cert : PeakCertificate) : Bool :=
  decide (cert.leftStep ≠ cert.rightStep ∧
    stepOrdinal cert.leftStep < stepOrdinal cert.rightStep)

def canonicalCertsB (certs : List PeakCertificate) : Bool :=
  certs.all canonicalCertificateB

def certificateValidB (cert : PeakCertificate) : Bool :=
  decide (cert.leftStep.source = cert.rightStep.source) &&
    routeValidB cert.leftStep.target cert.join cert.leftPath &&
    routeValidB cert.rightStep.target cert.join cert.rightPath &&
    routeDecreasingB cert.leftStep.label cert.rightStep.label cert.leftPath &&
    routeDecreasingB cert.leftStep.label cert.rightStep.label cert.rightPath

def coversPairB (certs : List PeakCertificate) (s₁ s₂ : StepTriple) : Bool :=
  if _ : s₁.source = s₂.source then
    if _ : s₁ = s₂ then
      true
    else
      certs.any (fun cert =>
        (matchesB cert s₁ s₂ || matchesB cert s₂ s₁) && certificateValidB cert)
  else
    true

def stepsSoundB (steps : List StepTriple) : Bool :=
  steps.all (fun s => semanticStepB s.label s.source s.target)

def coversAllPeaksB (steps : List StepTriple) (certs : List PeakCertificate) : Bool :=
  steps.all (fun s₁ => steps.all (fun s₂ => coversPairB certs s₁ s₂))

def checkB (steps : List StepTriple) (certs : List PeakCertificate) : Bool :=
  canonicalCertsB certs && (stepsSoundB steps && coversAllPeaksB steps certs)

theorem semanticStepB_eq_true_iff {l : Nat} {a b : Node} :
    semanticStepB l a b = true ↔ SemanticStep l a b := by
  constructor
  · intro h
    have h' :
        (l = 3 ∧ a = root ∧ b = left) ∨
          (l = 3 ∧ a = root ∧ b = right) ∨
          (l = 2 ∧ a = left ∧ b = join) ∨
          (l = 2 ∧ a = right ∧ b = join) ∨
          (l = 1 ∧ a = join ∧ b = root) :=
      of_decide_eq_true (by simpa [semanticStepB] using h)
    rcases h' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact SemanticStep.rootLeft
    · exact SemanticStep.rootRight
    · exact SemanticStep.leftJoin
    · exact SemanticStep.rightJoin
    · exact SemanticStep.joinRoot
  · intro h
    cases h <;> rfl

theorem routeValid_of_routeValidB {start finish : Node} {path : List StepTriple}
    (h : routeValidB start finish path = true) :
    RouteValid SemanticStep start finish path := by
  induction path generalizing start with
  | nil =>
      change start = finish
      simpa [routeValidB] using h
  | cons s rest ih =>
      simp only [routeValidB, Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true h.1.1,
        semanticStepB_eq_true_iff.mp h.1.2,
        ih h.2⟩

theorem routeDecreasing_of_routeDecreasingB {l₁ l₂ : Nat} {path : List StepTriple}
    (h : routeDecreasingB l₁ l₂ path = true) :
    RouteDecreasing (· < ·) l₁ l₂ path := by
  induction path with
  | nil => trivial
  | cons s rest ih =>
      simp only [routeDecreasingB, Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true h.1.1, of_decide_eq_true h.1.2, ih h.2⟩

theorem certificateValid_of_certificateValidB {cert : PeakCertificate}
    (h : certificateValidB cert = true) :
    CertificateValid SemanticStep (· < ·) cert := by
  simp only [certificateValidB, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1.1.1,
    routeValid_of_routeValidB h.1.1.1.2,
    routeValid_of_routeValidB h.1.1.2,
    routeDecreasing_of_routeDecreasingB h.1.2,
    routeDecreasing_of_routeDecreasingB h.2⟩

theorem canonicalCertificate_of_canonicalCertificateB_eq_true
    {cert : PeakCertificate} (h : canonicalCertificateB cert = true) :
    cert.leftStep ≠ cert.rightStep ∧
      stepOrdinal cert.leftStep < stepOrdinal cert.rightStep := by
  unfold canonicalCertificateB at h
  exact of_decide_eq_true h

theorem canonicalCerts_of_canonicalCertsB_eq_true {certs : List PeakCertificate}
    (h : canonicalCertsB certs = true) : CanonicalCerts certs := by
  intro cert hmem
  exact canonicalCertificate_of_canonicalCertificateB_eq_true ((List.all_eq_true.mp h) cert hmem)

theorem matches_of_matchesB_eq_true {cert : PeakCertificate} {s₁ s₂ : StepTriple}
    (h : matchesB cert s₁ s₂ = true) : Matches cert s₁ s₂ :=
  by
    unfold matchesB at h
    have hm : cert.leftStep = s₁ ∧ cert.rightStep = s₂ := of_decide_eq_true h
    exact hm

theorem coversPair_of_coversPairB_eq_true
    {certs : List PeakCertificate} {s₁ s₂ : StepTriple}
    (hsame : s₁.source = s₂.source)
    (h : coversPairB certs s₁ s₂ = true) :
    s₁ = s₂ ∨ ∃ cert ∈ certs,
      (Matches cert s₁ s₂ ∨ Matches cert s₂ s₁) ∧
        CertificateValid SemanticStep (· < ·) cert := by
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
      (hmatch.elim (fun hm => Or.inl (matches_of_matchesB_eq_true hm))
        (fun hm => Or.inr (matches_of_matchesB_eq_true hm))),
      certificateValid_of_certificateValidB hcert.2⟩

theorem stepsSound_of_stepsSoundB_eq_true {steps : List StepTriple}
    (h : stepsSoundB steps = true) : StepsSound steps SemanticStep := by
  intro s hs
  exact semanticStepB_eq_true_iff.mp ((List.all_eq_true.mp h) s hs)

theorem coversAllPeaks_of_coversAllPeaksB_eq_true
    {steps : List StepTriple} {certs : List PeakCertificate}
    (h : coversAllPeaksB steps certs = true) :
    CoversAllPeaks steps certs SemanticStep (· < ·) := by
  intro s₁ s₂ hs₁ hs₂ hsame
  have hrow : steps.all (fun s₂ => coversPairB certs s₁ s₂) = true :=
    (List.all_eq_true.mp h) s₁ hs₁
  have hpair : coversPairB certs s₁ s₂ = true :=
    (List.all_eq_true.mp hrow) s₂ hs₂
  exact coversPair_of_coversPairB_eq_true hsame hpair

theorem strictPackageValid_of_checkB_eq_true
    {steps : List StepTriple} {certs : List PeakCertificate}
    (h : checkB steps certs = true) :
    StrictPackageValid steps certs SemanticStep (· < ·) := by
  have hparts : stepsSoundB steps = true ∧ coversAllPeaksB steps certs = true := by
    have h' : canonicalCertsB certs = true ∧
        (stepsSoundB steps = true ∧ coversAllPeaksB steps certs = true) := by
      simpa [checkB, Bool.and_eq_true] using h
    exact h'.2
  have hcanonical : canonicalCertsB certs = true := by
    have h' : canonicalCertsB certs = true ∧
        (stepsSoundB steps = true ∧ coversAllPeaksB steps certs = true) := by
      simpa [checkB, Bool.and_eq_true] using h
    exact h'.1
  exact ⟨⟨stepsSound_of_stepsSoundB_eq_true hparts.1,
      coversAllPeaks_of_coversAllPeaksB_eq_true hparts.2⟩,
    canonicalCerts_of_canonicalCertsB_eq_true hcanonical⟩

theorem packageValid_of_checkB_eq_true
    {steps : List StepTriple} {certs : List PeakCertificate}
    (h : checkB steps certs = true) :
    PackageValid steps certs SemanticStep (· < ·) := by
  exact (strictPackageValid_of_checkB_eq_true h).1

theorem routeValid_to_starPred {r : LabeledARS Node Nat} {lt : Nat → Nat → Prop}
    {l₁ l₂ : Nat} {start finish : Node} {path : List StepTriple}
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
    {steps : List StepTriple} {certs : List PeakCertificate}
    {lt : Nat → Nat → Prop}
    (hvalid : PackageValid steps certs SemanticStep lt)
    (hcomplete : StepsComplete steps SemanticStep) :
    LocallyDecreasing SemanticStep lt := by
  rcases hvalid with ⟨hsound, hcover⟩
  intro a b c l₁ l₂ hab hac
  let s₁ : StepTriple := ⟨l₁, a, b⟩
  let s₂ : StepTriple := ⟨l₂, a, c⟩
  have hs₁ : s₁ ∈ steps := hcomplete l₁ a b hab
  have hs₂ : s₂ ∈ steps := hcomplete l₂ a c hac
  rcases hcover s₁ s₂ hs₁ hs₂ rfl with hsame | ⟨cert, hcert, hmatches, hcertvalid⟩
  · have hbc : b = c := by
      simpa [s₁, s₂] using congrArg StepTriple.target hsame
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

end Metatheory.Palomar433
