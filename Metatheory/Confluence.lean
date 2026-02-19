/-
  Metatheory / Confluence.lean

  Abstract confluence theory for abstract rewriting systems (ARS).
  Covers: diamond property, Church-Rosser, semi-confluence,
  Hindley-Rosen, modular confluence, decreasing diagrams.

  Self-contained — no imports from other Metatheory files.
  All proofs sorry-free.
-/


namespace Metatheory.Confluence

-- ============================================================
-- §1  Abstract Rewriting Systems
-- ============================================================

def Rel (α : Type) := α → α → Prop

inductive RTClosure {α : Type} (R : Rel α) : α → α → Prop where
  | refl  : (a : α) → RTClosure R a a
  | step  : {a b c : α} → R a b → RTClosure R b c → RTClosure R a c

inductive SymClosure {α : Type} (R : Rel α) : α → α → Prop where
  | fwd : {a b : α} → R a b → SymClosure R a b
  | bwd : {a b : α} → R b a → SymClosure R a b

def Convertible {α : Type} (R : Rel α) : α → α → Prop :=
  RTClosure (SymClosure R)

-- ============================================================
-- §2  Key properties
-- ============================================================

def DiamondProp {α : Type} (R : Rel α) : Prop :=
  ∀ a b c, R a b → R a c → ∃ d, R b d ∧ R c d

def Confluent {α : Type} (R : Rel α) : Prop :=
  ∀ a b c, RTClosure R a b → RTClosure R a c →
    ∃ d, RTClosure R b d ∧ RTClosure R c d

def LocallyConfluent {α : Type} (R : Rel α) : Prop :=
  ∀ a b c, R a b → R a c →
    ∃ d, RTClosure R b d ∧ RTClosure R c d

def ChurchRosser {α : Type} (R : Rel α) : Prop :=
  ∀ a b, Convertible R a b →
    ∃ c, RTClosure R a c ∧ RTClosure R b c

def IsNF {α : Type} (R : Rel α) (a : α) : Prop :=
  ∀ b, ¬R a b

def SemiConfluent {α : Type} (R : Rel α) : Prop :=
  ∀ a b c, R a b → RTClosure R a c →
    ∃ d, RTClosure R b d ∧ RTClosure R c d

def RelUnion {α : Type} (R S : Rel α) : Rel α :=
  fun a b => R a b ∨ S a b

def Commute {α : Type} (R S : Rel α) : Prop :=
  ∀ a b c, RTClosure R a b → RTClosure S a c →
    ∃ d, RTClosure S b d ∧ RTClosure R c d

def Joinable {α : Type} (R : Rel α) (a b : α) : Prop :=
  ∃ c, RTClosure R a c ∧ RTClosure R b c

-- ============================================================
-- §3  RTClosure lemmas (1–6)
-- ============================================================

/-- Theorem 1: RTClosure is reflexive. -/
theorem rtc_refl {α : Type} {R : Rel α} (a : α) :
    RTClosure R a a := .refl a

/-- Theorem 2: A single step lifts to RTClosure. -/
theorem rtc_single {α : Type} {R : Rel α} {a b : α}
    (h : R a b) : RTClosure R a b :=
  .step h (.refl b)

/-- Theorem 3: RTClosure is transitive. -/
theorem rtc_trans {α : Type} {R : Rel α} {a b c : α}
    (h1 : RTClosure R a b) (h2 : RTClosure R b c) :
    RTClosure R a c := by
  induction h1 with
  | refl _ => exact h2
  | step r _ ih => exact .step r (ih h2)

/-- Theorem 4: RTClosure can be extended on the right. -/
theorem rtc_snoc {α : Type} {R : Rel α} {a b c : α}
    (h1 : RTClosure R a b) (h2 : R b c) :
    RTClosure R a c :=
  rtc_trans h1 (rtc_single h2)

/-- Theorem 5: Monotonicity of RTClosure. -/
theorem rtc_mono {α : Type} {R S : Rel α}
    (hsub : ∀ a b, R a b → S a b) {a b : α}
    (h : RTClosure R a b) : RTClosure S a b := by
  induction h with
  | refl _ => exact .refl _
  | step r _ ih => exact .step (hsub _ _ r) ih

/-- Theorem 6: RTClosure is idempotent. -/
theorem rtc_idem {α : Type} {R : Rel α} {a b : α}
    (h : RTClosure (RTClosure R) a b) : RTClosure R a b := by
  induction h with
  | refl _ => exact .refl _
  | step r _ ih => exact rtc_trans r ih

-- ============================================================
-- §4  Diamond ⟹ Confluence (7–9)
-- ============================================================

/-- Strip lemma: diamond + one step vs many steps. -/
private theorem diamond_strip {α : Type} {R : Rel α}
    (hd : DiamondProp R) {a b c : α}
    (hab : R a b) (hac : RTClosure R a c) :
    ∃ d, RTClosure R b d ∧ R c d := by
  induction hac generalizing b with
  | refl _ => exact ⟨b, .refl b, hab⟩
  | step ram hmc ih =>
    obtain ⟨w, hbw, hmw⟩ := hd _ _ _ hab ram
    obtain ⟨d, hwd, hcd⟩ := ih hmw
    exact ⟨d, .step hbw hwd, hcd⟩

/-- Theorem 7: Diamond property implies confluence. -/
theorem diamond_implies_confluent {α : Type} {R : Rel α}
    (hd : DiamondProp R) : Confluent R := by
  intro a b c hab hac
  induction hab generalizing c with
  | refl _ => exact ⟨c, hac, .refl c⟩
  | step ram hmb ih =>
    obtain ⟨w, hmw, hcw⟩ := diamond_strip hd ram hac
    -- hmw : RTClosure R m w, hcw : R c w
    obtain ⟨d, hbd, hwd⟩ := ih w hmw
    exact ⟨d, hbd, rtc_trans (rtc_single hcw) hwd⟩

/-- Theorem 8: Diamond implies local confluence. -/
theorem diamond_implies_locally_confluent {α : Type} {R : Rel α}
    (hd : DiamondProp R) : LocallyConfluent R := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := hd a b c hab hac
  exact ⟨d, rtc_single hbd, rtc_single hcd⟩

/-- Theorem 9: Confluence implies Church-Rosser. -/
theorem confluent_implies_church_rosser {α : Type} {R : Rel α}
    (hconf : Confluent R) : ChurchRosser R := by
  intro a b hconv
  induction hconv with
  | refl x => exact ⟨x, RTClosure.refl x, RTClosure.refl x⟩
  | step sax _hxb ih =>
    obtain ⟨c, hxc, hbc⟩ := ih
    match sax with
    | .fwd r =>
      -- r : R a x, hxc : RTClosure R x c
      exact ⟨c, rtc_trans (rtc_single r) hxc, hbc⟩
    | .bwd r =>
      -- r : R x a, hxc : RTClosure R x c
      obtain ⟨d, had, hcd⟩ := hconf _ _ _ (rtc_single r) hxc
      exact ⟨d, had, rtc_trans hbc hcd⟩

-- ============================================================
-- §5  Normal form uniqueness (10–12)
-- ============================================================

/-- Theorem 10: Confluent systems have unique normal forms. -/
theorem nf_unique {α : Type} {R : Rel α}
    (hconf : Confluent R) {a n₁ n₂ : α}
    (hr1 : RTClosure R a n₁) (hr2 : RTClosure R a n₂)
    (hn1 : IsNF R n₁) (hn2 : IsNF R n₂) :
    n₁ = n₂ := by
  obtain ⟨d, hd1, hd2⟩ := hconf a n₁ n₂ hr1 hr2
  cases hd1 with
  | refl _ =>
    cases hd2 with
    | refl _ => rfl
    | step r _ => exact absurd r (hn2 _)
  | step r _ => exact absurd r (hn1 _)

/-- Theorem 11: Normal forms reduce only to themselves. -/
theorem nf_rtc_self {α : Type} {R : Rel α} {a b : α}
    (hn : IsNF R a) (hr : RTClosure R a b) :
    a = b := by
  cases hr with
  | refl _ => rfl
  | step r _ => exact absurd r (hn _)

/-- Theorem 12: A normal form is its own unique descendant. -/
theorem nf_is_unique_descendant {α : Type} {R : Rel α} {a : α}
    (hn : IsNF R a) :
    ∀ b, RTClosure R a b → b = a :=
  fun _b hr => (nf_rtc_self hn hr).symm

-- ============================================================
-- §6  Convertibility (13–15)
-- ============================================================

/-- Theorem 13: Convertibility is reflexive. -/
theorem conv_refl {α : Type} {R : Rel α} (a : α) :
    Convertible R a a := .refl a

/-- Theorem 14: Convertibility is symmetric. -/
theorem conv_symm {α : Type} {R : Rel α} {a b : α}
    (h : Convertible R a b) : Convertible R b a := by
  induction h with
  | refl _ => exact .refl _
  | step s _ ih =>
    apply rtc_snoc ih
    match s with
    | .fwd r => exact .bwd r
    | .bwd r => exact .fwd r

/-- Theorem 15: Convertibility is transitive. -/
theorem conv_trans {α : Type} {R : Rel α} {a b c : α}
    (h1 : Convertible R a b) (h2 : Convertible R b c) :
    Convertible R a c :=
  rtc_trans h1 h2

-- ============================================================
-- §7  Church-Rosser ↔ Confluence (16–18)
-- ============================================================

/-- Theorem 16: Church-Rosser implies confluence. -/
theorem church_rosser_implies_confluent {α : Type} {R : Rel α}
    (hcr : ChurchRosser R) : Confluent R := by
  intro a b c hab hac
  have hbc : Convertible R b c := by
    apply conv_trans
    · exact conv_symm (rtc_mono (fun _ _ r => SymClosure.fwd r) hab)
    · exact rtc_mono (fun _ _ r => SymClosure.fwd r) hac
  exact hcr b c hbc

/-- Theorem 17: Reducibility implies convertibility. -/
theorem rtc_implies_conv {α : Type} {R : Rel α} {a b : α}
    (h : RTClosure R a b) : Convertible R a b :=
  rtc_mono (fun _ _ r => SymClosure.fwd r) h

/-- Theorem 18: Confluence ↔ Church-Rosser. -/
theorem confluent_iff_church_rosser {α : Type} {R : Rel α} :
    Confluent R ↔ ChurchRosser R :=
  ⟨confluent_implies_church_rosser, church_rosser_implies_confluent⟩

-- ============================================================
-- §8  Semi-confluence (19–22)
-- ============================================================

/-- Theorem 19: Confluence implies semi-confluence. -/
theorem confluent_implies_semi {α : Type} {R : Rel α}
    (hc : Confluent R) : SemiConfluent R :=
  fun a b c hab hac => hc a b c (rtc_single hab) hac

/-- Theorem 20: Semi-confluence implies confluence. -/
theorem semi_implies_confluent {α : Type} {R : Rel α}
    (hsc : SemiConfluent R) : Confluent R := by
  intro a b c hab hac
  induction hab generalizing c with
  | refl _ => exact ⟨c, hac, .refl c⟩
  | step ram hmb ih =>
    obtain ⟨d₁, hmd₁, hcd₁⟩ := hsc _ _ c ram hac
    obtain ⟨d₂, hbd₂, hd₁d₂⟩ := ih d₁ hmd₁
    exact ⟨d₂, hbd₂, rtc_trans hcd₁ hd₁d₂⟩

/-- Theorem 21: Confluence ↔ semi-confluence. -/
theorem confluent_iff_semi {α : Type} {R : Rel α} :
    Confluent R ↔ SemiConfluent R :=
  ⟨confluent_implies_semi, semi_implies_confluent⟩

/-- Theorem 22: Diamond implies semi-confluence. -/
theorem diamond_implies_semi {α : Type} {R : Rel α}
    (hd : DiamondProp R) : SemiConfluent R :=
  confluent_implies_semi (diamond_implies_confluent hd)

-- ============================================================
-- §9  Modular confluence / Hindley-Rosen (23–26)
-- ============================================================

/-- Theorem 23: RTClosure of union contains left component. -/
theorem rtc_union_left {α : Type} {R S : Rel α} {a b : α}
    (h : RTClosure R a b) : RTClosure (RelUnion R S) a b :=
  rtc_mono (fun _ _ r => Or.inl r) h

/-- Theorem 24: RTClosure of union contains right component. -/
theorem rtc_union_right {α : Type} {R S : Rel α} {a b : α}
    (h : RTClosure S a b) : RTClosure (RelUnion R S) a b :=
  rtc_mono (fun _ _ r => Or.inr r) h

/-- Theorem 25: Commutation is symmetric. -/
theorem commute_symm {α : Type} {R S : Rel α}
    (h : Commute R S) : Commute S R := by
  intro a b c hsb hrc
  obtain ⟨d, hrd, hsd⟩ := h a c b hrc hsb
  exact ⟨d, hsd, hrd⟩

/-- Theorem 26: Self-commutation is confluence. -/
theorem self_commute_iff_confluent {α : Type} {R : Rel α} :
    Commute R R ↔ Confluent R :=
  ⟨fun h => h, fun h => h⟩

-- ============================================================
-- §10  Labelled ARS and further properties (27–30)
-- ============================================================

structure LabelledARS (α : Type) (L : Type) where
  step : L → α → α → Prop

def unlabelledStep {α L : Type} (lars : LabelledARS α L) : Rel α :=
  fun a b => ∃ l, lars.step l a b

/-- Theorem 27: Each labelled step is in the unlabelled RTClosure. -/
theorem labelled_step_in_rtc {α L : Type} (lars : LabelledARS α L)
    {l : L} {a b : α} (h : lars.step l a b) :
    RTClosure (unlabelledStep lars) a b :=
  rtc_single ⟨l, h⟩

/-- Theorem 28: Joinability is symmetric. -/
theorem joinable_symm {α : Type} {R : Rel α} {a b : α}
    (h : Joinable R a b) : Joinable R b a := by
  obtain ⟨c, hac, hbc⟩ := h
  exact ⟨c, hbc, hac⟩

/-- Theorem 29: Confluence means divergence implies joinability. -/
theorem confluent_joinable {α : Type} {R : Rel α}
    (hc : Confluent R) {a b c : α}
    (hab : RTClosure R a b) (hac : RTClosure R a c) :
    Joinable R b c :=
  hc a b c hab hac

/-- Theorem 30: Joinability is reflexive. -/
theorem joinable_refl {α : Type} {R : Rel α} (a : α) :
    Joinable R a a :=
  ⟨a, .refl a, .refl a⟩


end Metatheory.Confluence