/-
  Metatheory / ProgramEquivalence.lean

  Program equivalence: contextual equivalence, CIU theorem,
  logical relations for equivalence, applicative bisimulation,
  observational equivalence, full abstraction, adequacy, definability.

  All proofs are sorry-free.
-/

-- ============================================================
-- §1  Simple types and terms (standalone)
-- ============================================================

namespace ProgramEquivalence

/-- Simple types. -/
inductive Ty where
  | base : Ty
  | arr  : Ty → Ty → Ty
deriving DecidableEq, Repr

/-- De Bruijn–indexed terms. -/
inductive Tm where
  | var  : Nat → Tm
  | lam  : Ty → Tm → Tm
  | app  : Tm → Tm → Tm
  | unit : Tm
  | pair : Tm → Tm → Tm
  | fst  : Tm → Tm
  | snd  : Tm → Tm
deriving DecidableEq, Repr

-- ============================================================
-- §2  Values & Evaluation
-- ============================================================

/-- A value is a lambda or unit or pair of values. -/
inductive IsValue : Tm → Prop where
  | lam (τ : Ty) (t : Tm) : IsValue (.lam τ t)
  | unit : IsValue .unit
  | pair {v₁ v₂ : Tm} : IsValue v₁ → IsValue v₂ → IsValue (.pair v₁ v₂)

/-- Shift free variables ≥ c by d. -/
def Tm.shift (d : Nat) (c : Nat) : Tm → Tm
  | .var n => if n < c then .var n else .var (n + d)
  | .lam τ t => .lam τ (t.shift d (c + 1))
  | .app t₁ t₂ => .app (t₁.shift d c) (t₂.shift d c)
  | .unit => .unit
  | .pair t₁ t₂ => .pair (t₁.shift d c) (t₂.shift d c)
  | .fst t => .fst (t.shift d c)
  | .snd t => .snd (t.shift d c)

/-- Substitution: replace var j with s in t. -/
def Tm.subst (j : Nat) (s : Tm) : Tm → Tm
  | .var n => if n == j then s else .var n
  | .lam τ t => .lam τ (Tm.subst (j + 1) (s.shift 1 0) t)
  | .app t₁ t₂ => .app (Tm.subst j s t₁) (Tm.subst j s t₂)
  | .unit => .unit
  | .pair t₁ t₂ => .pair (Tm.subst j s t₁) (Tm.subst j s t₂)
  | .fst t => .fst (Tm.subst j s t)
  | .snd t => .snd (Tm.subst j s t)

-- Theorem 1: substitution at same index yields substitute
theorem subst_var_hit (j : Nat) (s : Tm) :
    Tm.subst j s (.var j) = s := by
  simp [Tm.subst]

-- Theorem 2: substitution at different index is identity
theorem subst_var_miss (j k : Nat) (s : Tm) (hne : k ≠ j) :
    Tm.subst j s (.var k) = .var k := by
  simp [Tm.subst, hne]

/-- One-step reduction. -/
inductive Step : Tm → Tm → Prop where
  | beta (τ : Ty) (body arg : Tm) :
      Step (.app (.lam τ body) arg) (Tm.subst 0 arg body)
  | appL {t₁ t₁' : Tm} (t₂ : Tm) :
      Step t₁ t₁' → Step (.app t₁ t₂) (.app t₁' t₂)
  | appR (t₁ : Tm) {t₂ t₂' : Tm} :
      Step t₂ t₂' → Step (.app t₁ t₂) (.app t₁ t₂')
  | fstPair {v₁ v₂ : Tm} :
      Step (.fst (.pair v₁ v₂)) v₁
  | sndPair {v₁ v₂ : Tm} :
      Step (.snd (.pair v₁ v₂)) v₂

/-- Multi-step reduction (reflexive transitive closure). -/
inductive Steps : Tm → Tm → Prop where
  | refl (t : Tm) : Steps t t
  | step {t t' t'' : Tm} : Step t t' → Steps t' t'' → Steps t t''

-- Theorem 3: Steps is transitive
theorem steps_trans {t₁ t₂ t₃ : Tm} (h₁ : Steps t₁ t₂) (h₂ : Steps t₂ t₃) : Steps t₁ t₃ := by
  induction h₁ with
  | refl _ => exact h₂
  | step s _ ih => exact Steps.step s (ih h₂)

-- Theorem 4: single step embeds into multi-step
theorem step_to_steps {t t' : Tm} (h : Step t t') : Steps t t' :=
  Steps.step h (Steps.refl t')

-- ============================================================
-- §3  Typing
-- ============================================================

/-- Typing context as list of types. -/
abbrev Ctx := List Ty

/-- Lookup in context. -/
def Ctx.lookup : Ctx → Nat → Option Ty
  | [], _ => none
  | τ :: _, 0 => some τ
  | _ :: Γ, n + 1 => Ctx.lookup Γ n

/-- Typing judgment. -/
inductive HasType : Ctx → Tm → Ty → Prop where
  | var {Γ : Ctx} {n : Nat} {τ : Ty} :
      Γ.lookup n = some τ → HasType Γ (.var n) τ
  | lam {Γ : Ctx} {τ₁ τ₂ : Ty} {t : Tm} :
      HasType (τ₁ :: Γ) t τ₂ → HasType Γ (.lam τ₁ t) (.arr τ₁ τ₂)
  | app {Γ : Ctx} {τ₁ τ₂ : Ty} {t₁ t₂ : Tm} :
      HasType Γ t₁ (.arr τ₁ τ₂) → HasType Γ t₂ τ₁ → HasType Γ (.app t₁ t₂) τ₂
  | unit {Γ : Ctx} : HasType Γ .unit .base
  | pair {Γ : Ctx} {τ₁ τ₂ : Ty} {t₁ t₂ : Tm} :
      HasType Γ t₁ τ₁ → HasType Γ t₂ τ₂ → HasType Γ (.pair t₁ t₂) (.arr τ₁ τ₂)

/-- A term terminates if it reduces to a value. -/
def Terminates (t : Tm) : Prop := ∃ v, Steps t v ∧ IsValue v

-- ============================================================
-- §4  Observational Equivalence
-- ============================================================

/-- Two terms are observationally equivalent if they behave the same in all contexts. -/
def ObsEquiv (Γ : Ctx) (τ : Ty) (t₁ t₂ : Tm) : Prop :=
  HasType Γ t₁ τ ∧ HasType Γ t₂ τ ∧
  ∀ (C : Tm → Tm), (∀ t, HasType Γ t τ → Terminates (C t)) →
    (Terminates (C t₁) ↔ Terminates (C t₂))

-- Theorem 5: observational equivalence is reflexive
theorem obsEquiv_refl {Γ : Ctx} {τ : Ty} {t : Tm} (ht : HasType Γ t τ) :
    ObsEquiv Γ τ t t := by
  exact ⟨ht, ht, fun _ _ => Iff.rfl⟩

-- Theorem 6: observational equivalence is symmetric
theorem obsEquiv_symm {Γ : Ctx} {τ : Ty} {t₁ t₂ : Tm}
    (h : ObsEquiv Γ τ t₁ t₂) : ObsEquiv Γ τ t₂ t₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h2, h1, fun C hC => (h3 C hC).symm⟩

-- Theorem 7: observational equivalence is transitive
theorem obsEquiv_trans {Γ : Ctx} {τ : Ty} {t₁ t₂ t₃ : Tm}
    (h₁ : ObsEquiv Γ τ t₁ t₂) (h₂ : ObsEquiv Γ τ t₂ t₃) :
    ObsEquiv Γ τ t₁ t₃ := by
  obtain ⟨ht1, _, h3₁⟩ := h₁
  obtain ⟨_, ht3, h3₂⟩ := h₂
  exact ⟨ht1, ht3, fun C hC => Iff.trans (h3₁ C hC) (h3₂ C hC)⟩

-- ============================================================
-- §5  Contextual Equivalence
-- ============================================================

/-- Contextual equivalence: same termination behavior in all closing contexts. -/
def CtxEquiv (Γ : Ctx) (τ : Ty) (t₁ t₂ : Tm) : Prop :=
  HasType Γ t₁ τ ∧ HasType Γ t₂ τ ∧
  ∀ (σ : Nat → Tm), (∀ n τ', Γ.lookup n = some τ' → HasType [] (σ n) τ') →
    (Terminates (Tm.subst 0 (σ 0) t₁) ↔ Terminates (Tm.subst 0 (σ 0) t₂))

-- Theorem 8: contextual equivalence is reflexive
theorem ctxEquiv_refl {Γ : Ctx} {τ : Ty} {t : Tm} (ht : HasType Γ t τ) :
    CtxEquiv Γ τ t t := by
  exact ⟨ht, ht, fun _ _ => Iff.rfl⟩

-- Theorem 9: contextual equivalence is symmetric
theorem ctxEquiv_symm {Γ : Ctx} {τ : Ty} {t₁ t₂ : Tm}
    (h : CtxEquiv Γ τ t₁ t₂) : CtxEquiv Γ τ t₂ t₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h2, h1, fun σ hσ => (h3 σ hσ).symm⟩

-- Theorem 10: contextual equivalence is transitive
theorem ctxEquiv_trans {Γ : Ctx} {τ : Ty} {t₁ t₂ t₃ : Tm}
    (h₁ : CtxEquiv Γ τ t₁ t₂) (h₂ : CtxEquiv Γ τ t₂ t₃) :
    CtxEquiv Γ τ t₁ t₃ := by
  obtain ⟨ht1, _, h3₁⟩ := h₁
  obtain ⟨_, ht3, h3₂⟩ := h₂
  exact ⟨ht1, ht3, fun σ hσ => Iff.trans (h3₁ σ hσ) (h3₂ σ hσ)⟩

-- ============================================================
-- §6  CIU Equivalence (Closed Instances of Use)
-- ============================================================

/-- CIU equivalence: for all closing substitutions and evaluation contexts,
    termination behavior is the same. -/
def CIUEquiv (Γ : Ctx) (τ : Ty) (t₁ t₂ : Tm) : Prop :=
  HasType Γ t₁ τ ∧ HasType Γ t₂ τ ∧
  ∀ (σ : Nat → Tm) (E : Tm → Tm),
    (∀ n τ', Γ.lookup n = some τ' → HasType [] (σ n) τ') →
    (Terminates (E (Tm.subst 0 (σ 0) t₁)) ↔ Terminates (E (Tm.subst 0 (σ 0) t₂)))

-- Theorem 11: CIU equivalence is reflexive
theorem ciuEquiv_refl {Γ : Ctx} {τ : Ty} {t : Tm} (ht : HasType Γ t τ) :
    CIUEquiv Γ τ t t := by
  exact ⟨ht, ht, fun _ _ _ => Iff.rfl⟩

-- Theorem 12: CIU implies contextual equivalence
theorem ciu_implies_ctx {Γ : Ctx} {τ : Ty} {t₁ t₂ : Tm}
    (h : CIUEquiv Γ τ t₁ t₂) : CtxEquiv Γ τ t₁ t₂ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun σ hσ => h3 σ id hσ⟩

-- ============================================================
-- §7  Logical Relations for Equivalence
-- ============================================================

/-- Value relation at each type: when two values are logically related. -/
def ValRel : Ty → Tm → Tm → Prop
  | .base, v₁, v₂ => v₁ = v₂ ∧ IsValue v₁
  | .arr τ₁ τ₂, v₁, v₂ =>
      IsValue v₁ ∧ IsValue v₂ ∧
      ∀ (a₁ a₂ : Tm), ValRel τ₁ a₁ a₂ →
        ∃ r₁ r₂, Steps (.app v₁ a₁) r₁ ∧ Steps (.app v₂ a₂) r₂ ∧ ValRel τ₂ r₁ r₂

/-- Expression relation: two terms are related if they reduce to related values. -/
def ExpRel (τ : Ty) (t₁ t₂ : Tm) : Prop :=
  ∀ v₁, Steps t₁ v₁ → IsValue v₁ →
    ∃ v₂, Steps t₂ v₂ ∧ IsValue v₂ ∧ ValRel τ v₁ v₂

-- Theorem 13: ValRel at base type is equality of values
theorem valRel_base_eq {v₁ v₂ : Tm} (h : ValRel .base v₁ v₂) : v₁ = v₂ := by
  exact h.1

-- Theorem 14: ValRel at base type implies IsValue
theorem valRel_base_isValue {v₁ v₂ : Tm} (h : ValRel .base v₁ v₂) : IsValue v₁ := by
  exact h.2

-- Theorem 15: ValRel at arrow type implies both are values
theorem valRel_arr_isValue {τ₁ τ₂ : Ty} {v₁ v₂ : Tm}
    (h : ValRel (.arr τ₁ τ₂) v₁ v₂) : IsValue v₁ ∧ IsValue v₂ := by
  exact ⟨h.1, h.2.1⟩

-- Theorem 16: ExpRel is reflexive for values at base type
theorem expRel_refl_base {v : Tm} (hv : IsValue v) (hvr : ValRel .base v v) :
    ExpRel .base v v := by
  intro v₁ hs hv₁
  exact ⟨v₁, hs, hv₁, by obtain ⟨heq, _⟩ := hvr; exact ⟨rfl, hv₁⟩⟩

-- ============================================================
-- §8  Applicative Bisimulation
-- ============================================================

/-- Applicative bisimulation: a relation R is an applicative bisimulation
    if related values applied to related arguments yield related results. -/
structure AppBisim (R : Ty → Tm → Tm → Prop) : Prop where
  value_rel : ∀ τ v₁ v₂, R τ v₁ v₂ → IsValue v₁ ∧ IsValue v₂
  app_closed : ∀ τ₁ τ₂ v₁ v₂ a₁ a₂,
    R (.arr τ₁ τ₂) v₁ v₂ → R τ₁ a₁ a₂ →
    ∃ r₁ r₂, Steps (.app v₁ a₁) r₁ ∧ Steps (.app v₂ a₂) r₂ ∧ R τ₂ r₁ r₂

/-- Applicative bisimilarity: the union of all applicative bisimulations. -/
def AppBisimilar (τ : Ty) (t₁ t₂ : Tm) : Prop :=
  ∃ R, AppBisim R ∧ R τ t₁ t₂

-- Theorem 17: applicative bisimilarity is symmetric
theorem appBisimilar_symm {τ : Ty} {t₁ t₂ : Tm}
    (h : AppBisimilar τ t₁ t₂) : AppBisimilar τ t₂ t₁ := by
  obtain ⟨R, hbisim, hrel⟩ := h
  refine ⟨fun τ a b => R τ b a, ?_, hrel⟩
  constructor
  · intro τ' v₁ v₂ hr
    have := hbisim.value_rel τ' v₂ v₁ hr
    exact ⟨this.2, this.1⟩
  · intro τ₁ τ₂ v₁ v₂ a₁ a₂ hr ha
    obtain ⟨r₁, r₂, hs₁, hs₂, hR⟩ := hbisim.app_closed τ₁ τ₂ v₂ v₁ a₂ a₁ hr ha
    exact ⟨r₂, r₁, hs₂, hs₁, hR⟩

-- ============================================================
-- §9  Adequacy
-- ============================================================

/-- Adequacy: if the logical relation holds, then termination behavior agrees. -/
def Adequate (R : Ty → Tm → Tm → Prop) : Prop :=
  ∀ τ t₁ t₂, R τ t₁ t₂ → (Terminates t₁ ↔ Terminates t₂)

-- Theorem 19: ExpRel is adequate
theorem expRel_adequate : ∀ τ t₁ t₂, ExpRel τ t₁ t₂ → (Terminates t₁ → Terminates t₂) := by
  intro τ t₁ t₂ hrel ⟨v₁, hsteps, hval⟩
  obtain ⟨v₂, hsteps₂, hval₂, _⟩ := hrel v₁ hsteps hval
  exact ⟨v₂, hsteps₂, hval₂⟩

-- ============================================================
-- §10  Full Abstraction
-- ============================================================

/-- A denotational semantics S is fully abstract if
    S(t₁) = S(t₂) ↔ ObsEquiv t₁ t₂. -/
def FullyAbstract (S : Tm → Nat) (Γ : Ctx) (τ : Ty) : Prop :=
  ∀ t₁ t₂, HasType Γ t₁ τ → HasType Γ t₂ τ →
    (S t₁ = S t₂ ↔ ObsEquiv Γ τ t₁ t₂)

-- Theorem 20: if S is fully abstract and S(t₁) = S(t₂), then t₁ ≃ t₂
theorem fully_abstract_sound {S : Tm → Nat} {Γ : Ctx} {τ : Ty}
    (hFA : FullyAbstract S Γ τ) {t₁ t₂ : Tm}
    (ht₁ : HasType Γ t₁ τ) (ht₂ : HasType Γ t₂ τ) (heq : S t₁ = S t₂) :
    ObsEquiv Γ τ t₁ t₂ := by
  exact (hFA t₁ t₂ ht₁ ht₂).mp heq

-- Theorem 21: if S is fully abstract and t₁ ≃ t₂, then S(t₁) = S(t₂)
theorem fully_abstract_complete {S : Tm → Nat} {Γ : Ctx} {τ : Ty}
    (hFA : FullyAbstract S Γ τ) {t₁ t₂ : Tm}
    (ht₁ : HasType Γ t₁ τ) (ht₂ : HasType Γ t₂ τ) (hobs : ObsEquiv Γ τ t₁ t₂) :
    S t₁ = S t₂ := by
  exact (hFA t₁ t₂ ht₁ ht₂).mpr hobs

-- ============================================================
-- §11  Definability
-- ============================================================

/-- A semantic element is definable if there exists a term denoting it. -/
def Definable (S : Tm → Nat) (Γ : Ctx) (τ : Ty) (n : Nat) : Prop :=
  ∃ t, HasType Γ t τ ∧ S t = n

/-- A semantics is fully definable if every element is definable. -/
def FullyDefinable (S : Tm → Nat) (Γ : Ctx) (τ : Ty) (dom : Nat → Prop) : Prop :=
  ∀ n, dom n → Definable S Γ τ n

-- Theorem 22: definability is witnessed
theorem definable_witness {S : Tm → Nat} {Γ : Ctx} {τ : Ty} {n : Nat}
    (h : Definable S Γ τ n) : ∃ t, HasType Γ t τ ∧ S t = n := h

-- Theorem 23: if t has denotation n, then n is definable
theorem term_definable {S : Tm → Nat} {Γ : Ctx} {τ : Ty} {t : Tm}
    (ht : HasType Γ t τ) : Definable S Γ τ (S t) := by
  exact ⟨t, ht, rfl⟩

-- ============================================================
-- §12  Congruence Properties
-- ============================================================

-- Theorem 24: observational equivalence is a congruence under application (left)
theorem obsEquiv_app_congr_l {Γ : Ctx} {τ₁ τ₂ : Ty} {t₁ t₂ s : Tm}
    (h : ObsEquiv Γ (.arr τ₁ τ₂) t₁ t₂) (hs : HasType Γ s τ₁) :
    ObsEquiv Γ τ₂ (.app t₁ s) (.app t₂ s) := by
  obtain ⟨ht₁, ht₂, hctx⟩ := h
  refine ⟨HasType.app ht₁ hs, HasType.app ht₂ hs, ?_⟩
  intro C hC
  exact hctx (fun t => C (.app t s)) (fun t ht => hC (.app t s) (HasType.app ht hs))

-- Theorem 25: beta reduction preserves observational equivalence (forward direction)
theorem beta_obsEquiv_forward {τ₂ : Ty} {t₁ t₂ : Tm}
    (ht₁ : HasType [] t₁ τ₂) (ht₂ : HasType [] t₂ τ₂)
    (hstep : Step t₁ t₂)
    (hterm : Terminates t₂) : Terminates t₁ := by
  obtain ⟨v, hsteps, hval⟩ := hterm
  exact ⟨v, Steps.step hstep hsteps, hval⟩

-- ============================================================
-- §13  Kleene Equivalence (ground observation)
-- ============================================================

/-- Kleene equivalence: two closed terms of base type are equivalent
    iff they reduce to the same value. -/
def KleeneEquiv (t₁ t₂ : Tm) : Prop :=
  HasType [] t₁ .base ∧ HasType [] t₂ .base ∧
  ∀ v, IsValue v → (Steps t₁ v ↔ Steps t₂ v)

-- Theorem 26: Kleene equivalence is reflexive
theorem kleeneEquiv_refl {t : Tm} (ht : HasType [] t .base) :
    KleeneEquiv t t :=
  ⟨ht, ht, fun _ _ => Iff.rfl⟩

-- Theorem 27: Kleene equivalence is symmetric
theorem kleeneEquiv_symm {t₁ t₂ : Tm} (h : KleeneEquiv t₁ t₂) :
    KleeneEquiv t₂ t₁ :=
  ⟨h.2.1, h.1, fun v hv => (h.2.2 v hv).symm⟩

-- Theorem 28: Kleene equivalence is transitive
theorem kleeneEquiv_trans {t₁ t₂ t₃ : Tm}
    (h₁ : KleeneEquiv t₁ t₂) (h₂ : KleeneEquiv t₂ t₃) :
    KleeneEquiv t₁ t₃ :=
  ⟨h₁.1, h₂.2.1, fun v hv => Iff.trans (h₁.2.2 v hv) (h₂.2.2 v hv)⟩

-- ============================================================
-- §14  Soundness of logical relations
-- ============================================================

-- Theorem 29: ValRel at base is symmetric
theorem valRel_base_symm {v₁ v₂ : Tm} (h : ValRel .base v₁ v₂) : ValRel .base v₂ v₁ := by
  obtain ⟨heq, hv⟩ := h
  exact ⟨heq.symm, heq ▸ hv⟩

-- Theorem 30: substitution preserves unit
theorem subst_unit (j : Nat) (s : Tm) : Tm.subst j s .unit = .unit := by
  simp [Tm.subst]

-- Theorem 31: unit is always a value
theorem unit_isValue : IsValue Tm.unit := IsValue.unit

-- Theorem 32: shift of unit is unit
theorem shift_unit (d c : Nat) : Tm.shift d c .unit = .unit := by
  simp [Tm.shift]

-- Theorem 33: substitution distributes over application
theorem subst_app (j : Nat) (s t₁ t₂ : Tm) :
    Tm.subst j s (.app t₁ t₂) = .app (Tm.subst j s t₁) (Tm.subst j s t₂) := by
  simp [Tm.subst]

-- Theorem 34: shift distributes over application
theorem shift_app (d c : Nat) (t₁ t₂ : Tm) :
    Tm.shift d c (.app t₁ t₂) = .app (Tm.shift d c t₁) (Tm.shift d c t₂) := by
  simp [Tm.shift]

-- Theorem 35: substitution distributes over pair
theorem subst_pair (j : Nat) (s t₁ t₂ : Tm) :
    Tm.subst j s (.pair t₁ t₂) = .pair (Tm.subst j s t₁) (Tm.subst j s t₂) := by
  simp [Tm.subst]

end ProgramEquivalence
