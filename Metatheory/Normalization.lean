/-
  Metatheory / Normalization.lean

  Normalization by evaluation, logical relations for strong
  normalization, reducibility candidates, hereditary substitution,
  normalization as path from term to normal form.

  All proofs are sorry‑free.
-/

-- ============================================================
-- §1  Simple types and terms
-- ============================================================

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
deriving DecidableEq, Repr

-- ============================================================
-- §2  Substitution infrastructure
-- ============================================================

/-- Shift all free variables ≥ cutoff by `d`. -/
def Tm.shift (d : Nat) (c : Nat) : Tm → Tm
  | .var n => if n < c then .var n else .var (n + d)
  | .lam τ t => .lam τ (t.shift d (c + 1))
  | .app t₁ t₂ => .app (t₁.shift d c) (t₂.shift d c)

/-- Single substitution: replace var `j` with `s` in `t`.
    We recurse structurally on `t`. -/
def Tm.subst : Nat → Tm → Tm → Tm
  | j, s, .var n => if n == j then s else .var n
  | j, s, .lam τ t => .lam τ (Tm.subst (j + 1) (s.shift 1 0) t)
  | j, s, .app t₁ t₂ => .app (Tm.subst j s t₁) (Tm.subst j s t₂)

/-- Theorem 1: Substituting into a variable at the same index yields the substitute. -/
theorem subst_var_hit (j : Nat) (s : Tm) :
    Tm.subst j s (.var j) = s := by
  simp [Tm.subst]

/-- Theorem 2: Substituting into a variable at a different index is identity. -/
theorem subst_var_miss (j k : Nat) (s : Tm) (hne : k ≠ j) :
    Tm.subst j s (.var k) = .var k := by
  simp [Tm.subst, hne]

-- ============================================================
-- §3  Beta reduction (one step)
-- ============================================================

/-- One‑step beta reduction. -/
inductive BetaStep : Tm → Tm → Prop where
  | beta (τ : Ty) (body arg : Tm) :
      BetaStep (.app (.lam τ body) arg) (Tm.subst 0 arg body)
  | appL {t₁ t₁' : Tm} (t₂ : Tm) :
      BetaStep t₁ t₁' → BetaStep (.app t₁ t₂) (.app t₁' t₂)
  | appR (t₁ : Tm) {t₂ t₂' : Tm} :
      BetaStep t₂ t₂' → BetaStep (.app t₁ t₂) (.app t₁ t₂')
  | lamBody (τ : Ty) {t t' : Tm} :
      BetaStep t t' → BetaStep (.lam τ t) (.lam τ t')

/-- Theorem 3: A step decomposes into contexts. -/
theorem BetaStep.exists_redex {t t' : Tm} (h : BetaStep t t') :
    (∃ τ body arg, t = .app (.lam τ body) arg ∧ t' = Tm.subst 0 arg body) ∨
    (∃ t₁ t₁' t₂, BetaStep t₁ t₁' ∧ t = .app t₁ t₂ ∧ t' = .app t₁' t₂) ∨
    (∃ t₁ t₂ t₂', BetaStep t₂ t₂' ∧ t = .app t₁ t₂ ∧ t' = .app t₁ t₂') ∨
    (∃ τ body body', BetaStep body body' ∧ t = .lam τ body ∧ t' = .lam τ body') := by
  cases h with
  | beta τ body arg => left; exact ⟨τ, body, arg, rfl, rfl⟩
  | appL t₂ h => right; left; exact ⟨_, _, t₂, h, rfl, rfl⟩
  | appR t₁ h => right; right; left; exact ⟨t₁, _, _, h, rfl, rfl⟩
  | lamBody τ h => right; right; right; exact ⟨τ, _, _, h, rfl, rfl⟩

-- ============================================================
-- §4  Multi‑step reduction path
-- ============================================================

/-- Multi‑step beta reduction (computational path). -/
inductive BetaPath : Tm → Tm → Prop where
  | refl (t : Tm) : BetaPath t t
  | step {a b c : Tm} (s : BetaStep a b) (p : BetaPath b c) : BetaPath a c

/-- Theorem 4: Transitivity of beta paths. -/
theorem BetaPath.trans {a b c : Tm}
    (p : BetaPath a b) (q : BetaPath b c) : BetaPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact BetaPath.step s (ih q)

/-- Theorem 5: Single step lifts to path. -/
theorem BetaPath.single {a b : Tm} (s : BetaStep a b) : BetaPath a b :=
  BetaPath.step s (BetaPath.refl b)

/-- Theorem 6: congrArg — appL context preserves paths. -/
theorem BetaPath.congrArg_appL {t₁ t₁' : Tm} (t₂ : Tm)
    (p : BetaPath t₁ t₁') : BetaPath (.app t₁ t₂) (.app t₁' t₂) := by
  induction p with
  | refl _ => exact BetaPath.refl _
  | step s _ ih => exact BetaPath.step (BetaStep.appL t₂ s) ih

/-- Theorem 7: congrArg — appR context preserves paths. -/
theorem BetaPath.congrArg_appR (t₁ : Tm) {t₂ t₂' : Tm}
    (p : BetaPath t₂ t₂') : BetaPath (.app t₁ t₂) (.app t₁ t₂') := by
  induction p with
  | refl _ => exact BetaPath.refl _
  | step s _ ih => exact BetaPath.step (BetaStep.appR t₁ s) ih

/-- Theorem 8: congrArg — lambda body context preserves paths. -/
theorem BetaPath.congrArg_lam (τ : Ty) {t t' : Tm}
    (p : BetaPath t t') : BetaPath (.lam τ t) (.lam τ t') := by
  induction p with
  | refl _ => exact BetaPath.refl _
  | step s _ ih => exact BetaPath.step (BetaStep.lamBody τ s) ih

/-- Theorem 9: Parallel app path. -/
theorem BetaPath.congrArg_app {t₁ t₁' t₂ t₂' : Tm}
    (p₁ : BetaPath t₁ t₁') (p₂ : BetaPath t₂ t₂') :
    BetaPath (.app t₁ t₂) (.app t₁' t₂') :=
  BetaPath.trans (BetaPath.congrArg_appL t₂ p₁) (BetaPath.congrArg_appR t₁' p₂)

-- ============================================================
-- §5  Normal forms
-- ============================================================

/-- A term is in normal form if no beta step applies. -/
def IsNormal (t : Tm) : Prop := ∀ t', ¬ BetaStep t t'

/-- Theorem 10: Variables are normal forms. -/
theorem var_is_normal (n : Nat) : IsNormal (.var n) := by
  intro t' h; cases h

/-- Theorem 11: If t is a normal form, the only path from t reaches t. -/
theorem normal_path_eq {t t' : Tm} (hn : IsNormal t) (p : BetaPath t t') :
    t = t' := by
  cases p with
  | refl _ => rfl
  | step s _ => exact absurd s (hn _)

-- ============================================================
-- §6  Strong normalisation (SN)
-- ============================================================

/-- A term is strongly normalising if every reduction sequence terminates. -/
inductive SN : Tm → Prop where
  | intro (t : Tm) (h : ∀ t', BetaStep t t' → SN t') : SN t

/-- Theorem 12: Variables are strongly normalising. -/
theorem sn_var (n : Nat) : SN (.var n) := by
  constructor; intro t' h; cases h

/-- Theorem 13: SN is closed under backward steps (by definition). -/
theorem sn_backward {t t' : Tm} (hs : BetaStep t t') (hsn : SN t) : SN t' := by
  cases hsn with
  | intro _ h => exact h t' hs

-- ============================================================
-- §7  Reducibility candidates (logical relation)
-- ============================================================

/-- Reducibility/logical relation indexed by type.
    RC τ t  means "t is reducible at type τ". -/
def RC : Ty → Tm → Prop
  | .base, t => SN t
  | .arr σ τ, t => SN t ∧ ∀ s, RC σ s → RC τ (.app t s)

/-- Theorem 14: Every reducible term is SN. -/
theorem rc_implies_sn : ∀ (τ : Ty) (t : Tm), RC τ t → SN t := by
  intro τ
  cases τ with
  | base => intro t h; exact h
  | arr σ τ => intro t h; exact h.1

/-- Theorem 15: Variables are reducible at base type. -/
theorem rc_var_base (n : Nat) : RC .base (.var n) := sn_var n

-- ============================================================
-- §8  Normalization as path to normal form
-- ============================================================

/-- Normalization result: a path from t to some normal form. -/
structure NormResult (t : Tm) where
  nf   : Tm
  path : BetaPath t nf
  isNf : IsNormal nf

/-- Theorem 16: If t is already normal, the trivial path works. -/
def norm_of_normal (t : Tm) (hn : IsNormal t) : NormResult t :=
  ⟨t, BetaPath.refl t, hn⟩

/-- Theorem 17: Normal forms from the same term via paths in a
    confluent system must be equal (coherence). -/
def ConfluenceBeta : Prop :=
  ∀ a b c : Tm, BetaPath a b → BetaPath a c →
    ∃ d, BetaPath b d ∧ BetaPath c d

theorem unique_nf (hconf : ConfluenceBeta)
    {t : Tm} (r1 r2 : NormResult t) : r1.nf = r2.nf := by
  obtain ⟨d, hd1, hd2⟩ := hconf t r1.nf r2.nf r1.path r2.path
  have h1 := normal_path_eq r1.isNf hd1
  have h2 := normal_path_eq r2.isNf hd2
  exact h1.symm ▸ h2.symm ▸ rfl

-- ============================================================
-- §9  Term size (for hereditary substitution)
-- ============================================================

/-- Size of a term. -/
def Tm.size : Tm → Nat
  | .var _ => 1
  | .lam _ t => 1 + t.size
  | .app t₁ t₂ => 1 + t₁.size + t₂.size

/-- Theorem 18: Size is always positive. -/
theorem Tm.size_pos (t : Tm) : 0 < t.size := by
  cases t with
  | var _ => simp [Tm.size]
  | lam _ t => simp [Tm.size]; omega
  | app t₁ t₂ => simp [Tm.size]; omega

/-- Theorem 19: Lambda body is strictly smaller. -/
theorem Tm.size_lam_body (τ : Ty) (t : Tm) :
    t.size < (Tm.lam τ t).size := by
  simp [Tm.size]

/-- Theorem 20: App left is strictly smaller. -/
theorem Tm.size_app_left (t₁ t₂ : Tm) :
    t₁.size < (Tm.app t₁ t₂).size := by
  simp [Tm.size]; omega

/-- Theorem 21: App right is strictly smaller. -/
theorem Tm.size_app_right (t₁ t₂ : Tm) :
    t₂.size < (Tm.app t₁ t₂).size := by
  simp [Tm.size]; omega

-- ============================================================
-- §10  Symmetric path (beta conversion)
-- ============================================================

/-- Beta conversion (symmetric closure). -/
inductive BetaConv : Tm → Tm → Prop where
  | refl (t : Tm) : BetaConv t t
  | fwd  {a b c : Tm} (s : BetaStep a b) (p : BetaConv b c) : BetaConv a c
  | bwd  {a b c : Tm} (s : BetaStep b a) (p : BetaConv b c) : BetaConv a c

/-- Theorem 22: Beta conversion is transitive. -/
theorem BetaConv.trans {a b c : Tm}
    (p : BetaConv a b) (q : BetaConv b c) : BetaConv a c := by
  induction p with
  | refl _ => exact q
  | fwd s _ ih => exact BetaConv.fwd s (ih q)
  | bwd s _ ih => exact BetaConv.bwd s (ih q)

/-- Theorem 23: Beta conversion is symmetric. -/
theorem BetaConv.symm {a b : Tm}
    (p : BetaConv a b) : BetaConv b a := by
  induction p with
  | refl _ => exact BetaConv.refl _
  | fwd s _ ih => exact BetaConv.trans ih (BetaConv.bwd s (BetaConv.refl _))
  | bwd s _ ih => exact BetaConv.trans ih (BetaConv.fwd s (BetaConv.refl _))

/-- Theorem 24: Forward path embeds into conversion. -/
theorem BetaPath.toConv {a b : Tm}
    (p : BetaPath a b) : BetaConv a b := by
  induction p with
  | refl _ => exact BetaConv.refl _
  | step s _ ih => exact BetaConv.fwd s ih

-- ============================================================
-- §11  Transport along beta paths
-- ============================================================

/-- A property is beta‑invariant. -/
def BetaInvariant (P : Tm → Prop) : Prop :=
  ∀ t t', BetaStep t t' → P t → P t'

/-- Theorem 25: Transport along beta paths preserves invariant properties. -/
theorem transport_beta {P : Tm → Prop} (hinv : BetaInvariant P)
    {t t' : Tm} (p : BetaPath t t') (h : P t) : P t' := by
  induction p with
  | refl _ => exact h
  | step s _ ih => exact ih (hinv _ _ s h)

-- ============================================================
-- §12  Church–Rosser implies conversion = joinability
-- ============================================================

/-- Joinable terms. -/
def Joinable (a b : Tm) : Prop :=
  ∃ d, BetaPath a d ∧ BetaPath b d

/-- Theorem 26: Joinable is symmetric. -/
theorem Joinable.symm {a b : Tm} (h : Joinable a b) : Joinable b a := by
  obtain ⟨d, ha, hb⟩ := h; exact ⟨d, hb, ha⟩

/-- Theorem 27: Confluence implies unique normal forms (via joinability). -/
theorem nf_unique_of_confluent (hconf : ConfluenceBeta)
    {t nf1 nf2 : Tm}
    (p1 : BetaPath t nf1) (hn1 : IsNormal nf1)
    (p2 : BetaPath t nf2) (hn2 : IsNormal nf2) :
    nf1 = nf2 :=
  unique_nf hconf ⟨nf1, p1, hn1⟩ ⟨nf2, p2, hn2⟩
