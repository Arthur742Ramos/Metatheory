/-
  Metatheory.TemporalTypes
  ========================
  Temporal logic types over traces: safety, liveness, fairness,
  always, eventually, until, leads-to, ranking functions.
  Pure Lean 4 — no Mathlib.
-/

namespace TemporalTypes

-- ════════════════════════════════════════════════════════════════════
-- 1. Trace model
-- ════════════════════════════════════════════════════════════════════

/-- An infinite trace is a function Nat → σ. -/
def Trace (σ : Type) := Nat → σ

/-- Suffix of a trace starting at position i. -/
def Trace.suffix {σ : Type} (t : Trace σ) (i : Nat) : Trace σ :=
  fun n => t (i + n)

-- Thm 1
theorem suffix_zero {σ : Type} (t : Trace σ) : t.suffix 0 = t := by
  funext n; simp [Trace.suffix]

-- Thm 2
theorem suffix_suffix {σ : Type} (t : Trace σ) (i j : Nat) :
    (t.suffix i).suffix j = t.suffix (i + j) := by
  funext n; simp [Trace.suffix, Nat.add_assoc]

-- Thm 3
theorem suffix_at {σ : Type} (t : Trace σ) (i : Nat) :
    (t.suffix i) 0 = t i := by
  simp [Trace.suffix]

-- ════════════════════════════════════════════════════════════════════
-- 2. LTL Propositions
-- ════════════════════════════════════════════════════════════════════

def StatePred (σ : Type) := σ → Prop

def Always {σ : Type} (P : StatePred σ) (t : Trace σ) : Prop :=
  ∀ i, P (t i)

def Eventually {σ : Type} (P : StatePred σ) (t : Trace σ) : Prop :=
  ∃ i, P (t i)

def Next {σ : Type} (P : StatePred σ) (t : Trace σ) : Prop :=
  P (t 1)

def Until {σ : Type} (P Q : StatePred σ) (t : Trace σ) : Prop :=
  ∃ j, Q (t j) ∧ ∀ i, i < j → P (t i)

def WeakUntil {σ : Type} (P Q : StatePred σ) (t : Trace σ) : Prop :=
  Until P Q t ∨ Always P t

def InfOften {σ : Type} (P : StatePred σ) (t : Trace σ) : Prop :=
  ∀ i, ∃ j, j ≥ i ∧ P (t j)

def EventuallyAlways {σ : Type} (P : StatePred σ) (t : Trace σ) : Prop :=
  ∃ i, ∀ j, j ≥ i → P (t j)

-- ════════════════════════════════════════════════════════════════════
-- 3. Core LTL theorems
-- ════════════════════════════════════════════════════════════════════

-- Thm 4
theorem always_implies_eventually {σ : Type} {P : StatePred σ} {t : Trace σ}
    (h : Always P t) : Eventually P t :=
  ⟨0, h 0⟩

-- Thm 5
theorem always_and {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (hp : Always P t) (hq : Always Q t) :
    Always (fun s => P s ∧ Q s) t :=
  fun i => ⟨hp i, hq i⟩

-- Thm 6
theorem always_and_inv {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (h : Always (fun s => P s ∧ Q s) t) :
    Always P t ∧ Always Q t :=
  ⟨fun i => (h i).1, fun i => (h i).2⟩

-- Thm 7
theorem eventually_or {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (h : Eventually P t) :
    Eventually (fun s => P s ∨ Q s) t :=
  let ⟨i, hi⟩ := h; ⟨i, Or.inl hi⟩

-- Thm 8
theorem always_mono {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (hpq : ∀ s, P s → Q s) (hp : Always P t) : Always Q t :=
  fun i => hpq _ (hp i)

-- Thm 9
theorem eventually_mono {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (hpq : ∀ s, P s → Q s) (hp : Eventually P t) : Eventually Q t :=
  let ⟨i, hi⟩ := hp; ⟨i, hpq _ hi⟩

-- Thm 10
theorem next_mono {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (hpq : ∀ s, P s → Q s) (hp : Next P t) : Next Q t :=
  hpq _ hp

-- Thm 11
theorem always_suffix {σ : Type} {P : StatePred σ} {t : Trace σ}
    (h : Always P t) (i : Nat) : Always P (t.suffix i) :=
  fun n => by simp [Trace.suffix]; exact h (i + n)

-- Thm 12
theorem eventually_suffix {σ : Type} {P : StatePred σ} {t : Trace σ} {i : Nat}
    (h : Eventually P (t.suffix i)) : Eventually P t := by
  obtain ⟨j, hj⟩ := h; exact ⟨i + j, by simp [Trace.suffix] at hj; exact hj⟩

-- Thm 13
theorem next_always {σ : Type} {P : StatePred σ} {t : Trace σ}
    (h : Always P t) : Next P t :=
  h 1

-- Thm 14
theorem until_implies_eventually {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (h : Until P Q t) : Eventually Q t :=
  let ⟨j, hj, _⟩ := h; ⟨j, hj⟩

-- Thm 15
theorem until_right_now {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (h : Q (t 0)) : Until P Q t :=
  ⟨0, h, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

-- Thm 16
theorem weakuntil_from_always {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (h : Always P t) : WeakUntil P Q t :=
  Or.inr h

-- Thm 17
theorem until_implies_weakuntil {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (h : Until P Q t) : WeakUntil P Q t :=
  Or.inl h

-- ════════════════════════════════════════════════════════════════════
-- 4. Safety and Liveness
-- ════════════════════════════════════════════════════════════════════

def Safety {σ : Type} (Inv : StatePred σ) (t : Trace σ) : Prop := Always Inv t
def Liveness {σ : Type} (Goal : StatePred σ) (t : Trace σ) : Prop := Eventually Goal t
def StrongLiveness {σ : Type} (Goal : StatePred σ) (t : Trace σ) : Prop := InfOften Goal t

-- Thm 18
theorem safety_preserved_suffix {σ : Type} {Inv : StatePred σ} {t : Trace σ}
    (h : Safety Inv t) (i : Nat) : Safety Inv (t.suffix i) :=
  always_suffix h i

-- Thm 19
theorem safety_mono {σ : Type} {I1 I2 : StatePred σ} {t : Trace σ}
    (him : ∀ s, I1 s → I2 s) (h : Safety I1 t) : Safety I2 t :=
  always_mono him h

-- Thm 20
theorem safety_and {σ : Type} {I1 I2 : StatePred σ} {t : Trace σ}
    (h1 : Safety I1 t) (h2 : Safety I2 t) :
    Safety (fun s => I1 s ∧ I2 s) t :=
  always_and h1 h2

-- Thm 21
theorem safety_implies_not_eventually_neg {σ : Type} {Inv : StatePred σ} {t : Trace σ}
    (h : Safety Inv t) : ¬Eventually (fun s => ¬Inv s) t :=
  fun ⟨i, hi⟩ => hi (h i)

-- Thm 22
theorem liveness_from_until {σ : Type} {P Goal : StatePred σ} {t : Trace σ}
    (h : Until P Goal t) : Liveness Goal t :=
  until_implies_eventually h

-- Thm 23
theorem strong_liveness_implies_liveness {σ : Type} {Goal : StatePred σ} {t : Trace σ}
    (h : StrongLiveness Goal t) : Liveness Goal t :=
  let ⟨j, _, hj⟩ := h 0; ⟨j, hj⟩

-- Thm 24
theorem strong_liveness_suffix {σ : Type} {Goal : StatePred σ} {t : Trace σ}
    (h : StrongLiveness Goal t) (i : Nat) : StrongLiveness Goal (t.suffix i) := by
  intro n
  obtain ⟨j, hj1, hj2⟩ := h (i + n)
  refine ⟨j - i, ?_, ?_⟩
  · omega
  · simp [Trace.suffix]
    have : i + (j - i) = j := by omega
    rw [this]; exact hj2

-- ════════════════════════════════════════════════════════════════════
-- 5. Fairness
-- ════════════════════════════════════════════════════════════════════

def WeakFair {σ : Type} (enabled taken : StatePred σ) (t : Trace σ) : Prop :=
  InfOften enabled t → InfOften taken t

-- Thm 25
theorem weak_fair_trivial {σ : Type} {e tk : StatePred σ} {t : Trace σ}
    (h : InfOften tk t) : WeakFair e tk t :=
  fun _ => h

-- Thm 26
theorem weak_fair_not_enabled {σ : Type} {e tk : StatePred σ} {t : Trace σ}
    (h : ¬InfOften e t) : WeakFair e tk t :=
  fun he => absurd he h

-- Thm 27
theorem infoften_mono {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (hpq : ∀ s, P s → Q s) (h : InfOften P t) : InfOften Q t :=
  fun i => let ⟨j, hj1, hj2⟩ := h i; ⟨j, hj1, hpq _ hj2⟩

-- Thm 28
theorem eventuallyAlways_implies_infoften {σ : Type} {P : StatePred σ} {t : Trace σ}
    (h : EventuallyAlways P t) : InfOften P t := by
  intro i; obtain ⟨k, hk⟩ := h
  by_cases hik : i ≤ k
  · exact ⟨k, hik, hk k (Nat.le_refl _)⟩
  · exact ⟨i, Nat.le_refl _, hk i (by omega)⟩

-- Thm 29
theorem infoften_suffix {σ : Type} {P : StatePred σ} {t : Trace σ}
    (h : InfOften P t) (i : Nat) : InfOften P (t.suffix i) := by
  intro n
  obtain ⟨j, hj1, hj2⟩ := h (i + n)
  refine ⟨j - i, ?_, ?_⟩
  · omega
  · simp [Trace.suffix]
    have : i + (j - i) = j := by omega
    rw [this]; exact hj2

-- ════════════════════════════════════════════════════════════════════
-- 6. Typed Transition System
-- ════════════════════════════════════════════════════════════════════

structure TTS (σ : Type) where
  init : StatePred σ
  step : σ → σ → Prop

def TTS.IsRun {σ : Type} (sys : TTS σ) (t : Trace σ) : Prop :=
  sys.init (t 0) ∧ ∀ i, sys.step (t i) (t (i + 1))

-- Thm 30
theorem run_suffix_step {σ : Type} {sys : TTS σ} {t : Trace σ}
    (h : sys.IsRun t) (i : Nat) : sys.step (t i) (t (i + 1)) :=
  h.2 i

-- Thm 31
theorem invariant_induction {σ : Type} {sys : TTS σ} {Inv : StatePred σ} {t : Trace σ}
    (hrun : sys.IsRun t)
    (hinit : ∀ s, sys.init s → Inv s)
    (hstep : ∀ s s', Inv s → sys.step s s' → Inv s') :
    Safety Inv t := by
  intro i; induction i with
  | zero => exact hinit _ hrun.1
  | succ n ih => exact hstep _ _ ih (hrun.2 n)

-- Thm 32
theorem invariant_strengthen {σ : Type} {sys : TTS σ}
    {I1 I2 : StatePred σ} {t : Trace σ}
    (hrun : sys.IsRun t)
    (h1init : ∀ s, sys.init s → I1 s)
    (h1step : ∀ s s', I1 s → sys.step s s' → I1 s')
    (h12 : ∀ s, I1 s → I2 s) :
    Safety I2 t :=
  safety_mono h12 (invariant_induction hrun h1init h1step)

-- ════════════════════════════════════════════════════════════════════
-- 7. Leads-to
-- ════════════════════════════════════════════════════════════════════

def LeadsTo {σ : Type} (P Q : StatePred σ) (t : Trace σ) : Prop :=
  ∀ i, P (t i) → ∃ j, j ≥ i ∧ Q (t j)

-- Thm 33
theorem leadsto_refl {σ : Type} {P : StatePred σ} {t : Trace σ} :
    LeadsTo P P t :=
  fun i hp => ⟨i, Nat.le_refl _, hp⟩

-- Thm 34
theorem leadsto_mono {σ : Type} {P Q R : StatePred σ} {t : Trace σ}
    (hpq : LeadsTo P Q t) (hqr : ∀ s, Q s → R s) : LeadsTo P R t :=
  fun i hp => let ⟨j, hj1, hj2⟩ := hpq i hp; ⟨j, hj1, hqr _ hj2⟩

-- Thm 35
theorem leadsto_trans {σ : Type} {P Q R : StatePred σ} {t : Trace σ}
    (hpq : LeadsTo P Q t) (hqr : LeadsTo Q R t) : LeadsTo P R t :=
  fun i hp =>
    let ⟨j, hj1, hj2⟩ := hpq i hp
    let ⟨k, hk1, hk2⟩ := hqr j hj2
    ⟨k, Nat.le_trans hj1 hk1, hk2⟩

-- Thm 36
theorem leadsto_weaken_left {σ : Type} {P P' Q : StatePred σ} {t : Trace σ}
    (hpp : ∀ s, P' s → P s) (hpq : LeadsTo P Q t) : LeadsTo P' Q t :=
  fun i hp => hpq i (hpp _ hp)

-- Thm 37
theorem leadsto_always_implies_infoften {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (halt : Always P t) (hlt : LeadsTo P Q t) : InfOften Q t :=
  fun i => let ⟨j, hj1, hj2⟩ := hlt i (halt i); ⟨j, hj1, hj2⟩

-- Thm 38
theorem leadsto_or {σ : Type} {P Q R : StatePred σ} {t : Trace σ}
    (hpq : LeadsTo P R t) (hqr : LeadsTo Q R t) :
    LeadsTo (fun s => P s ∨ Q s) R t :=
  fun i h => h.elim (fun hp => hpq i hp) (fun hq => hqr i hq)

-- ════════════════════════════════════════════════════════════════════
-- 8. Duality / negation laws
-- ════════════════════════════════════════════════════════════════════

-- Thm 39
theorem always_not_eventually {σ : Type} {P : StatePred σ} {t : Trace σ}
    (h : Always (fun s => ¬P s) t) : ¬Eventually P t :=
  fun ⟨i, hi⟩ => h i hi

-- Thm 40
theorem eventually_not_always {σ : Type} {P : StatePred σ} {t : Trace σ}
    (h : Eventually (fun s => ¬P s) t) : ¬Always P t :=
  fun ha => let ⟨i, hi⟩ := h; hi (ha i)

-- ════════════════════════════════════════════════════════════════════
-- 9. Until laws
-- ════════════════════════════════════════════════════════════════════

-- Thm 41
theorem until_mono_right {σ : Type} {P Q Q' : StatePred σ} {t : Trace σ}
    (hqq : ∀ s, Q s → Q' s) (h : Until P Q t) : Until P Q' t :=
  let ⟨j, hj, hp⟩ := h; ⟨j, hqq _ hj, hp⟩

-- Thm 42
theorem until_mono_left {σ : Type} {P P' Q : StatePred σ} {t : Trace σ}
    (hpp : ∀ s, P s → P' s) (h : Until P Q t) : Until P' Q t :=
  let ⟨j, hj, hp⟩ := h; ⟨j, hj, fun i hi => hpp _ (hp i hi)⟩

-- Thm 43
theorem until_or_right {σ : Type} {P Q R : StatePred σ} {t : Trace σ}
    (h : Until P Q t) : Until P (fun s => Q s ∨ R s) t :=
  until_mono_right (fun s hq => Or.inl hq) h

-- Thm 44
theorem until_conj_eventually {σ : Type} {P₁ P₂ Q₁ Q₂ : StatePred σ} {t : Trace σ}
    (h1 : Until P₁ Q₁ t) (_ : Until P₂ Q₂ t) :
    Eventually (fun s => Q₁ s ∨ Q₂ s) t :=
  let ⟨j1, hq1, _⟩ := h1; ⟨j1, Or.inl hq1⟩

-- Thm 45
theorem weakuntil_mono {σ : Type} {P P' Q Q' : StatePred σ} {t : Trace σ}
    (hpp : ∀ s, P s → P' s) (hqq : ∀ s, Q s → Q' s)
    (h : WeakUntil P Q t) : WeakUntil P' Q' t := by
  cases h with
  | inl hu => exact Or.inl (until_mono_left hpp (until_mono_right hqq hu))
  | inr ha => exact Or.inr (always_mono hpp ha)

-- ════════════════════════════════════════════════════════════════════
-- 10. Bounded properties
-- ════════════════════════════════════════════════════════════════════

def BoundedAlways {σ : Type} (P : StatePred σ) (n : Nat) (t : Trace σ) : Prop :=
  ∀ i, i ≤ n → P (t i)

def BoundedEventually {σ : Type} (P : StatePred σ) (n : Nat) (t : Trace σ) : Prop :=
  ∃ i, i ≤ n ∧ P (t i)

-- Thm 46
theorem bounded_always_mono {σ : Type} {P : StatePred σ} {n m : Nat} {t : Trace σ}
    (hmn : m ≤ n) (h : BoundedAlways P n t) : BoundedAlways P m t :=
  fun i hi => h i (Nat.le_trans hi hmn)

-- Thm 47
theorem bounded_eventually_mono {σ : Type} {P : StatePred σ} {n m : Nat} {t : Trace σ}
    (hmn : n ≤ m) (h : BoundedEventually P n t) : BoundedEventually P m t :=
  let ⟨i, hi, hp⟩ := h; ⟨i, Nat.le_trans hi hmn, hp⟩

-- Thm 48
theorem always_implies_bounded {σ : Type} {P : StatePred σ} {t : Trace σ} {n : Nat}
    (h : Always P t) : BoundedAlways P n t :=
  fun i _ => h i

-- Thm 49
theorem bounded_eventually_implies_eventually {σ : Type} {P : StatePred σ} {n : Nat} {t : Trace σ}
    (h : BoundedEventually P n t) : Eventually P t :=
  let ⟨i, _, hp⟩ := h; ⟨i, hp⟩

-- ════════════════════════════════════════════════════════════════════
-- 11. Ranking functions / well-founded termination
-- ════════════════════════════════════════════════════════════════════

def RankingWitness {σ : Type} (sys : TTS σ) (Goal : StatePred σ)
    (rank : σ → Nat) : Prop :=
  ∀ s s', sys.step s s' → ¬Goal s → rank s' < rank s

-- Thm 50
theorem ranking_implies_bounded {σ : Type} {sys : TTS σ}
    {Goal : StatePred σ} {rank : σ → Nat} {t : Trace σ}
    (hrun : sys.IsRun t) (hrank : RankingWitness sys Goal rank) :
    BoundedEventually Goal (rank (t 0)) t :=
  Classical.byContradiction fun hne => by
    -- Key: if Goal never holds up to step k, rank decreases by at least k
    have bound : ∀ k, k ≤ rank (t 0) → (∀ j, j < k → ¬Goal (t j)) →
        rank (t k) + k ≤ rank (t 0) := by
      intro k hk hng
      induction k with
      | zero => omega
      | succ n ih =>
        have := ih (by omega) (fun j hj => hng j (by omega))
        have := hrank _ _ (hrun.2 n) (hng n (by omega))
        omega
    have hng : ∀ j, j ≤ rank (t 0) → ¬Goal (t j) :=
      fun j hj hg => hne ⟨j, hj, hg⟩
    have hb := bound (rank (t 0)) (Nat.le_refl _) (fun j hj => hng j (by omega))
    have := hrank _ _ (hrun.2 (rank (t 0))) (hng (rank (t 0)) (Nat.le_refl _))
    omega

-- Thm 51
theorem ranking_implies_liveness {σ : Type} {sys : TTS σ}
    {Goal : StatePred σ} {rank : σ → Nat} {t : Trace σ}
    (hrun : sys.IsRun t) (hrank : RankingWitness sys Goal rank) :
    Liveness Goal t :=
  bounded_eventually_implies_eventually (ranking_implies_bounded hrun hrank)

-- ════════════════════════════════════════════════════════════════════
-- 12. Compositional reasoning
-- ════════════════════════════════════════════════════════════════════

def TTS.par {σ : Type} (s1 s2 : TTS σ) : TTS σ where
  init := fun s => s1.init s ∧ s2.init s
  step := fun s s' => s1.step s s' ∨ s2.step s s'

-- Thm 52
theorem par_safety {σ : Type} {s1 s2 : TTS σ} {Inv : StatePred σ} {t : Trace σ}
    (hrun : (s1.par s2).IsRun t)
    (hinit : ∀ s, s1.init s → s2.init s → Inv s)
    (hstep1 : ∀ s s', Inv s → s1.step s s' → Inv s')
    (hstep2 : ∀ s s', Inv s → s2.step s s' → Inv s') :
    Safety Inv t := by
  intro i; induction i with
  | zero => exact hinit _ hrun.1.1 hrun.1.2
  | succ n ih =>
    cases hrun.2 n with
    | inl h => exact hstep1 _ _ ih h
    | inr h => exact hstep2 _ _ ih h

-- Thm 53
theorem eventually_always_next {σ : Type} {P : StatePred σ} {t : Trace σ}
    (h : EventuallyAlways P t) : EventuallyAlways P (t.suffix 1) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, fun j hj => by simp [Trace.suffix]; exact hi (1 + j) (by omega)⟩

-- Thm 54
theorem infoften_and_eventually_always {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (hP : InfOften P t) (hQ : EventuallyAlways Q t) :
    InfOften (fun s => P s ∧ Q s) t := by
  obtain ⟨k, hk⟩ := hQ
  intro i
  obtain ⟨j, hj1, hj2⟩ := hP (Nat.max i k)
  refine ⟨j, Nat.le_trans (Nat.le_max_left i k) hj1, hj2, hk j (Nat.le_trans (Nat.le_max_right i k) hj1)⟩

-- Thm 55
theorem always_eventually_always {σ : Type} {P : StatePred σ} {t : Trace σ}
    (h : Always P t) : EventuallyAlways P t :=
  ⟨0, fun j _ => h j⟩

-- Thm 56
theorem next_and {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (hp : Next P t) (hq : Next Q t) : Next (fun s => P s ∧ Q s) t :=
  ⟨hp, hq⟩

-- Thm 57
theorem next_or_left {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (hp : Next P t) : Next (fun s => P s ∨ Q s) t :=
  Or.inl hp

-- Thm 58
theorem next_or_right {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (hq : Next Q t) : Next (fun s => P s ∨ Q s) t :=
  Or.inr hq

-- Thm 59
theorem next_impl {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (hpq : Next (fun s => P s → Q s) t) (hp : Next P t) : Next Q t :=
  hpq hp

-- ════════════════════════════════════════════════════════════════════
-- 13. Deadlock freedom
-- ════════════════════════════════════════════════════════════════════

def Stuck {σ : Type} (sys : TTS σ) (s : σ) : Prop :=
  ∀ s', ¬sys.step s s'

def DeadlockFree {σ : Type} (sys : TTS σ) (t : Trace σ) : Prop :=
  Safety (fun s => ¬Stuck sys s) t

-- Thm 60
theorem run_not_stuck {σ : Type} {sys : TTS σ} {t : Trace σ}
    (hrun : sys.IsRun t) : DeadlockFree sys t :=
  fun i hs => hs (t (i + 1)) (hrun.2 i)

-- ════════════════════════════════════════════════════════════════════
-- 14. Response and persistence
-- ════════════════════════════════════════════════════════════════════

def Response {σ : Type} (P Q : StatePred σ) (t : Trace σ) : Prop :=
  ∀ i, P (t i) → ∃ j, j ≥ i ∧ Q (t j)

def Persistence {σ : Type} (P : StatePred σ) (t : Trace σ) : Prop :=
  EventuallyAlways P t

-- Thm 61
theorem response_is_leadsto {σ : Type} {P Q : StatePred σ} {t : Trace σ} :
    Response P Q t ↔ LeadsTo P Q t :=
  Iff.rfl

-- Thm 62
theorem persistence_mono {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (hpq : ∀ s, P s → Q s) (h : Persistence P t) : Persistence Q t :=
  let ⟨i, hi⟩ := h; ⟨i, fun j hj => hpq _ (hi j hj)⟩

-- Thm 63
theorem persistence_and {σ : Type} {P Q : StatePred σ} {t : Trace σ}
    (hp : Persistence P t) (hq : Persistence Q t) :
    Persistence (fun s => P s ∧ Q s) t := by
  obtain ⟨i, hi⟩ := hp; obtain ⟨j, hj⟩ := hq
  exact ⟨Nat.max i j, fun k hk =>
    ⟨hi k (Nat.le_trans (Nat.le_max_left i j) hk),
     hj k (Nat.le_trans (Nat.le_max_right i j) hk)⟩⟩

-- Thm 64
theorem persistence_implies_infoften {σ : Type} {P : StatePred σ} {t : Trace σ}
    (h : Persistence P t) : InfOften P t :=
  eventuallyAlways_implies_infoften h

-- ════════════════════════════════════════════════════════════════════
-- 15. Safety transfer and stuttering
-- ════════════════════════════════════════════════════════════════════

-- Thm 65
theorem safety_transfer {σ : Type} {Inv : StatePred σ} {t1 t2 : Trace σ}
    (heq : ∀ i, Inv (t1 i) ↔ Inv (t2 i)) (h : Safety Inv t1) : Safety Inv t2 :=
  fun i => (heq i).mp (h i)

-- Thm 66
theorem liveness_transfer {σ : Type} {G : StatePred σ} {t1 t2 : Trace σ}
    (heq : ∀ i, G (t1 i) ↔ G (t2 i)) (h : Liveness G t1) : Liveness G t2 :=
  let ⟨i, hi⟩ := h; ⟨i, (heq i).mp hi⟩

def SameVisited {σ : Type} (t1 t2 : Trace σ) : Prop :=
  (∀ i, ∃ j, t2 j = t1 i) ∧ (∀ j, ∃ i, t1 i = t2 j)

-- Thm 67
theorem same_visited_refl {σ : Type} (t : Trace σ) : SameVisited t t :=
  ⟨fun i => ⟨i, rfl⟩, fun j => ⟨j, rfl⟩⟩

-- Thm 68
theorem same_visited_symm {σ : Type} {t1 t2 : Trace σ}
    (h : SameVisited t1 t2) : SameVisited t2 t1 :=
  ⟨h.2, h.1⟩

-- ════════════════════════════════════════════════════════════════════
-- 16. Temporal type syntax
-- ════════════════════════════════════════════════════════════════════

inductive TempTy where
  | prop   : TempTy
  | always : TempTy → TempTy
  | event  : TempTy → TempTy
  | next   : TempTy → TempTy
  | conj   : TempTy → TempTy → TempTy
  | disj   : TempTy → TempTy → TempTy
  | impl   : TempTy → TempTy → TempTy
  deriving DecidableEq, Repr

def TempTy.size : TempTy → Nat
  | .prop     => 1
  | .always A => A.size + 1
  | .event A  => A.size + 1
  | .next A   => A.size + 1
  | .conj A B => A.size + B.size + 1
  | .disj A B => A.size + B.size + 1
  | .impl A B => A.size + B.size + 1

-- Thm 69
theorem tempty_size_pos (A : TempTy) : A.size ≥ 1 := by
  cases A <;> simp [TempTy.size] <;> omega

-- Thm 70
theorem tempty_conj_size {A B : TempTy} :
    (TempTy.conj A B).size = A.size + B.size + 1 := rfl

-- Thm 71
theorem tempty_always_size {A : TempTy} :
    (TempTy.always A).size = A.size + 1 := rfl

def TempTy.depth : TempTy → Nat
  | .prop     => 0
  | .always A => A.depth + 1
  | .event A  => A.depth + 1
  | .next A   => A.depth + 1
  | .conj A B => Nat.max A.depth B.depth + 1
  | .disj A B => Nat.max A.depth B.depth + 1
  | .impl A B => Nat.max A.depth B.depth + 1

-- Thm 72
theorem tempty_depth_prop : TempTy.prop.depth = 0 := rfl

-- Thm 73
theorem tempty_depth_always {A : TempTy} :
    (TempTy.always A).depth = A.depth + 1 := rfl

-- Thm 74
theorem tempty_depth_conj {A B : TempTy} :
    (TempTy.conj A B).depth = Nat.max A.depth B.depth + 1 := rfl

-- Thm 75
theorem tempty_conj_depth_gt_left {A B : TempTy} :
    (TempTy.conj A B).depth ≥ A.depth + 1 := by
  show Nat.max A.depth B.depth + 1 ≥ A.depth + 1
  have : A.depth ≤ Nat.max A.depth B.depth := Nat.le_max_left ..
  omega

end TemporalTypes
