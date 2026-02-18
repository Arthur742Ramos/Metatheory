/-
# System F Strong Normalization (Full Reduction)

This module proves **strong normalization** for System F with *full* reduction
(`StrongStep`), i.e. reduction is closed under `lam` and `tlam`.

The proof follows Girard/Tait reducibility candidates, using a Kripke-style
interpretation for `∀` to stay structurally recursive.

## Proof Structure

The main theorem `strong_normalization` follows from:
1. **Reducibility candidates** (`Candidate`, `CR_Props`) - closure conditions
2. **Reducibility predicate** (`Red k ρ A M`) - Kripke-indexed logical relation
3. **CR properties for all types** (`cr_props_all`) - ~1400 lines of induction
4. **Fundamental lemma** (`fundamental_lemma`) - typing implies reducibility

## Key Lemmas

- `shiftTermUp_substTerm0`: de Bruijn commutation lemma (Pierce, TAPL, Lemma 6.2.4)
- `sn_shiftTermUp`: SN preserved by term variable shifting (backward simulation)
- `red_level_subst`: world level + type substitution (Kripke monotonicity)

## References

- Girard, Lafont & Taylor, "Proofs and Types" (1989) - Chapter 6 (System F)
- Pierce, "Types and Programming Languages" (2002) - Chapter 23
- Tait, "Intensional Interpretations of Functionals" (1967)
-/

import Metatheory.SystemF.StrongReduction
import Metatheory.SystemF.Typing

namespace Metatheory.SystemF

open Ty
open Term

/-! ## Neutral Terms -/

/-- Neutral terms (cannot be an introduction form at the head of a redex). -/
def IsNeutral : Term → Prop
  | var _ => True
  | lam _ _ => False
  | tlam _ => False
  | app _ _ => True
  | tapp _ _ => True

theorem neutral_var (n : Nat) : IsNeutral (var n) := trivial

theorem neutral_app_of_not_lam {M N : Term} (h : ∀ τ M', M ≠ lam τ M') : IsNeutral (app M N) := by
  cases M with
  | var n => simp [IsNeutral]
  | lam τ M =>
    exfalso
    exact h τ M rfl
  | app M₁ M₂ => simp [IsNeutral]
  | tlam M => simp [IsNeutral]
  | tapp M τ => simp [IsNeutral]

theorem neutral_tapp_of_not_tlam {M : Term} {τ : Ty} (h : ∀ M', M ≠ tlam M') :
    IsNeutral (tapp M τ) := by
  cases M with
  | var n => simp [IsNeutral]
  | lam τ M => simp [IsNeutral]
  | app M N => simp [IsNeutral]
  | tlam M =>
    exfalso
    exact h M rfl
  | tapp M τ' => simp [IsNeutral]

theorem neutral_app_step {M N P : Term} (hM : IsNeutral M) (hstep : app M N ⟶ₛ P) :
    (∃ M', M ⟶ₛ M' ∧ P = app M' N) ∨ (∃ N', N ⟶ₛ N' ∧ P = app M N') := by
  cases hstep with
  | beta τ M' N' =>
    -- M = lam τ M', contradicts neutrality
    have : False := by simp [IsNeutral] at hM
    exact False.elim this
  | appL h =>
    exact Or.inl ⟨_, h, rfl⟩
  | appR h =>
    exact Or.inr ⟨_, h, rfl⟩

theorem neutral_tapp_step {M : Term} {τ : Ty} {P : Term} (hM : IsNeutral M) (hstep : tapp M τ ⟶ₛ P) :
    (∃ M', M ⟶ₛ M' ∧ P = tapp M' τ) := by
  cases hstep with
  | tbeta M' τ' =>
    -- M = tlam M', contradicts neutrality
    have : False := by simp [IsNeutral] at hM
    exact False.elim this
  | tappL h =>
    exact ⟨_, h, rfl⟩

/-! ## Term-Structure Equivalence

Two terms are term-structure equivalent if they have the same constructor at each position,
differing only in type annotations. This is needed early because Candidate requires it as a field.
-/

/-- Term-structure equivalence: terms with same structure but possibly different type annotations. -/
inductive TermStructEq : Term → Term → Prop where
  | var : ∀ n, TermStructEq (var n) (var n)
  | lam : ∀ τ₁ τ₂ M₁ M₂, TermStructEq M₁ M₂ → TermStructEq (lam τ₁ M₁) (lam τ₂ M₂)
  | app : ∀ M₁ M₂ N₁ N₂, TermStructEq M₁ M₂ → TermStructEq N₁ N₂ → TermStructEq (app M₁ N₁) (app M₂ N₂)
  | tlam : ∀ M₁ M₂, TermStructEq M₁ M₂ → TermStructEq (tlam M₁) (tlam M₂)
  | tapp : ∀ M₁ M₂ τ₁ τ₂, TermStructEq M₁ M₂ → TermStructEq (tapp M₁ τ₁) (tapp M₂ τ₂)

/-- Notation for term-structure equivalence. -/
scoped infix:50 " ≈ₜ " => TermStructEq

/-- Term-structure equivalence is reflexive. -/
theorem TermStructEq.refl : ∀ M, M ≈ₜ M := by
  intro M
  induction M with
  | var n => exact TermStructEq.var n
  | lam τ M ih => exact TermStructEq.lam τ τ M M ih
  | app M N ihM ihN => exact TermStructEq.app M M N N ihM ihN
  | tlam M ih => exact TermStructEq.tlam M M ih
  | tapp M τ ih => exact TermStructEq.tapp M M τ τ ih

/-- Term-structure equivalence is symmetric. -/
theorem TermStructEq.symm {M N : Term} (h : M ≈ₜ N) : N ≈ₜ M := by
  induction h with
  | var n => exact TermStructEq.var n
  | lam τ₁ τ₂ M₁ M₂ _ ih => exact TermStructEq.lam τ₂ τ₁ M₂ M₁ ih
  | app M₁ M₂ N₁ N₂ _ _ ihM ihN => exact TermStructEq.app M₂ M₁ N₂ N₁ ihM ihN
  | tlam M₁ M₂ _ ih => exact TermStructEq.tlam M₂ M₁ ih
  | tapp M₁ M₂ τ₁ τ₂ _ ih => exact TermStructEq.tapp M₂ M₁ τ₂ τ₁ ih

/-- Term shifting preserves term-structure equivalence. -/
private theorem shiftTermUp_TermStructEq_early (d c : Nat) {M N : Term} (h : M ≈ₜ N) :
    shiftTermUp d c M ≈ₜ shiftTermUp d c N := by
  induction h generalizing c with
  | var n =>
    simp only [shiftTermUp]
    by_cases hn : n < c <;> simp [hn] <;> exact TermStructEq.var _
  | lam τ₁ τ₂ M₁ M₂ _ ih =>
    simp only [shiftTermUp]; exact TermStructEq.lam τ₁ τ₂ _ _ (ih (c + 1))
  | app M₁ M₂ N₁ N₂ _ _ ihM ihN =>
    simp only [shiftTermUp]; exact TermStructEq.app _ _ _ _ (ihM c) (ihN c)
  | tlam M₁ M₂ _ ih =>
    simp only [shiftTermUp]; exact TermStructEq.tlam _ _ (ih c)
  | tapp M₁ M₂ τ₁ τ₂ _ ih =>
    simp only [shiftTermUp]; exact TermStructEq.tapp _ _ τ₁ τ₂ (ih c)

/-- Type shifting preserves term-structure equivalence. -/
private theorem shiftTypeInTerm_TermStructEq_early (d c : Nat) {M N : Term} (h : M ≈ₜ N) :
    shiftTypeInTerm d c M ≈ₜ shiftTypeInTerm d c N := by
  induction h generalizing c with
  | var n => simp [shiftTypeInTerm]; exact TermStructEq.var n
  | lam τ₁ τ₂ M₁ M₂ _ ih =>
    simp [shiftTypeInTerm]; exact TermStructEq.lam _ _ _ _ (ih c)
  | app M₁ M₂ N₁ N₂ _ _ ihM ihN =>
    simp [shiftTypeInTerm]; exact TermStructEq.app _ _ _ _ (ihM c) (ihN c)
  | tlam M₁ M₂ _ ih =>
    simp [shiftTypeInTerm]; exact TermStructEq.tlam _ _ (ih (c + 1))
  | tapp M₁ M₂ τ₁ τ₂ _ ih =>
    simp [shiftTypeInTerm]; exact TermStructEq.tapp _ _ _ _ (ih c)

/-- Term substitution preserves term-structure equivalence. -/
private theorem substTerm_TermStructEq_early {M₁ M₂ N₁ N₂ : Term} (k : Nat)
    (hM : M₁ ≈ₜ M₂) (hN : N₁ ≈ₜ N₂) : substTerm k N₁ M₁ ≈ₜ substTerm k N₂ M₂ := by
  induction hM generalizing k N₁ N₂ with
  | var n =>
    simp only [substTerm]
    by_cases hnk : n < k
    · simp [hnk]; exact TermStructEq.var n
    · by_cases heq : n = k
      · simp [heq]; exact hN
      · simp [hnk, heq]; exact TermStructEq.var (n - 1)
  | lam τ₁ τ₂ M₁ M₂ _ ih =>
    simp only [substTerm]
    have hN' : shiftTermUp 1 0 N₁ ≈ₜ shiftTermUp 1 0 N₂ := shiftTermUp_TermStructEq_early 1 0 hN
    exact TermStructEq.lam τ₁ τ₂ _ _ (ih (k + 1) hN')
  | app M₁ M₂ P₁ P₂ _ _ ihM ihP =>
    simp only [substTerm]
    exact TermStructEq.app _ _ _ _ (ihM k hN) (ihP k hN)
  | tlam M₁ M₂ _ ih =>
    simp only [substTerm]
    have hN' : shiftTypeInTerm 1 0 N₁ ≈ₜ shiftTypeInTerm 1 0 N₂ := shiftTypeInTerm_TermStructEq_early 1 0 hN
    exact TermStructEq.tlam _ _ (ih k hN')
  | tapp M₁ M₂ τ₁ τ₂ _ ih =>
    simp only [substTerm]
    exact TermStructEq.tapp _ _ τ₁ τ₂ (ih k hN)

/-- Type substitution preserves term-structure equivalence. -/
private theorem substTypeInTerm_TermStructEq_early (k : Nat) (σ : Ty) (M : Term) :
    substTypeInTerm k σ M ≈ₜ M := by
  induction M generalizing k σ with
  | var n => simp [substTypeInTerm]; exact TermStructEq.var n
  | lam τ M ih => simp [substTypeInTerm]; exact TermStructEq.lam _ τ _ M (ih k σ)
  | app M N ihM ihN => simp [substTypeInTerm]; exact TermStructEq.app _ M _ N (ihM k σ) (ihN k σ)
  | tlam M ih => simp [substTypeInTerm]; exact TermStructEq.tlam _ M (ih (k + 1) (shiftTyUp 1 0 σ))
  | tapp M τ ih => simp [substTypeInTerm]; exact TermStructEq.tapp _ M _ τ (ih k σ)

/-- Term-structure equivalence is transitive. -/
theorem TermStructEq.trans {M N P : Term} (h₁ : M ≈ₜ N) (h₂ : N ≈ₜ P) : M ≈ₜ P := by
  induction h₁ generalizing P with
  | var n => exact h₂
  | lam τ₁ τ₂ M₁ M₂ _ ih =>
    cases h₂ with
    | lam τ₂' τ₃ M₂' M₃ h₂' => exact TermStructEq.lam τ₁ τ₃ M₁ M₃ (ih h₂')
  | app M₁ M₂ N₁ N₂ _ _ ihM ihN =>
    cases h₂ with
    | app M₂' M₃ N₂' N₃ h₂M h₂N => exact TermStructEq.app M₁ M₃ N₁ N₃ (ihM h₂M) (ihN h₂N)
  | tlam M₁ M₂ _ ih =>
    cases h₂ with
    | tlam M₂' M₃ h₂' => exact TermStructEq.tlam M₁ M₃ (ih h₂')
  | tapp M₁ M₂ τ₁ τ₂ _ ih =>
    cases h₂ with
    | tapp M₂' M₃ τ₂' τ₃ h₂' => exact TermStructEq.tapp M₁ M₃ τ₁ τ₃ (ih h₂')

/-- If M ≈ₜ N and M steps, then N steps to a term-structure equivalent result. -/
private theorem TermStructEq.step_early {M N M' : Term} (h : M ≈ₜ N) (hstep : M ⟶ₛ M') :
    ∃ N', (N ⟶ₛ N') ∧ (M' ≈ₜ N') := by
  induction h generalizing M' with
  | var n => cases hstep
  | lam τ₁ τ₂ M₁ M₂ hM ih =>
    cases hstep with
    | lam hM' =>
      obtain ⟨N', hN', hEq⟩ := ih hM'
      exact ⟨Term.lam τ₂ N', StrongStep.lam hN', TermStructEq.lam τ₁ τ₂ _ _ hEq⟩
  | app M₁ M₂ N₁ N₂ hM hN ihM ihN =>
    cases hstep with
    | beta τ body arg =>
      cases hM with
      | lam τ₁ τ₂ body₁ body₂ hbody =>
        exact ⟨substTerm0 N₂ body₂, StrongStep.beta τ₂ body₂ N₂,
               substTerm_TermStructEq_early 0 hbody hN⟩
    | appL hM' =>
      obtain ⟨M₂', hM₂', hEq⟩ := ihM hM'
      exact ⟨Term.app M₂' N₂, StrongStep.appL hM₂', TermStructEq.app _ _ _ _ hEq hN⟩
    | appR hN' =>
      obtain ⟨N₂', hN₂', hEq⟩ := ihN hN'
      exact ⟨Term.app M₂ N₂', StrongStep.appR hN₂', TermStructEq.app _ _ _ _ hM hEq⟩
  | tlam M₁ M₂ hM ih =>
    cases hstep with
    | tlam hM' =>
      obtain ⟨N', hN', hEq⟩ := ih hM'
      exact ⟨Term.tlam N', StrongStep.tlam hN', TermStructEq.tlam _ _ hEq⟩
  | tapp M₁ M₂ τ₁ τ₂ hM ih =>
    cases hstep with
    | tbeta body _ =>
      cases hM with
      | tlam body₁ body₂ hbody =>
        exact ⟨substTypeInTerm0 τ₂ body₂, StrongStep.tbeta body₂ τ₂,
               TermStructEq.trans (substTypeInTerm_TermStructEq_early 0 τ₁ body)
                 (TermStructEq.trans hbody (TermStructEq.symm (substTypeInTerm_TermStructEq_early 0 τ₂ body₂)))⟩
    | tappL hM' =>
      obtain ⟨M₂', hM₂', hEq⟩ := ih hM'
      exact ⟨Term.tapp M₂' τ₂, StrongStep.tappL hM₂', TermStructEq.tapp _ _ τ₁ τ₂ hEq⟩

/-- Term-structure equivalent terms have the same SN status. -/
theorem TermStructEq.sn_iff {M N : Term} (h : M ≈ₜ N) : SN M ↔ SN N := by
  constructor
  · intro hM
    induction hM generalizing N with
    | intro M hacc ih =>
      apply sn_intro
      intro N' hstep
      obtain ⟨M', hM', hEq⟩ := h.symm.step_early hstep
      exact ih M' hM' hEq.symm
  · intro hN
    induction hN generalizing M with
    | intro N hacc ih =>
      apply sn_intro
      intro M' hstep
      obtain ⟨N', hN', hEq⟩ := h.step_early hstep
      exact ih N' hN' hEq

/-! ## Reducibility Candidates -/

/-- A reducibility candidate for `StrongStep`. -/
structure Candidate where
  /-- World-indexed predicate (world = # type variables in scope). -/
  pred : Nat → Term → Prop
  cr1 : ∀ {k M}, pred k M → SN M
  cr2 : ∀ {k M N}, pred k M → (M ⟶ₛ N) → pred k N
  cr3 : ∀ {k M}, IsNeutral M → (∀ N, M ⟶ₛ N → pred k N) → pred k M
  /-- Weakening: extend the type-variable world by one. -/
  wk : ∀ {k M}, pred k M → pred (k + 1) (shiftTypeInTerm 1 0 M)
  /-- Type substitution with level drop: pred at level k+1 implies pred at level k after type subst.
      This is the key property for handling type instantiation in System F. -/
  tySubstLevelDrop : ∀ {k M} (σ : Ty), pred (k + 1) M → pred k (substTypeInTerm0 σ M)
  /-- Term-structure invariance: the predicate respects term-structure equivalence. -/
  termStructInv : ∀ {k M N}, M ≈ₜ N → (pred k M ↔ pred k N)

/-- Type environments interpret type variables as candidates (de Bruijn indexed). -/
abbrev TyEnv := Nat → Candidate

/-- Extend a type environment with a new innermost type variable. -/
def extendTyEnv (ρ : TyEnv) (R : Candidate) : TyEnv
  | 0 => R
  | n + 1 => ρ n

/-! ## Interpretation of Types (Logical Relation)

We interpret each type as a predicate on terms, parameterized by a type
environment `ρ`. The `∀` case is Kripke-style: we shift the term into an
extended type-variable context and apply it to the fresh type variable.
-/

/-- Reducibility predicate indexed by type, parameterized by a type environment. -/
def instFresh (M : Term) : Term :=
  match M with
  | tlam M =>
      -- This is the β-reduct of `tapp (shiftTypeInTerm 1 0 (tlam M)) (tvar 0)`.
      substTypeInTerm0 (tvar 0) (shiftTypeInTerm 1 1 M)
  | _ =>
      tapp (shiftTypeInTerm 1 0 M) (tvar 0)

def Red (k : Nat) (ρ : TyEnv) : Ty → Term → Prop
  | tvar n, M => (ρ n).pred k M
  | arr A B, M =>
      ∀ k', k ≤ k' → ∀ N, Red k' ρ A N → Red k' ρ B (app (shiftTypeInTerm (k' - k) 0 M) N)
  | all A, M =>
      ∀ k', k ≤ k' → ∀ R : Candidate,
        Red (k' + 1) (extendTyEnv ρ R) A
          (tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0))

/-! ## Next Steps

`Red` is the core logical relation. The rest of the development proves:

- Candidate closure properties for `Red` (CR1/CR2/CR3)
- The fundamental lemma for typing
- Strong normalization for closed well-typed terms

These proofs are provided below in this file.
-/

/-! ## Shifting Infrastructure -/

namespace Ty

/-- Commutation of `shiftTyUp` with one-step weakening of the cutoff. -/
theorem shiftTyUp_comm_succ (d : Nat) {b c : Nat} (hb : b ≤ c) :
    ∀ σ : Ty, shiftTyUp d (c + 1) (shiftTyUp 1 b σ) = shiftTyUp 1 b (shiftTyUp d c σ) := by
  intro σ
  induction σ generalizing b c with
  | tvar n =>
    by_cases hnb : n < b
    · have hnc : n < c := Nat.lt_of_lt_of_le hnb hb
      have hncs : n < c + 1 := Nat.lt_trans hnc (Nat.lt_succ_self c)
      simp [shiftTyUp, hnb, hnc, hncs]
    · have hb' : b ≤ n := Nat.le_of_not_gt hnb
      by_cases hnc : n < c
      · have hncs : n + 1 < c + 1 := Nat.succ_lt_succ hnc
        have hnbsd : ¬n + d < b := Nat.not_lt_of_ge (Nat.le_trans hb' (Nat.le_add_right n d))
        have hnbsd' : ¬d + n < b := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hnbsd
        simp [shiftTyUp, hnb, hnc, hncs]
      · have hncs : ¬n + 1 < c + 1 := by
          simpa [Nat.succ_lt_succ_iff] using hnc
        have hnbsd : ¬n + d < b := Nat.not_lt_of_ge (Nat.le_trans hb' (Nat.le_add_right n d))
        have hnbsd' : ¬d + n < b := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hnbsd
        simp [shiftTyUp, hnb, hnc, hncs, hnbsd', Nat.add_assoc, Nat.add_comm]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp [shiftTyUp, ih₁ hb, ih₂ hb]
  | all τ ih =>
    have hb' : b + 1 ≤ c + 1 := Nat.succ_le_succ hb
    simp [shiftTyUp, ih hb']

theorem shiftTyUp_add (d₁ d₂ c : Nat) : ∀ τ : Ty,
    shiftTyUp d₁ c (shiftTyUp d₂ c τ) = shiftTyUp (d₁ + d₂) c τ := by
  intro τ
  induction τ generalizing c with
  | tvar n =>
    by_cases hn : n < c
    · simp [shiftTyUp, hn]
    · have hn' : ¬n + d₂ < c := by
        have : c ≤ n := Nat.le_of_not_gt hn
        exact Nat.not_lt.mpr (Nat.le_trans this (Nat.le_add_right n d₂))
      simp [shiftTyUp, hn, hn']
      simp [Nat.add_left_comm, Nat.add_comm]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp [shiftTyUp, ih₁ (c := c), ih₂ (c := c)]
  | all τ ih =>
    simp [shiftTyUp, ih (c := c + 1)]

end Ty

theorem shiftTypeInTerm_shiftTermUp_comm (d c d' c' : Nat) (M : Term) :
    shiftTypeInTerm d c (shiftTermUp d' c' M) = shiftTermUp d' c' (shiftTypeInTerm d c M) := by
  induction M generalizing c c' with
  | var n =>
    by_cases hn : n < c'
    · simp [shiftTermUp, hn, shiftTypeInTerm]
    · simp [shiftTermUp, hn, shiftTypeInTerm]
  | lam τ M ih =>
    simp [shiftTermUp, shiftTypeInTerm]
    exact ih (c := c) (c' := c' + 1)
  | app M N ihM ihN =>
    simp [shiftTermUp, shiftTypeInTerm, ihM, ihN]
  | tlam M ih =>
    simp [shiftTermUp, shiftTypeInTerm, ih]
  | tapp M τ ih =>
    simp [shiftTermUp, shiftTypeInTerm, ih]

theorem shiftTypeInTerm_zero (c : Nat) : ∀ M : Term, shiftTypeInTerm 0 c M = M := by
  intro M
  induction M generalizing c with
  | var n =>
    rfl
  | lam τ M ih =>
    simp [shiftTypeInTerm, Ty.shiftTyUp_zero, ih (c := c)]
  | app M N ihM ihN =>
    simp [shiftTypeInTerm, ihM (c := c), ihN (c := c)]
  | tlam M ih =>
    simp [shiftTypeInTerm, ih (c := c + 1)]
  | tapp M τ ih =>
    simp [shiftTypeInTerm, Ty.shiftTyUp_zero, ih (c := c)]

theorem shiftTypeInTerm_add (d₁ d₂ c : Nat) : ∀ M : Term,
    shiftTypeInTerm d₁ c (shiftTypeInTerm d₂ c M) = shiftTypeInTerm (d₁ + d₂) c M := by
  intro M
  induction M generalizing c with
  | var n =>
    simp [shiftTypeInTerm]
  | lam τ M ih =>
    simp [shiftTypeInTerm, Ty.shiftTyUp_add, ih (c := c)]
  | app M N ihM ihN =>
    simp [shiftTypeInTerm, ihM (c := c), ihN (c := c)]
  | tlam M ih =>
    simp [shiftTypeInTerm, ih (c := c + 1)]
  | tapp M τ ih =>
    simp [shiftTypeInTerm, Ty.shiftTyUp_add, ih (c := c)]

theorem shiftTypeInTerm_comm_succ (d : Nat) {b c : Nat} (hb : b ≤ c) :
    ∀ M : Term, shiftTypeInTerm d (c + 1) (shiftTypeInTerm 1 b M) =
      shiftTypeInTerm 1 b (shiftTypeInTerm d c M) := by
  intro M
  induction M generalizing b c with
  | var n =>
    simp [shiftTypeInTerm]
  | lam τ M ih =>
    have hτ := Ty.shiftTyUp_comm_succ d (b := b) (c := c) hb τ
    simp [shiftTypeInTerm, hτ, ih hb]
  | app M N ihM ihN =>
    simp [shiftTypeInTerm, ihM hb, ihN hb]
  | tlam M ih =>
    have hb' : b + 1 ≤ c + 1 := Nat.succ_le_succ hb
    simpa [shiftTypeInTerm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (b := b + 1) (c := c + 1) hb'
  | tapp M τ ih =>
    have hτ := Ty.shiftTyUp_comm_succ d (b := b) (c := c) hb τ
    simp [shiftTypeInTerm, hτ, ih hb]

namespace Ty

theorem shiftTyUp_succ_after (d k : Nat) : ∀ τ : Ty,
    shiftTyUp 1 (k + d) (shiftTyUp d k τ) = shiftTyUp (d + 1) k τ := by
  intro τ
  induction τ generalizing k with
  | tvar n =>
    by_cases hnk : n < k
    · -- below the cutoff: no shifts apply
      have hnkd : n < k + d := Nat.lt_of_lt_of_le hnk (Nat.le_add_right k d)
      simp [shiftTyUp, hnk, hnkd]
    · -- above the cutoff: both shifts add
      have hnk' : k ≤ n := Nat.le_of_not_gt hnk
      have hnkd : ¬n + d < k + d := by
        exact Nat.not_lt.mpr (Nat.add_le_add_right hnk' d)
      simp [shiftTyUp, hnk, hnkd, Nat.add_assoc]
  | arr A B ihA ihB =>
    simp [shiftTyUp, ihA, ihB]
  | all A ih =>
    -- Under a binder, the cutoff increases by 1.
    have hkd : k + d + 1 = (k + 1) + d := by omega
    simp [shiftTyUp, hkd, ih (k := k + 1)]

end Ty

theorem shiftTypeInTerm_succ_after (d k : Nat) : ∀ M : Term,
    shiftTypeInTerm 1 (k + d) (shiftTypeInTerm d k M) = shiftTypeInTerm (d + 1) k M := by
  intro M
  induction M generalizing k with
  | var n =>
    simp [shiftTypeInTerm]
  | lam τ M ih =>
    simp [shiftTypeInTerm, Ty.shiftTyUp_succ_after, ih]
  | app M N ihM ihN =>
    simp [shiftTypeInTerm, ihM, ihN]
  | tlam M ih =>
    have hkd : k + d + 1 = (k + 1) + d := by omega
    simp [shiftTypeInTerm, hkd, ih (k := k + 1)]
  | tapp M τ ih =>
    simp [shiftTypeInTerm, Ty.shiftTyUp_succ_after, ih]

/-! ## Shifting commutes with substitution -/

theorem shiftTypeInTerm_substTerm (d c : Nat) :
    ∀ (k : Nat) (N M : Term),
      shiftTypeInTerm d c (substTerm k N M) =
        substTerm k (shiftTypeInTerm d c N) (shiftTypeInTerm d c M) := by
  intro k N M
  induction M generalizing c k N with
  | var n =>
    simp [substTerm, shiftTypeInTerm]
    by_cases hnk : n < k
    · simp [shiftTypeInTerm, hnk]
    · by_cases hEq : n = k
      · simp [hEq]
      · simp [shiftTypeInTerm, hnk, hEq]
  | lam τ M ih =>
    simp [substTerm, shiftTypeInTerm]
    have h := ih (c := c) (k := k + 1) (N := shiftTermUp 1 0 N)
    simpa [shiftTypeInTerm_shiftTermUp_comm] using h
  | app M₁ M₂ ih₁ ih₂ =>
    simp [substTerm, shiftTypeInTerm, ih₁, ih₂]
  | tlam M ih =>
    simp [substTerm, shiftTypeInTerm]
    have h := ih (c := c + 1) (k := k) (N := shiftTypeInTerm 1 0 N)
    have hN :
        shiftTypeInTerm d (c + 1) (shiftTypeInTerm 1 0 N) =
          shiftTypeInTerm 1 0 (shiftTypeInTerm d c N) :=
      shiftTypeInTerm_comm_succ d (b := 0) (c := c) (Nat.zero_le c) N
    simpa [hN] using h
  | tapp M τ ih =>
    simp [substTerm, shiftTypeInTerm, ih]

theorem shiftTypeInTerm_substTerm0 (d c : Nat) (N M : Term) :
    shiftTypeInTerm d c (substTerm0 N M) =
      substTerm0 (shiftTypeInTerm d c N) (shiftTypeInTerm d c M) := by
  unfold substTerm0
  simpa using shiftTypeInTerm_substTerm (d := d) (c := c) (k := 0) (N := N) (M := M)

namespace Ty

theorem shiftTyUp_substTy_lt (d c k : Nat) (hk : k < c + 1) (σ : Ty) :
    ∀ τ : Ty, shiftTyUp d c (substTy k σ τ) = substTy k (shiftTyUp d c σ) (shiftTyUp d (c + 1) τ) := by
  intro τ
  induction τ generalizing c k σ with
  | tvar n =>
    by_cases hnk : n < k
    · have hk_le : k ≤ c := Nat.le_of_lt_succ hk
      have hncc : n < c := Nat.lt_of_lt_of_le hnk hk_le
      have hnc : n < c + 1 := Nat.lt_trans hncc (Nat.lt_succ_self c)
      simp [substTy, shiftTyUp, hnk, hncc, hnc]
    · by_cases hEq : n = k
      · subst hEq
        -- after substitution, the goal is immediate since `shiftTyUp d (c+1) (tvar n) = tvar n`
        -- (because `n < c+1`) and `substTy n _ (tvar n)` selects the substituted type.
        simp [substTy, shiftTyUp, hk]
      · have hgt : k < n := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnk) (Ne.symm hEq)
        by_cases hnc : n < c + 1
        · have hnc' : n - 1 < c := by omega
          simp [substTy, shiftTyUp, hnk, hEq, hnc, hnc']
        · have hge : c ≤ n - 1 := by omega
          have hnc' : ¬n - 1 < c := Nat.not_lt_of_ge hge
          have hnkd : ¬n + d < k := Nat.not_lt_of_ge (Nat.le_trans (Nat.le_of_lt hgt) (Nat.le_add_right n d))
          have hneq : n + d ≠ k := by
            have hlt : k < n + d := Nat.lt_of_lt_of_le hgt (Nat.le_add_right n d)
            exact (Nat.ne_of_lt hlt).symm
          have hnkd' : ¬d + n < k := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hnkd
          have hneq' : d + n ≠ k := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hneq
          have hsub : d + (n - 1) = d + n - 1 := by omega
          simp [substTy, shiftTyUp, hnk, hEq, hnc, hnc', hnkd', hneq', hsub,
            Nat.add_comm]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp [substTy, shiftTyUp,
      ih₁ (c := c) (k := k) hk (σ := σ),
      ih₂ (c := c) (k := k) hk (σ := σ)]
  | all τ ih =>
    have hk' : k + 1 < (c + 1) + 1 := Nat.succ_lt_succ hk
    have hσ :
        shiftTyUp d (c + 1) (shiftTyUp 1 0 σ) = shiftTyUp 1 0 (shiftTyUp d c σ) :=
      shiftTyUp_comm_succ d (b := 0) (c := c) (Nat.zero_le c) σ
    simp [substTy, shiftTyUp,
      ih (c := c + 1) (k := k + 1) hk' (σ := shiftTyUp 1 0 σ),
      hσ]

end Ty

theorem shiftTypeInTerm_substTypeInTerm (d c : Nat) :
    ∀ (k : Nat) (_hk : k < c + 1) (σ : Ty) (M : Term),
      shiftTypeInTerm d c (substTypeInTerm k σ M) =
        substTypeInTerm k (shiftTyUp d c σ) (shiftTypeInTerm d (c + 1) M) := by
  intro k hk σ M
  induction M generalizing c k σ with
  | var n =>
    simp [substTypeInTerm, shiftTypeInTerm]
  | lam τ M ih =>
    have hτ := Ty.shiftTyUp_substTy_lt (d := d) (c := c) (k := k) hk (σ := σ) τ
    simp [substTypeInTerm, shiftTypeInTerm, hτ, ih (c := c) (k := k) hk (σ := σ)]
  | app M N ihM ihN =>
    simp [substTypeInTerm, shiftTypeInTerm,
      ihM (c := c) (k := k) hk (σ := σ),
      ihN (c := c) (k := k) hk (σ := σ)]
  | tlam M ih =>
    have hk' : k + 1 < (c + 1) + 1 := Nat.succ_lt_succ hk
    have hσ :
        shiftTyUp d (c + 1) (shiftTyUp 1 0 σ) = shiftTyUp 1 0 (shiftTyUp d c σ) :=
      Ty.shiftTyUp_comm_succ d (b := 0) (c := c) (Nat.zero_le c) σ
    simp [substTypeInTerm, shiftTypeInTerm,
      ih (c := c + 1) (k := k + 1) hk' (σ := shiftTyUp 1 0 σ),
      hσ]
  | tapp M τ ih =>
    have hτ := Ty.shiftTyUp_substTy_lt (d := d) (c := c) (k := k) hk (σ := σ) τ
    simp [substTypeInTerm, shiftTypeInTerm, hτ, ih (c := c) (k := k) hk (σ := σ)]

theorem shiftTypeInTerm_substTypeInTerm0 (d c : Nat) (σ : Ty) (M : Term) :
    shiftTypeInTerm d c (substTypeInTerm0 σ M) =
      substTypeInTerm0 (shiftTyUp d c σ) (shiftTypeInTerm d (c + 1) M) := by
  unfold substTypeInTerm0
  have hk : (0 : Nat) < c + 1 := Nat.zero_lt_succ c
  simpa using shiftTypeInTerm_substTypeInTerm (d := d) (c := c) (k := 0) hk (σ := σ) (M := M)

/-! ## Type Substitution Infrastructure -/

namespace Ty

theorem substTy_shiftTyUp_cancel (k : Nat) (σ : Ty) : ∀ τ : Ty, substTy k σ (shiftTyUp 1 k τ) = τ := by
  intro τ
  induction τ generalizing k σ with
  | tvar n =>
    by_cases hnk : n < k
    · simp [shiftTyUp, substTy, hnk]
    · have hnks : ¬n + 1 < k := by omega
      have hneq : n + 1 ≠ k := by omega
      simp [shiftTyUp, substTy, hnk, hnks, hneq]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp [shiftTyUp, substTy, ih₁, ih₂]
  | all τ ih =>
    simp [shiftTyUp, substTy, ih (k := k + 1) (σ := shiftTyUp 1 0 σ)]

theorem substTy_succ_shiftTyUp_comm (c k : Nat) (σ : Ty) (hc : c ≤ k) :
    ∀ τ : Ty, substTy (k + 1) (shiftTyUp 1 c σ) (shiftTyUp 1 c τ) = shiftTyUp 1 c (substTy k σ τ) := by
  intro τ
  induction τ generalizing c k σ with
  | tvar n =>
    by_cases hnc : n < c
    · have hnk : n < k := Nat.lt_of_lt_of_le hnc hc
      have hnks : n < k + 1 := Nat.lt_trans hnk (Nat.lt_succ_self k)
      simp [shiftTyUp, substTy, hnc, hnk, hnks]
    · have hgec : c ≤ n := Nat.le_of_not_gt hnc
      by_cases hnk : n < k
      · have hnks : n + 1 < k + 1 := Nat.succ_lt_succ hnk
        simp [shiftTyUp, substTy, hnc, hnk, hnks]
      · by_cases hEq : n = k
        · have hkc : ¬k < c := by simpa [hEq] using hnc
          simp [shiftTyUp, substTy, hEq, hkc]
        · have hgt : k < n := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnk) (Ne.symm hEq)
          have hnks : ¬n + 1 < k + 1 := by omega
          have hneq : n + 1 ≠ k + 1 := by omega
          have hnc' : ¬n - 1 < c := by omega
          have hshift₁ : shiftTyUp 1 c (tvar n) = tvar (n + 1) := by
            simp [shiftTyUp, hnc]
          have hshift₂ : shiftTyUp 1 c (tvar (n - 1)) = tvar n := by
            have hn' : n - 1 + 1 = n := by omega
            simp [shiftTyUp, hnc', hn']
          -- LHS: substitute after shifting yields `tvar n`.
          -- RHS: shift after substitution (which yields `tvar (n-1)`) yields `tvar n`.
          rw [hshift₁]
          have hsub : (n + 1) - 1 = n := by omega
          simp [substTy, hnks, hsub]
          simp [hnk, hEq]
          rw [hshift₂]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp [shiftTyUp, substTy, ih₁ (hc := hc), ih₂ (hc := hc)]
  | all τ ih =>
    have hc' : c + 1 ≤ k + 1 := Nat.succ_le_succ hc
    have hσ :
        shiftTyUp 1 0 (shiftTyUp 1 c σ) = shiftTyUp 1 (c + 1) (shiftTyUp 1 0 σ) := by
      simpa using (Eq.symm (shiftTyUp_comm_succ (d := 1) (b := 0) (c := c) (Nat.zero_le c) σ))
    simp [shiftTyUp, substTy, hσ, ih (c := c + 1) (k := k + 1) (σ := shiftTyUp 1 0 σ) (hc := hc')]

theorem substTy_substTy (j k : Nat) (hj : j ≤ k) (σ τ : Ty) :
    ∀ A : Ty,
      substTy k σ (substTy j τ A) =
        substTy j (substTy k σ τ) (substTy (k + 1) (shiftTyUp 1 j σ) A) := by
  intro A
  induction A generalizing j k σ τ with
  | tvar n =>
    by_cases hnj : n < j
    · have hnk : n < k := Nat.lt_of_lt_of_le hnj hj
      have hnks : n < k + 1 := Nat.lt_trans hnk (Nat.lt_succ_self k)
      simp [substTy, hnj, hnk, hnks]
    · by_cases hEqj : n = j
      · have hjlt : j < k + 1 := Nat.lt_of_le_of_lt hj (Nat.lt_succ_self k)
        simp [substTy, hEqj, hjlt]
      · have hgtj : j < n := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnj) (Ne.symm hEqj)
        by_cases hEqk : n = k + 1
        · have hnkj : ¬k + 1 < j := by omega
          have hneqj : k + 1 ≠ j := by omega
          have hcancel : substTy j (substTy k σ τ) (shiftTyUp 1 j σ) = σ := by
            simpa using (substTy_shiftTyUp_cancel (k := j) (σ := substTy k σ τ) σ)
          simp [substTy, hEqk, hnkj, hneqj, hcancel]
        · by_cases hnlt : n < k + 1
          · have hnlt' : n - 1 < k := by omega
            simp [substTy, hnj, hEqj, hnlt, hnlt']
          · have hngt : k + 1 < n := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnlt) (Ne.symm hEqk)
            have hnge : ¬n < k + 1 := Nat.not_lt_of_ge (Nat.le_of_lt hngt)
            have hnge' : ¬n - 1 < k := by omega
            have hngej : ¬n - 1 < j := by omega
            have hneqj : n - 1 ≠ j := by omega
            have hneqk : n - 1 ≠ k := by omega
            simp [substTy, hnj, hEqj, hEqk, hnge, hnge', hngej, hneqj, hneqk]
  | arr A B ihA ihB =>
    simp [substTy, ihA (hj := hj), ihB (hj := hj)]
  | all A ih =>
    have hj' : j + 1 ≤ k + 1 := Nat.succ_le_succ hj
    have hσ :
        shiftTyUp 1 0 (shiftTyUp 1 j σ) = shiftTyUp 1 (j + 1) (shiftTyUp 1 0 σ) := by
      simpa using (Eq.symm (shiftTyUp_comm_succ (d := 1) (b := 0) (c := j) (Nat.zero_le j) σ))
    have hτ :
        shiftTyUp 1 0 (substTy k σ τ) = substTy (k + 1) (shiftTyUp 1 0 σ) (shiftTyUp 1 0 τ) := by
      simpa using
        (Eq.symm (substTy_succ_shiftTyUp_comm (c := 0) (k := k) (σ := σ) (Nat.zero_le k) τ))
    simp [substTy, hσ, hτ,
      ih (j := j + 1) (k := k + 1) (hj := hj') (σ := shiftTyUp 1 0 σ) (τ := shiftTyUp 1 0 τ)]

theorem substTy_substTy0 (k : Nat) (σ τ : Ty) : ∀ A : Ty,
    substTy k σ (substTy0 τ A) = substTy0 (substTy k σ τ) (substTy (k + 1) (shiftTyUp 1 0 σ) A) := by
  intro A
  simpa [substTy0] using substTy_substTy (j := 0) (k := k) (hj := Nat.zero_le k) (σ := σ) (τ := τ) A

end Ty

theorem substTypeInTerm_shiftTermUp_comm (k : Nat) (σ : Ty) (d c : Nat) :
    ∀ M : Term, substTypeInTerm k σ (shiftTermUp d c M) = shiftTermUp d c (substTypeInTerm k σ M) := by
  intro M
  induction M generalizing c k σ with
  | var n =>
    by_cases hn : n < c
    · simp [shiftTermUp, substTypeInTerm, hn]
    · simp [shiftTermUp, substTypeInTerm, hn]
  | lam τ M ih =>
    simp [shiftTermUp, substTypeInTerm, ih (c := c + 1)]
  | app M N ihM ihN =>
    simp [shiftTermUp, substTypeInTerm, ihM, ihN]
  | tlam M ih =>
    simp [shiftTermUp, substTypeInTerm, ih (c := c) (k := k + 1) (σ := shiftTyUp 1 0 σ)]
  | tapp M τ ih =>
    simp [shiftTermUp, substTypeInTerm, ih]

theorem substTypeInTerm_succ_shiftTypeInTerm_comm (c k : Nat) (σ : Ty) (hc : c ≤ k) :
    ∀ M : Term,
      substTypeInTerm (k + 1) (shiftTyUp 1 c σ) (shiftTypeInTerm 1 c M) =
        shiftTypeInTerm 1 c (substTypeInTerm k σ M) := by
  intro M
  induction M generalizing c k σ with
  | var n =>
    simp [substTypeInTerm, shiftTypeInTerm]
  | lam τ M ih =>
    have hτ := Ty.substTy_succ_shiftTyUp_comm (c := c) (k := k) (σ := σ) hc τ
    simp [substTypeInTerm, shiftTypeInTerm, hτ, ih (c := c) (k := k) (σ := σ) (hc := hc)]
  | app M N ihM ihN =>
    simp [substTypeInTerm, shiftTypeInTerm, ihM (hc := hc), ihN (hc := hc)]
  | tlam M ih =>
    have hc' : c + 1 ≤ k + 1 := Nat.succ_le_succ hc
    have hσ :
        shiftTyUp 1 0 (shiftTyUp 1 c σ) = shiftTyUp 1 (c + 1) (shiftTyUp 1 0 σ) := by
      simpa using (Eq.symm (Ty.shiftTyUp_comm_succ (d := 1) (b := 0) (c := c) (Nat.zero_le c) σ))
    simp [substTypeInTerm, shiftTypeInTerm, hσ,
      ih (c := c + 1) (k := k + 1) (σ := shiftTyUp 1 0 σ) (hc := hc')]
  | tapp M τ ih =>
    have hτ := Ty.substTy_succ_shiftTyUp_comm (c := c) (k := k) (σ := σ) hc τ
    simp [substTypeInTerm, shiftTypeInTerm, hτ, ih (c := c) (k := k) (σ := σ) (hc := hc)]

theorem substTypeInTerm_substTerm (k : Nat) (σ : Ty) :
    ∀ (j : Nat) (N M : Term),
      substTypeInTerm k σ (substTerm j N M) =
        substTerm j (substTypeInTerm k σ N) (substTypeInTerm k σ M) := by
  intro j N M
  induction M generalizing j N k σ with
  | var n =>
    simp [substTerm, substTypeInTerm]
    by_cases hnj : n < j
    · simp [substTypeInTerm, hnj]
    · by_cases hEq : n = j
      · simp [hEq]
      · simp [substTypeInTerm, hnj, hEq]
  | lam τ M ih =>
    simp [substTerm, substTypeInTerm]
    have hN :
        substTypeInTerm k σ (shiftTermUp 1 0 N) =
          shiftTermUp 1 0 (substTypeInTerm k σ N) :=
      substTypeInTerm_shiftTermUp_comm (k := k) (σ := σ) (d := 1) (c := 0) N
    have h := ih (j := j + 1) (N := shiftTermUp 1 0 N) (k := k) (σ := σ)
    simpa [hN] using h
  | app M₁ M₂ ih₁ ih₂ =>
    simp [substTerm, substTypeInTerm, ih₁ (j := j) (N := N), ih₂ (j := j) (N := N)]
  | tlam M ih =>
    simp [substTerm, substTypeInTerm]
    have hc : (0 : Nat) ≤ k := Nat.zero_le k
    have hN :
        substTypeInTerm (k + 1) (shiftTyUp 1 0 σ) (shiftTypeInTerm 1 0 N) =
          shiftTypeInTerm 1 0 (substTypeInTerm k σ N) := by
      simpa using
        substTypeInTerm_succ_shiftTypeInTerm_comm (c := 0) (k := k) (σ := σ) hc N
    have h := ih (j := j) (N := shiftTypeInTerm 1 0 N) (k := k + 1) (σ := shiftTyUp 1 0 σ)
    simpa [hN] using h
  | tapp M τ ih =>
    simp [substTerm, substTypeInTerm, ih (j := j) (N := N)]

theorem substTypeInTerm_substTypeInTerm (j k : Nat) (hj : j ≤ k) (σ τ : Ty) :
    ∀ M : Term,
      substTypeInTerm k σ (substTypeInTerm j τ M) =
        substTypeInTerm j (substTy k σ τ) (substTypeInTerm (k + 1) (shiftTyUp 1 j σ) M) := by
  intro M
  induction M generalizing j k σ τ with
  | var n =>
    simp [substTypeInTerm]
  | lam A M ih =>
    have hA := Ty.substTy_substTy (j := j) (k := k) hj (σ := σ) (τ := τ) A
    simp [substTypeInTerm, hA, ih (hj := hj)]
  | app M N ihM ihN =>
    simp [substTypeInTerm, ihM (hj := hj), ihN (hj := hj)]
  | tlam M ih =>
    have hj' : j + 1 ≤ k + 1 := Nat.succ_le_succ hj
    have hσ :
        shiftTyUp 1 (j + 1) (shiftTyUp 1 0 σ) = shiftTyUp 1 0 (shiftTyUp 1 j σ) := by
      simpa using (shiftTyUp_comm_succ (d := 1) (b := 0) (c := j) (Nat.zero_le j) σ)
    have hτ :
        substTy (k + 1) (shiftTyUp 1 0 σ) (shiftTyUp 1 0 τ) = shiftTyUp 1 0 (substTy k σ τ) :=
      substTy_succ_shiftTyUp_comm (c := 0) (k := k) (σ := σ) (Nat.zero_le k) τ
    simp [substTypeInTerm, hσ, hτ,
      ih (j := j + 1) (k := k + 1) (hj := hj') (σ := shiftTyUp 1 0 σ) (τ := shiftTyUp 1 0 τ)]
  | tapp M A ih =>
    have hA := Ty.substTy_substTy (j := j) (k := k) hj (σ := σ) (τ := τ) A
    simp [substTypeInTerm, hA, ih (hj := hj)]

theorem substTypeInTerm_substTypeInTerm0 (k : Nat) (σ τ : Ty) :
    ∀ M : Term,
      substTypeInTerm k σ (substTypeInTerm0 τ M) =
        substTypeInTerm0 (substTy k σ τ) (substTypeInTerm (k + 1) (shiftTyUp 1 0 σ) M) := by
  intro M
  simpa [substTypeInTerm0] using
    substTypeInTerm_substTypeInTerm (j := 0) (k := k) (hj := Nat.zero_le k) (σ := σ) (τ := τ) M

/-! ## Term Substitution Infrastructure -/

theorem shiftTermUp_comm_succ (d : Nat) {b c : Nat} (hb : b ≤ c) :
    ∀ M : Term, shiftTermUp d (c + 1) (shiftTermUp 1 b M) =
      shiftTermUp 1 b (shiftTermUp d c M) := by
  intro M
  induction M generalizing b c with
  | var n =>
    by_cases hnb : n < b
    · have hnc : n < c := Nat.lt_of_lt_of_le hnb hb
      have hncs : n < c + 1 := Nat.lt_trans hnc (Nat.lt_succ_self c)
      simp [shiftTermUp, hnb, hnc, hncs]
    · have hnb_ge : b ≤ n := Nat.le_of_not_gt hnb
      by_cases hnc : n < c
      · have hncs : n + 1 < c + 1 := Nat.succ_lt_succ hnc
        simp [shiftTermUp, hnb, hnc, hncs]
      · have hncs : ¬n + 1 < c + 1 := by
          exact Nat.not_lt.mpr (Nat.succ_le_succ (Nat.le_of_not_gt hnc))
        have hndb : ¬d + n < b :=
          Nat.not_lt.mpr (Nat.le_trans hnb_ge (Nat.le_add_left n d))
        simp [shiftTermUp, hnb, hnc, hncs, hndb, Nat.add_assoc, Nat.add_comm]
  | lam τ M ih =>
    have hb' : b + 1 ≤ c + 1 := Nat.succ_le_succ hb
    simpa [shiftTermUp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (b := b + 1) (c := c + 1) hb'
  | app M N ihM ihN =>
    simp [shiftTermUp, ihM (hb := hb), ihN (hb := hb)]
  | tlam M ih =>
    simp [shiftTermUp, ih (hb := hb)]
  | tapp M τ ih =>
    simp [shiftTermUp, ih (hb := hb)]

theorem shiftTermUp_substTerm_comm_gen (d c k : Nat) (hc : c ≤ k) (P M : Term) :
    shiftTermUp d c (substTerm k P M) =
      substTerm (k + d) (shiftTermUp d c P) (shiftTermUp d c M) := by
  induction M generalizing c k P with
  | var n =>
    by_cases hnc : n < c
    · have hnk : n < k := Nat.lt_of_lt_of_le hnc hc
      have hnkd : n < k + d := Nat.lt_of_lt_of_le hnk (Nat.le_add_right k d)
      simp only [substTerm, hnk, ↓reduceIte, shiftTermUp, hnc, hnkd]
    · have hgec : c ≤ n := Nat.le_of_not_lt hnc
      by_cases hnk : n < k
      · have hnd : n + d < k + d := Nat.add_lt_add_right hnk d
        simp only [substTerm, hnk, ↓reduceIte, shiftTermUp, hnc, hnd]
      · by_cases hEq : n = k
        · -- n = k case: LHS reduces to P, RHS to substituting into shifted var
          rw [hEq]
          have hnc' : ¬k < c := Nat.not_lt_of_le hc
          simp only [substTerm, Nat.lt_irrefl, ↓reduceIte, shiftTermUp, hnc']
        · have hgt : k < n := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hnk) (Ne.symm hEq)
          have hnc' : ¬ n - 1 < c := by omega
          have hnkd : ¬ n + d < k + d := by omega
          have hneq : n + d ≠ k + d := by omega
          have hpred : n - 1 + d = n + d - 1 := by omega
          simp only [substTerm, hnk, hEq, ↓reduceIte, shiftTermUp, hnc, hnkd, hneq, hnc', hpred]
  | lam τ M ih =>
    have hc' : c + 1 ≤ k + 1 := Nat.succ_le_succ hc
    simp only [substTerm, shiftTermUp]
    have hP : shiftTermUp d (c + 1) (shiftTermUp 1 0 P) = shiftTermUp 1 0 (shiftTermUp d c P) := by
      exact shiftTermUp_comm_succ (d := d) (b := 0) (c := c) (Nat.zero_le c) P
    have hkd : k + d + 1 = k + 1 + d := by omega
    rw [ih (c := c + 1) (k := k + 1) (P := shiftTermUp 1 0 P) hc', hP, hkd]
  | app M N ihM ihN =>
    simp only [shiftTermUp, substTerm, ihM (hc := hc), ihN (hc := hc)]
  | tlam M ih =>
    simp only [substTerm, shiftTermUp]
    have hComm : shiftTypeInTerm 1 0 (shiftTermUp d c P) = shiftTermUp d c (shiftTypeInTerm 1 0 P) := by
      exact shiftTypeInTerm_shiftTermUp_comm (d := 1) (c := 0) (d' := d) (c' := c) P
    rw [ih (hc := hc), hComm]
  | tapp M τ ih =>
    simp only [shiftTermUp, substTerm, ih (hc := hc)]

theorem shiftTermUp_substTerm_comm (c k : Nat) (hc : c ≤ k) :
    ∀ (P : Term) (M : Term),
      shiftTermUp 1 c (substTerm k P M) =
        substTerm (k + 1) (shiftTermUp 1 c P) (shiftTermUp 1 c M) :=
  shiftTermUp_substTerm_comm_gen 1 c k hc

/-- Generalized identity: substTerm (d + c) P (shiftTermUp d c M) = substTerm c P (shiftTermUp d (c+1) M).
    At c = 0, this gives substTerm d P (shiftTermUp d 0 M) = substTerm 0 P (shiftTermUp d 1 M). -/
theorem substTerm_shiftTermUp_dist_gen (d c : Nat) (P M : Term) :
    substTerm (d + c) P (shiftTermUp d c M) = substTerm c P (shiftTermUp d (c + 1) M) := by
  induction M generalizing d c P with
  | var n =>
    by_cases hnc : n < c
    · -- n < c: both sides are var n (n is not shifted, and n < c < d + c)
      have hnc1 : n < c + 1 := Nat.lt_trans hnc (Nat.lt_succ_self c)
      have hn_lt_dc : n < d + c := by omega
      have hn_neq_dc : n ≠ d + c := Nat.ne_of_lt hn_lt_dc
      have hn_neq_c : n ≠ c := Nat.ne_of_lt hnc
      simp only [shiftTermUp, hnc, hnc1, ↓reduceIte, substTerm, hn_lt_dc]
    · have hn_ge_c : c ≤ n := Nat.le_of_not_lt hnc
      by_cases hnc1 : n < c + 1
      · -- n = c: both sides substitute P
        have hn_eq_c : n = c := Nat.le_antisymm (Nat.lt_succ_iff.mp hnc1) hn_ge_c
        -- Explicitly compute both sides
        -- LHS: substTerm (d + c) P (shiftTermUp d c (var n))
        --    = substTerm (d + c) P (var (n + d))  [since n = c, so n ≥ c]
        --    = P  [since n + d = c + d = d + c]
        -- RHS: substTerm c P (shiftTermUp d (c + 1) (var n))
        --    = substTerm c P (var n)  [since n = c < c + 1]
        --    = P  [since n = c]
        rw [hn_eq_c]
        simp only [shiftTermUp, Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self, substTerm,
                   Nat.add_comm c d]
      · -- n > c: n gets shifted to n + d, and both sides give var (n + d - 1)
        have hn_gt_c : c < n := Nat.lt_of_succ_le (Nat.le_of_not_lt hnc1)
        have hnd_nlt_dc : ¬ n + d < d + c := by omega
        have hnd_neq_dc : n + d ≠ d + c := by omega
        have hnd_nlt_c : ¬ n + d < c := by omega
        have hnd_neq_c : n + d ≠ c := by omega
        have hpred : n + d - 1 = n - 1 + d := by omega
        simp only [shiftTermUp, hnc, hnc1, ↓reduceIte, substTerm, hnd_nlt_dc, hnd_neq_dc, hnd_nlt_c, hnd_neq_c, hpred]
  | lam τ M ih =>
    simp only [shiftTermUp, substTerm]
    have h1 : d + c + 1 = d + (c + 1) := by omega
    rw [h1]
    congr 1
    exact ih d (c + 1) (shiftTermUp 1 0 P)
  | app M N ihM ihN =>
    simp only [shiftTermUp, substTerm, ihM d c P, ihN d c P]
  | tlam M ih =>
    simp only [shiftTermUp, substTerm]
    congr 1
    exact ih d c (shiftTypeInTerm 1 0 P)
  | tapp M τ ih =>
    simp only [shiftTermUp, substTerm, ih d c P]

/-- For any term M, substTerm d P (shiftTermUp d 0 M) equals substTerm 0 P (shiftTermUp d 1 M). -/
theorem substTerm_shiftTermUp_dist (d : Nat) (P M : Term) :
    substTerm d P (shiftTermUp d 0 M) = substTerm 0 P (shiftTermUp d 1 M) := by
  have h := substTerm_shiftTermUp_dist_gen d 0 P M
  simp only [Nat.add_zero, Nat.zero_add] at h
  exact h

theorem shiftTermUp_substTerm_comm_lt (d c k : Nat) (hk : k < c) (P M : Term) :
    shiftTermUp d c (substTerm k P M) =
      substTerm k (shiftTermUp d c P) (shiftTermUp d (c + 1) M) := by
  induction M generalizing c k P with
  | var n =>
    -- Split based on whether n < k, n = k, k < n < c, n = c, or n > c
    by_cases hnk : n < k
    · -- Case 1: n < k < c, so n < c < c + 1
      have hnc : n < c := Nat.lt_trans hnk hk
      have hnc1 : n < c + 1 := Nat.lt_trans hnc (Nat.lt_succ_self c)
      simp only [substTerm, hnk, ↓reduceIte, shiftTermUp, hnc, hnc1]
    · by_cases hEq : n = k
      · -- Case 2: n = k < c, so n < c + 1
        subst hEq
        have hnc : n < c := hk
        have hnc1 : n < c + 1 := Nat.lt_trans hnc (Nat.lt_succ_self c)
        simp only [substTerm, Nat.lt_irrefl, ↓reduceIte, shiftTermUp, hnc1]
      · -- k < n (since ¬ n < k and n ≠ k)
        have hkn : k < n := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hnk) (Ne.symm hEq)
        have hn_pos : 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le k) hkn)
        by_cases hnc : n < c
        · -- Case 3: k < n < c, so n - 1 < c and n < c + 1
          have hnc1 : n < c + 1 := Nat.lt_trans hnc (Nat.lt_succ_self c)
          have hn1c : n - 1 < c := Nat.lt_of_lt_of_le (Nat.sub_lt hn_pos Nat.one_pos) (Nat.le_of_lt hnc)
          simp only [substTerm, hnk, hEq, ↓reduceIte, shiftTermUp, hn1c, hnc1]
        · -- n ≥ c, but we split on n = c or n > c
          by_cases hnc_eq : n = c
          · -- Case 4: n = c > k, so n - 1 = c - 1 < c
            -- Since k < n = c and 0 ≤ k, we have 0 < c, so c ≥ 1
            have hc_pos : 0 < c := by
              rw [← hnc_eq]; exact Nat.lt_of_le_of_lt (Nat.zero_le k) hkn
            have hn1c : n - 1 < c := by rw [hnc_eq]; exact Nat.sub_lt hc_pos Nat.one_pos
            have hnc1 : n < c + 1 := by rw [hnc_eq]; exact Nat.lt_succ_self c
            simp only [substTerm, hnk, hEq, ↓reduceIte, shiftTermUp, hn1c, hnc1]
          · -- Case 5: n > c > k
            have hcn : c < n := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hnc) (Ne.symm hnc_eq)
            have hnc1 : ¬ n < c + 1 := Nat.not_lt.mpr (Nat.succ_le_of_lt hcn)
            have hn1c : ¬ n - 1 < c := Nat.not_lt.mpr (Nat.le_sub_of_add_le (Nat.succ_le_of_lt hcn))
            have hndk : ¬ n + d < k := Nat.not_lt.mpr (Nat.le_trans (Nat.le_of_lt hk) (Nat.le_trans (Nat.le_of_lt hcn) (Nat.le_add_right n d)))
            have hndkeq : n + d ≠ k := Nat.ne_of_gt (Nat.lt_of_lt_of_le hk (Nat.le_trans (Nat.le_of_lt hcn) (Nat.le_add_right n d)))
            have hn1dk : ¬ n - 1 + d < k := Nat.not_lt.mpr (Nat.le_trans (Nat.le_of_lt hk) (Nat.le_trans (Nat.le_sub_of_add_le (Nat.succ_le_of_lt hcn)) (Nat.le_add_right (n - 1) d)))
            have hn1dkeq : n - 1 + d ≠ k := Nat.ne_of_gt (Nat.lt_of_lt_of_le hk (Nat.le_trans (Nat.le_sub_of_add_le (Nat.succ_le_of_lt hcn)) (Nat.le_add_right (n - 1) d)))
            have hpred : n + d - 1 = n - 1 + d := Nat.sub_add_comm hn_pos
            simp only [substTerm, hnk, hEq, ↓reduceIte, shiftTermUp, hnc1, hn1c, hndk, hndkeq, hpred]
  | lam τ M ih =>
    simp only [shiftTermUp, substTerm]
    have hc' : k + 1 < c + 1 := Nat.succ_lt_succ hk
    -- Use IH: shiftTermUp d (c+1) (substTerm (k+1) Q M) = substTerm (k+1) (shiftTermUp d (c+1) Q) (shiftTermUp d (c+2) M)
    have h1 := ih (c := c + 1) (k := k + 1) (P := shiftTermUp 1 0 P) hc'
    -- Need: shiftTermUp 1 0 (shiftTermUp d c P) = shiftTermUp d (c + 1) (shiftTermUp 1 0 P)
    have hP : shiftTermUp 1 0 (shiftTermUp d c P) = shiftTermUp d (c + 1) (shiftTermUp 1 0 P) := by
      have hcomm := shiftTermUp_comm_succ (d := d) (b := 0) (c := c) (Nat.zero_le c) P
      simp only [] at hcomm
      exact hcomm.symm
    simp only [Nat.add_assoc] at h1
    rw [h1, ← hP]
  | app M N ihM ihN =>
    simp only [shiftTermUp, substTerm, ihM (hk := hk), ihN (hk := hk)]
  | tlam M ih =>
    simp only [shiftTermUp, substTerm]
    -- IH: shiftTermUp d c (substTerm k Q M) = substTerm k (shiftTermUp d c Q) (shiftTermUp d (c + 1) M)
    -- With Q = shiftTypeInTerm 1 0 P, need to show:
    -- tlam (shiftTermUp d c (substTerm k (shiftTypeInTerm 1 0 P) M))
    --   = tlam (substTerm k (shiftTypeInTerm 1 0 (shiftTermUp d c P)) (shiftTermUp d (c + 1) M))
    -- Use IH to get LHS = tlam (substTerm k (shiftTermUp d c (shiftTypeInTerm 1 0 P)) (shiftTermUp d (c + 1) M))
    -- Then need: shiftTypeInTerm 1 0 (shiftTermUp d c P) = shiftTermUp d c (shiftTypeInTerm 1 0 P)
    have hcomm : shiftTypeInTerm 1 0 (shiftTermUp d c P) = shiftTermUp d c (shiftTypeInTerm 1 0 P) := by
      exact shiftTypeInTerm_shiftTermUp_comm (d := 1) (c := 0) (d' := d) (c' := c) P
    rw [ih (hk := hk), hcomm]
  | tapp M τ ih =>
    simp only [shiftTermUp, substTerm, ih (hk := hk)]

theorem shiftTermUp_substTerm0 (d c : Nat) (P M : Term) :
    shiftTermUp d c (substTerm0 P M) =
      substTerm0 (shiftTermUp d c P) (shiftTermUp d (c + 1) M) := by
  unfold substTerm0
  by_cases hc : c = 0
  · subst hc
    rw [shiftTermUp_substTerm_comm_gen d 0 0 (Nat.le_refl 0) P M]
    simp only [Nat.zero_add]
    rw [substTerm_shiftTermUp_dist]
  · have hk : 0 < c := Nat.pos_of_ne_zero hc
    exact shiftTermUp_substTerm_comm_lt d c 0 hk P M

theorem substTypeInTerm_shiftTypeInTerm_cancel (k : Nat) (σ : Ty) :
    ∀ M : Term, substTypeInTerm k σ (shiftTypeInTerm 1 k M) = M := by
  intro M
  induction M generalizing k σ with
  | var n =>
    simp [substTypeInTerm, shiftTypeInTerm]
  | lam τ M ih =>
    have hτ : substTy k σ (shiftTyUp 1 k τ) = τ := Ty.substTy_shiftTyUp_cancel (k := k) (σ := σ) τ
    simp [substTypeInTerm, shiftTypeInTerm, hτ, ih (k := k) (σ := σ)]
  | app M N ihM ihN =>
    simp [substTypeInTerm, shiftTypeInTerm, ihM (k := k) (σ := σ), ihN (k := k) (σ := σ)]
  | tlam M ih =>
    simp [substTypeInTerm, shiftTypeInTerm, ih (k := k + 1) (σ := shiftTyUp 1 0 σ)]
  | tapp M τ ih =>
    have hτ : substTy k σ (shiftTyUp 1 k τ) = τ := Ty.substTy_shiftTyUp_cancel (k := k) (σ := σ) τ
    simp [substTypeInTerm, shiftTypeInTerm, hτ, ih (k := k) (σ := σ)]

theorem substTypeInTerm0_tapp_shiftTypeInTerm_cancel (σ : Ty) (M : Term) :
    substTypeInTerm0 σ (tapp (shiftTypeInTerm 1 0 M) (tvar 0)) = tapp M σ := by
  -- Cancel the shift in the function part and substitute the fresh variable in the argument.
  simp [substTypeInTerm0, substTypeInTerm, substTypeInTerm_shiftTypeInTerm_cancel, Ty.substTy]

theorem substTerm_shiftTermUp_cancel (k : Nat) (N : Term) :
    ∀ M : Term, substTerm k N (shiftTermUp 1 k M) = M := by
  intro M
  induction M generalizing k N with
  | var n =>
    simp [shiftTermUp]
    by_cases hnk : n < k
    · simp [substTerm, hnk]
    · have hnk' : ¬n + 1 < k := by
        have : k ≤ n := Nat.le_of_not_gt hnk
        omega
      have hne : ¬n + 1 = k := by
        have : k ≤ n := Nat.le_of_not_gt hnk
        omega
      simp [substTerm, hnk, hnk', hne]
  | lam τ M ih =>
    simp [shiftTermUp, substTerm, ih (k := k + 1) (N := shiftTermUp 1 0 N)]
  | app M₁ M₂ ih₁ ih₂ =>
    simp [shiftTermUp, substTerm, ih₁ (k := k) (N := N), ih₂ (k := k) (N := N)]
  | tlam M ih =>
    simp [shiftTermUp, substTerm, ih (k := k) (N := shiftTypeInTerm 1 0 N)]
  | tapp M τ ih =>
    simp [shiftTermUp, substTerm, ih (k := k) (N := N)]

/-- Term substitution composition (in the `j ≤ k` case). -/
theorem substTerm_substTerm (j k : Nat) (hj : j ≤ k) (P N : Term) :
    ∀ M : Term,
      substTerm k P (substTerm j N M) =
        substTerm j (substTerm k P N) (substTerm (k + 1) (shiftTermUp 1 j P) M) := by
  intro M
  induction M generalizing j k P N with
  | var n =>
    by_cases hnj : n < j
    · have hnk : n < k := Nat.lt_of_lt_of_le hnj hj
      have hnk' : n < k + 1 := Nat.lt_trans hnk (Nat.lt_succ_self k)
      simp [substTerm, hnj, hnk, hnk']
    · by_cases hEqj : n = j
      · have hjk1 : j < k + 1 := Nat.lt_of_le_of_lt hj (Nat.lt_succ_self k)
        simp [substTerm, hEqj, hjk1]
      · have hgtj : j < n := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnj) (Ne.symm hEqj)
        by_cases hnk1 : n < k + 1
        · -- then n ≤ k
          have hnle : n ≤ k := Nat.lt_succ_iff.mp hnk1
          have hn1lt : n - 1 < k := by
            cases n with
            | zero =>
              have : False := by
                have : (0 : Nat) < 0 := Nat.lt_of_le_of_lt (Nat.zero_le j) hgtj
                exact Nat.lt_irrefl 0 this
              exact False.elim this
            | succ n' =>
              have hnle' : n' + 1 ≤ k := by simpa using hnle
              have : n' < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self n') hnle'
              simpa using this
          simp [substTerm, hnj, hEqj, hnk1, hn1lt]
        · by_cases hEqk1 : n = k + 1
          · subst hEqk1
            have hk1j : ¬k + 1 < j := by omega
            have hk1eq : k + 1 ≠ j := by omega
            simp [substTerm, hk1j, hk1eq,
              substTerm_shiftTermUp_cancel (k := j) (N := substTerm k P N) (M := P)]
          · have hgt : k + 1 < n := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnk1) (Ne.symm hEqk1)
            have hn1gt : k < n - 1 := by omega
            have hn1ltk : ¬n - 1 < k := by omega
            have hn1eqk : n - 1 ≠ k := by omega
            have hnj' : ¬n - 1 < j := by omega
            have hneq' : n - 1 ≠ j := by omega
            simp [substTerm, hnj, hEqj, hnk1, hEqk1, hn1ltk, hn1eqk, hnj', hneq']
  | lam τ M ih =>
    have hj' : j + 1 ≤ k + 1 := Nat.succ_le_succ hj
    have hN :
        shiftTermUp 1 0 (substTerm k P N) =
          substTerm (k + 1) (shiftTermUp 1 0 P) (shiftTermUp 1 0 N) := by
      -- commuting term shift with substitution at a lower cutoff
      simpa using (shiftTermUp_substTerm_comm (c := 0) (k := k) (P := P) (M := N) (Nat.zero_le k))
    have hP :
        shiftTermUp 1 (j + 1) (shiftTermUp 1 0 P) =
          shiftTermUp 1 0 (shiftTermUp 1 j P) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (shiftTermUp_comm_succ (d := 1) (b := 0) (c := j) (Nat.zero_le j) P)
    simp [substTerm, ih (j := j + 1) (k := k + 1) (P := shiftTermUp 1 0 P) (N := shiftTermUp 1 0 N) hj',
      hN, hP]
  | app M N ihM ihN =>
    simp [substTerm, ihM (hj := hj), ihN (hj := hj)]
  | tlam M ih =>
    -- Under a type binder, both substituted terms get their type variables shifted.
    have hShiftP : shiftTypeInTerm 1 0 (shiftTermUp 1 j P) = shiftTermUp 1 j (shiftTypeInTerm 1 0 P) := by
      simpa using (shiftTypeInTerm_shiftTermUp_comm (d := 1) (c := 0) (d' := 1) (c' := j) P)
    have hShiftN :
        substTerm k (shiftTypeInTerm 1 0 P) (shiftTypeInTerm 1 0 N) = shiftTypeInTerm 1 0 (substTerm k P N) := by
      simpa using (shiftTypeInTerm_substTerm (d := 1) (c := 0) (k := k) (N := P) (M := N)).symm
    simp [substTerm, ih (hj := hj) (P := shiftTypeInTerm 1 0 P) (N := shiftTypeInTerm 1 0 N), hShiftP, hShiftN]
  | tapp M τ ih =>
    simp [substTerm, ih (hj := hj)]

/-! ## Term substitution preserves full reduction -/

theorem substTerm_preserves_step (k : Nat) (P : Term) :
    ∀ {M N : Term}, (M ⟶ₛ N) → substTerm k P M ⟶ₛ substTerm k P N := by
  intro M N h
  induction h generalizing k P with
  | beta τ M N =>
    simp [substTerm, substTerm_substTerm (j := 0) (k := k) (hj := Nat.zero_le k)]
    exact StrongStep.beta _ _ _
  | tbeta Mbody τ =>
    have hCancel : substTypeInTerm0 τ (shiftTypeInTerm 1 0 P) = P := by
      simpa [substTypeInTerm0] using (substTypeInTerm_shiftTypeInTerm_cancel (k := 0) (σ := τ) P)
    have hComm :
        substTypeInTerm0 τ (substTerm k (shiftTypeInTerm 1 0 P) Mbody) =
          substTerm k P (substTypeInTerm0 τ Mbody) := by
      simp [substTypeInTerm_substTerm (k := 0) (σ := τ), hCancel]
    have hStep :
        tapp (tlam (substTerm k (shiftTypeInTerm 1 0 P) Mbody)) τ ⟶ₛ
          substTypeInTerm0 τ (substTerm k (shiftTypeInTerm 1 0 P) Mbody) :=
      StrongStep.tbeta (M := substTerm k (shiftTypeInTerm 1 0 P) Mbody) (τ := τ)
    simpa [substTerm, hComm] using hStep
  | lam h ih =>
    simp [substTerm]
    exact StrongStep.lam (ih (k := k + 1) (P := shiftTermUp 1 0 P))
  | appL h ih =>
    simp [substTerm]
    exact StrongStep.appL (ih (k := k) (P := P))
  | appR h ih =>
    simp [substTerm]
    exact StrongStep.appR (ih (k := k) (P := P))
  | tlam h ih =>
    simp [substTerm]
    exact StrongStep.tlam (ih (k := k) (P := shiftTypeInTerm 1 0 P))
  | tappL h ih =>
    simp [substTerm]
    exact StrongStep.tappL (ih (k := k) (P := P))

theorem sn_of_substTerm (k : Nat) (N : Term) {M : Term} (h : SN (substTerm k N M)) : SN M := by
  have : ∀ T, SN T → ∀ M, T = substTerm k N M → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M hEq
      subst hEq
      apply sn_intro
      intro M' hstep
      have hstep' : substTerm k N M ⟶ₛ substTerm k N M' :=
        substTerm_preserves_step (k := k) (P := N) hstep
      exact ih (substTerm k N M') hstep' M' rfl
  exact this (substTerm k N M) h M rfl

/-! ## Type substitution preserves full reduction -/

theorem substTypeInTerm_preserves_step (k : Nat) (σ : Ty) :
    ∀ {M N : Term}, (M ⟶ₛ N) → substTypeInTerm k σ M ⟶ₛ substTypeInTerm k σ N := by
  intro M N h
  induction h generalizing k σ with
  | beta τ M N =>
    simp [substTypeInTerm, substTypeInTerm_substTerm (k := k) (σ := σ) (j := 0)]
    exact StrongStep.beta _ _ _
  | tbeta M τ =>
    simp [substTypeInTerm, substTypeInTerm_substTypeInTerm0 (k := k) (σ := σ) (τ := τ)]
    exact StrongStep.tbeta _ _
  | lam h ih =>
    simp [substTypeInTerm]
    exact StrongStep.lam (ih (k := k) (σ := σ))
  | appL h ih =>
    simp [substTypeInTerm]
    exact StrongStep.appL (ih (k := k) (σ := σ))
  | appR h ih =>
    simp [substTypeInTerm]
    exact StrongStep.appR (ih (k := k) (σ := σ))
  | tlam h ih =>
    simp [substTypeInTerm]
    exact StrongStep.tlam (ih (k := k + 1) (σ := shiftTyUp 1 0 σ))
  | tappL h ih =>
    simp [substTypeInTerm]
    exact StrongStep.tappL (ih (k := k) (σ := σ))

/-! ## Shifting preserves full reduction -/

theorem shiftTypeInTerm_preserves_step (d c : Nat) :
    ∀ {M N : Term}, (M ⟶ₛ N) → shiftTypeInTerm d c M ⟶ₛ shiftTypeInTerm d c N := by
  intro M N h
  induction h generalizing c with
  | beta τ M N =>
    simp [shiftTypeInTerm, shiftTypeInTerm_substTerm0]
    exact StrongStep.beta _ _ _
  | tbeta M τ =>
    simp [shiftTypeInTerm, shiftTypeInTerm_substTypeInTerm0]
    exact StrongStep.tbeta _ _
  | lam h ih =>
    simp [shiftTypeInTerm]
    exact StrongStep.lam (ih (c := c))
  | appL h ih =>
    simp [shiftTypeInTerm]
    exact StrongStep.appL (ih (c := c))
  | appR h ih =>
    simp [shiftTypeInTerm]
    exact StrongStep.appR (ih (c := c))
  | tlam h ih =>
    simp [shiftTypeInTerm]
    exact StrongStep.tlam (ih (c := c + 1))
  | tappL h ih =>
    simp [shiftTypeInTerm]
    exact StrongStep.tappL (ih (c := c))

/-- Term variable shifting preserves full reduction. -/
theorem shiftTermUp_preserves_step (d c : Nat) :
    ∀ {M N : Term}, (M ⟶ₛ N) → shiftTermUp d c M ⟶ₛ shiftTermUp d c N := by
  intro M N h
  induction h generalizing c with
  | beta τ M N =>
    simp [shiftTermUp, shiftTermUp_substTerm0]
    exact StrongStep.beta _ _ _
  | tbeta M τ =>
    -- Type substitution in terms commutes with term variable shifting
    simp only [shiftTermUp]
    have hComm : shiftTermUp d c (substTypeInTerm0 τ M) =
        substTypeInTerm0 τ (shiftTermUp d c M) := by
      simp only [substTypeInTerm0]
      exact (substTypeInTerm_shiftTermUp_comm 0 τ d c M).symm
    rw [hComm]
    exact StrongStep.tbeta _ _
  | lam h ih =>
    simp [shiftTermUp]
    exact StrongStep.lam (ih (c := c + 1))
  | appL h ih =>
    simp [shiftTermUp]
    exact StrongStep.appL (ih (c := c))
  | appR h ih =>
    simp [shiftTermUp]
    exact StrongStep.appR (ih (c := c))
  | tlam h ih =>
    simp [shiftTermUp]
    exact StrongStep.tlam (ih (c := c))
  | tappL h ih =>
    simp [shiftTermUp]
    exact StrongStep.tappL (ih (c := c))

/-- Any reduction step on a shifted term comes from a step on the original term. -/
theorem step_of_shiftTypeInTerm_step (d c : Nat) :
    ∀ {M N : Term}, (shiftTypeInTerm d c M ⟶ₛ N) → ∃ N', M ⟶ₛ N' ∧ N = shiftTypeInTerm d c N' := by
  intro M N h
  induction M generalizing c N with
  | var n =>
    cases h
  | lam τ M ih =>
    cases h with
    | lam hM =>
      rcases ih (c := c) (N := _) hM with ⟨N', hstep, rfl⟩
      refine ⟨lam τ N', StrongStep.lam hstep, ?_⟩
      simp [shiftTypeInTerm]
  | app M₁ M₂ ih₁ ih₂ =>
    cases M₁ with
    | lam τ M₁body =>
      cases h with
      | beta τ' M' N' =>
        refine ⟨substTerm0 M₂ M₁body, StrongStep.beta τ M₁body M₂, ?_⟩
        simp only [shiftTypeInTerm_substTerm0]
      | appL h1 =>
        rcases ih₁ (c := c) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨app N' M₂, StrongStep.appL hstep, ?_⟩
        simp [shiftTypeInTerm]
      | appR h2 =>
        rcases ih₂ (c := c) (N := _) h2 with ⟨N', hstep, rfl⟩
        refine ⟨app (lam τ M₁body) N', StrongStep.appR hstep, ?_⟩
        simp [shiftTypeInTerm]
    | var n =>
      cases h with
      | appL h1 =>
        rcases ih₁ (c := c) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨app N' M₂, StrongStep.appL hstep, ?_⟩
        simp [shiftTypeInTerm]
      | appR h2 =>
        rcases ih₂ (c := c) (N := _) h2 with ⟨N', hstep, rfl⟩
        refine ⟨app (var n) N', StrongStep.appR hstep, ?_⟩
        simp [shiftTypeInTerm]
    | app M₁₁ M₁₂ =>
      cases h with
      | appL h1 =>
        rcases ih₁ (c := c) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨app N' M₂, StrongStep.appL hstep, ?_⟩
        simp [shiftTypeInTerm]
      | appR h2 =>
        rcases ih₂ (c := c) (N := _) h2 with ⟨N', hstep, rfl⟩
        refine ⟨app (app M₁₁ M₁₂) N', StrongStep.appR hstep, ?_⟩
        simp [shiftTypeInTerm]
    | tlam M₁body =>
      cases h with
      | appL h1 =>
        rcases ih₁ (c := c) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨app N' M₂, StrongStep.appL hstep, ?_⟩
        simp [shiftTypeInTerm]
      | appR h2 =>
        rcases ih₂ (c := c) (N := _) h2 with ⟨N', hstep, rfl⟩
        refine ⟨app (tlam M₁body) N', StrongStep.appR hstep, ?_⟩
        simp [shiftTypeInTerm]
    | tapp M₁body τ =>
      cases h with
      | appL h1 =>
        rcases ih₁ (c := c) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨app N' M₂, StrongStep.appL hstep, ?_⟩
        simp [shiftTypeInTerm]
      | appR h2 =>
        rcases ih₂ (c := c) (N := _) h2 with ⟨N', hstep, rfl⟩
        refine ⟨app (tapp M₁body τ) N', StrongStep.appR hstep, ?_⟩
        simp [shiftTypeInTerm]
  | tlam M ih =>
    cases h with
    | tlam hM =>
      rcases ih (c := c + 1) (N := _) hM with ⟨N', hstep, rfl⟩
      refine ⟨tlam N', StrongStep.tlam hstep, ?_⟩
      simp [shiftTypeInTerm]
  | tapp M τ ih =>
    cases M with
    | tlam Mbody =>
      cases h with
      | tbeta M' τ' =>
        refine ⟨substTypeInTerm0 τ Mbody, StrongStep.tbeta Mbody τ, ?_⟩
        simp only [shiftTypeInTerm_substTypeInTerm0]
      | tappL h1 =>
        rcases ih (c := c) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨tapp N' τ, StrongStep.tappL hstep, ?_⟩
        simp [shiftTypeInTerm]
    | var n =>
      cases h with
      | tappL h1 =>
        cases h1
    | lam τ' Mbody =>
      cases h with
      | tappL h1 =>
        rcases ih (c := c) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨tapp N' τ, StrongStep.tappL hstep, ?_⟩
        simp [shiftTypeInTerm]
    | app M₁ M₂ =>
      cases h with
      | tappL h1 =>
        rcases ih (c := c) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨tapp N' τ, StrongStep.tappL hstep, ?_⟩
        simp [shiftTypeInTerm]
    | tapp Mbody τ' =>
      cases h with
      | tappL h1 =>
        rcases ih (c := c) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨tapp N' τ, StrongStep.tappL hstep, ?_⟩
        simp [shiftTypeInTerm]

/-- Any reduction step on a type-substituted term comes from a step on the original term. -/
theorem step_of_substTypeInTerm_step (k : Nat) (σ : Ty) :
    ∀ {M N : Term}, (substTypeInTerm k σ M ⟶ₛ N) → ∃ N', M ⟶ₛ N' ∧ N = substTypeInTerm k σ N' := by
  intro M N h
  induction M generalizing k σ N with
  | var n =>
    cases h
  | lam τ M ih =>
    cases h with
    | lam hM =>
      rcases ih (k := k) (σ := σ) (N := _) hM with ⟨N', hstep, rfl⟩
      refine ⟨lam τ N', StrongStep.lam hstep, ?_⟩
      simp [substTypeInTerm]
  | app M₁ M₂ ih₁ ih₂ =>
    cases M₁ with
    | lam τ M₁body =>
      cases h with
      | beta τ' M' N' =>
        refine ⟨substTerm0 M₂ M₁body, StrongStep.beta τ M₁body M₂, ?_⟩
        -- Align the substituted beta reduct.
        have hComm :
            substTypeInTerm k σ (substTerm0 M₂ M₁body) =
              substTerm0 (substTypeInTerm k σ M₂) (substTypeInTerm k σ M₁body) := by
          simpa [substTerm0] using
            (substTypeInTerm_substTerm (k := k) (σ := σ) (j := 0) (N := M₂) (M := M₁body))
        -- `N` is definitionally the RHS beta reduct.
        simp [hComm]
      | appL h1 =>
        rcases ih₁ (k := k) (σ := σ) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨app N' M₂, StrongStep.appL hstep, ?_⟩
        simp [substTypeInTerm]
      | appR h2 =>
        rcases ih₂ (k := k) (σ := σ) (N := _) h2 with ⟨N', hstep, rfl⟩
        refine ⟨app (lam τ M₁body) N', StrongStep.appR hstep, ?_⟩
        simp [substTypeInTerm]
    | var n =>
      cases h with
      | appL h1 =>
        rcases ih₁ (k := k) (σ := σ) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨app N' M₂, StrongStep.appL hstep, ?_⟩
        simp [substTypeInTerm]
      | appR h2 =>
        rcases ih₂ (k := k) (σ := σ) (N := _) h2 with ⟨N', hstep, rfl⟩
        refine ⟨app (var n) N', StrongStep.appR hstep, ?_⟩
        simp [substTypeInTerm]
    | app M₁₁ M₁₂ =>
      cases h with
      | appL h1 =>
        rcases ih₁ (k := k) (σ := σ) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨app N' M₂, StrongStep.appL hstep, ?_⟩
        simp [substTypeInTerm]
      | appR h2 =>
        rcases ih₂ (k := k) (σ := σ) (N := _) h2 with ⟨N', hstep, rfl⟩
        refine ⟨app (app M₁₁ M₁₂) N', StrongStep.appR hstep, ?_⟩
        simp [substTypeInTerm]
    | tlam M₁body =>
      cases h with
      | appL h1 =>
        rcases ih₁ (k := k) (σ := σ) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨app N' M₂, StrongStep.appL hstep, ?_⟩
        simp [substTypeInTerm]
      | appR h2 =>
        rcases ih₂ (k := k) (σ := σ) (N := _) h2 with ⟨N', hstep, rfl⟩
        refine ⟨app (tlam M₁body) N', StrongStep.appR hstep, ?_⟩
        simp [substTypeInTerm]
    | tapp M₁body τ =>
      cases h with
      | appL h1 =>
        rcases ih₁ (k := k) (σ := σ) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨app N' M₂, StrongStep.appL hstep, ?_⟩
        simp [substTypeInTerm]
      | appR h2 =>
        rcases ih₂ (k := k) (σ := σ) (N := _) h2 with ⟨N', hstep, rfl⟩
        refine ⟨app (tapp M₁body τ) N', StrongStep.appR hstep, ?_⟩
        simp [substTypeInTerm]
  | tlam M ih =>
    cases h with
    | tlam hM =>
      rcases ih (k := k + 1) (σ := shiftTyUp 1 0 σ) (N := _) hM with ⟨N', hstep, rfl⟩
      refine ⟨tlam N', StrongStep.tlam hstep, ?_⟩
      simp [substTypeInTerm]
  | tapp M τ ih =>
    cases M with
    | tlam Mbody =>
      cases h with
      | tbeta M' τ' =>
        refine ⟨substTypeInTerm0 τ Mbody, StrongStep.tbeta Mbody τ, ?_⟩
        have hComm :
            substTypeInTerm k σ (substTypeInTerm0 τ Mbody) =
              substTypeInTerm0 (substTy k σ τ) (substTypeInTerm (k + 1) (shiftTyUp 1 0 σ) Mbody) := by
          simpa using (substTypeInTerm_substTypeInTerm0 (k := k) (σ := σ) (τ := τ) Mbody)
        simp [hComm]
      | tappL h1 =>
        rcases ih (k := k) (σ := σ) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨tapp N' τ, StrongStep.tappL hstep, ?_⟩
        simp [substTypeInTerm]
    | var n =>
      cases h with
      | tappL h1 =>
        cases h1
    | lam τ' Mbody =>
      cases h with
      | tappL h1 =>
        rcases ih (k := k) (σ := σ) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨tapp N' τ, StrongStep.tappL hstep, ?_⟩
        simp [substTypeInTerm]
    | app M₁ M₂ =>
      cases h with
      | tappL h1 =>
        rcases ih (k := k) (σ := σ) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨tapp N' τ, StrongStep.tappL hstep, ?_⟩
        simp [substTypeInTerm]
    | tapp Mbody τ' =>
      cases h with
      | tappL h1 =>
        rcases ih (k := k) (σ := σ) (N := _) h1 with ⟨N', hstep, rfl⟩
        refine ⟨tapp N' τ, StrongStep.tappL hstep, ?_⟩
        simp [substTypeInTerm]
/-! ## `instFresh` and reduction -/

theorem instFresh_steps_of_step :
    ∀ {M N : Term}, (M ⟶ₛ N) → instFresh M ⟶ₛ* instFresh N := by
  intro M N hstep
  cases M with
  | tlam Mbody =>
    -- Only reduction under `tlam` is possible.
    cases hstep with
    | tlam hBody =>
      rename_i Nbody
      have hShift : shiftTypeInTerm 1 1 Mbody ⟶ₛ shiftTypeInTerm 1 1 Nbody :=
        shiftTypeInTerm_preserves_step (d := 1) (c := 1) hBody
      have hSubst :
          substTypeInTerm0 (tvar 0) (shiftTypeInTerm 1 1 Mbody) ⟶ₛ
            substTypeInTerm0 (tvar 0) (shiftTypeInTerm 1 1 Nbody) := by
        simpa [substTypeInTerm0] using
          substTypeInTerm_preserves_step (k := 0) (σ := tvar 0) hShift
      exact StrongMultiStep.single (by simpa [instFresh] using hSubst)
  | var n =>
    cases hstep
  | lam τ Mbody =>
    have hShift : shiftTypeInTerm 1 0 (lam τ Mbody) ⟶ₛ shiftTypeInTerm 1 0 N :=
      shiftTypeInTerm_preserves_step (d := 1) (c := 0) hstep
    have h1 : tapp (shiftTypeInTerm 1 0 (lam τ Mbody)) (tvar 0) ⟶ₛ
        tapp (shiftTypeInTerm 1 0 N) (tvar 0) :=
      StrongStep.tappL hShift
    cases N with
    | tlam Nbody =>
      have htb : tapp (shiftTypeInTerm 1 0 (tlam Nbody)) (tvar 0) ⟶ₛ instFresh (tlam Nbody) := by
        simp [instFresh, shiftTypeInTerm]
        exact StrongStep.tbeta _ _
      exact StrongMultiStep.step (by simpa [instFresh] using h1) (StrongMultiStep.single htb)
    | var n =>
      simpa [instFresh] using StrongMultiStep.single h1
    | lam τ' Nbody =>
      simpa [instFresh] using StrongMultiStep.single h1
    | app N1 N2 =>
      simpa [instFresh] using StrongMultiStep.single h1
    | tapp N1 τ' =>
      simpa [instFresh] using StrongMultiStep.single h1
  | app M1 M2 =>
    have hShift : shiftTypeInTerm 1 0 (app M1 M2) ⟶ₛ shiftTypeInTerm 1 0 N :=
      shiftTypeInTerm_preserves_step (d := 1) (c := 0) hstep
    have h1 : tapp (shiftTypeInTerm 1 0 (app M1 M2)) (tvar 0) ⟶ₛ
        tapp (shiftTypeInTerm 1 0 N) (tvar 0) :=
      StrongStep.tappL hShift
    cases N with
    | tlam Nbody =>
      have htb : tapp (shiftTypeInTerm 1 0 (tlam Nbody)) (tvar 0) ⟶ₛ instFresh (tlam Nbody) := by
        simp [instFresh, shiftTypeInTerm]
        exact StrongStep.tbeta _ _
      exact StrongMultiStep.step (by simpa [instFresh] using h1) (StrongMultiStep.single htb)
    | var n =>
      simpa [instFresh] using StrongMultiStep.single h1
    | lam τ' Nbody =>
      simpa [instFresh] using StrongMultiStep.single h1
    | app N1 N2 =>
      simpa [instFresh] using StrongMultiStep.single h1
    | tapp N1 τ' =>
      simpa [instFresh] using StrongMultiStep.single h1
  | tapp M τ =>
    have hShift : shiftTypeInTerm 1 0 (tapp M τ) ⟶ₛ shiftTypeInTerm 1 0 N :=
      shiftTypeInTerm_preserves_step (d := 1) (c := 0) hstep
    have h1 : tapp (shiftTypeInTerm 1 0 (tapp M τ)) (tvar 0) ⟶ₛ
        tapp (shiftTypeInTerm 1 0 N) (tvar 0) :=
      StrongStep.tappL hShift
    cases N with
    | tlam Nbody =>
      have htb : tapp (shiftTypeInTerm 1 0 (tlam Nbody)) (tvar 0) ⟶ₛ instFresh (tlam Nbody) := by
        simp [instFresh, shiftTypeInTerm]
        exact StrongStep.tbeta _ _
      exact StrongMultiStep.step (by simpa [instFresh] using h1) (StrongMultiStep.single htb)
    | var n =>
      simpa [instFresh] using StrongMultiStep.single h1
    | lam τ' Nbody =>
      simpa [instFresh] using StrongMultiStep.single h1
    | app N1 N2 =>
      simpa [instFresh] using StrongMultiStep.single h1
    | tapp N1 τ' =>
      simpa [instFresh] using StrongMultiStep.single h1

/-! ## Candidate Closure for `Red` (CR2) -/

theorem red_cr2 : ∀ {k : Nat} {ρ : TyEnv} {A : Ty} {M N : Term},
    Red k ρ A M → (M ⟶ₛ N) → Red k ρ A N := by
  intro k ρ A
  induction A generalizing k ρ with
  | tvar n =>
    intro M N hM hstep
    exact (ρ n).cr2 hM hstep
  | arr A B ihA ihB =>
    intro M N hM hstep
    intro k' hk P hP
    have hMP : Red k' ρ B (app (shiftTypeInTerm (k' - k) 0 M) P) := hM k' hk P hP
    have hshift : shiftTypeInTerm (k' - k) 0 M ⟶ₛ shiftTypeInTerm (k' - k) 0 N :=
      shiftTypeInTerm_preserves_step (d := k' - k) (c := 0) hstep
    have happ : app (shiftTypeInTerm (k' - k) 0 M) P ⟶ₛ app (shiftTypeInTerm (k' - k) 0 N) P :=
      StrongStep.appL hshift
    exact ihB (k := k') (ρ := ρ) (M := app (shiftTypeInTerm (k' - k) 0 M) P)
      (N := app (shiftTypeInTerm (k' - k) 0 N) P) hMP happ
  | all A ih =>
    intro M N hM hstep
    intro k' hk R
    have hInst :
        Red (k' + 1) (extendTyEnv ρ R) A
          (tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0)) :=
      hM k' hk R
    have hshift0 : shiftTypeInTerm 1 0 M ⟶ₛ shiftTypeInTerm 1 0 N :=
      shiftTypeInTerm_preserves_step (d := 1) (c := 0) hstep
    have hshift1 :
        shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M) ⟶ₛ
          shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 N) :=
      shiftTypeInTerm_preserves_step (d := k' - k) (c := 1) hshift0
    have happ :
        tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0) ⟶ₛ
          tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 N)) (tvar 0) :=
      StrongStep.tappL hshift1
    exact ih (k := k' + 1) (ρ := extendTyEnv ρ R)
      (M := tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0))
      (N := tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 N)) (tvar 0))
      hInst happ

/-- Multi-step CR2: reducibility is preserved by multi-step forward reduction. -/
theorem red_cr2_multi : ∀ {k : Nat} {ρ : TyEnv} {A : Ty} {M N : Term},
    Red k ρ A M → (M ⟶ₛ* N) → Red k ρ A N := by
  intro k ρ A M N hM hsteps
  induction hsteps with
  | refl => exact hM
  | step hstep _ ih => exact ih (red_cr2 hM hstep)

/-- Term substitution preserves multi-step reduction. -/
theorem substTerm_preserves_multi_step (k : Nat) (P : Term) :
    ∀ {M N : Term}, (M ⟶ₛ* N) → substTerm k P M ⟶ₛ* substTerm k P N := by
  intro M N h
  induction h with
  | refl => exact StrongMultiStep.refl _
  | step hstep _ ih =>
    exact StrongMultiStep.step (substTerm_preserves_step k P hstep) ih

/-- shiftTypeInTerm preserves multi-step reduction. -/
theorem shiftTypeInTerm_preserves_multi_step (d c : Nat) :
    ∀ {M N : Term}, (M ⟶ₛ* N) → shiftTypeInTerm d c M ⟶ₛ* shiftTypeInTerm d c N := by
  intro M N h
  induction h with
  | refl => exact StrongMultiStep.refl _
  | step hstep _ ih =>
    exact StrongMultiStep.step (shiftTypeInTerm_preserves_step d c hstep) ih

/-- substTypeInTerm preserves multi-step reduction. -/
theorem substTypeInTerm_preserves_multi_step (k : Nat) (τ : Ty) :
    ∀ {M N : Term}, (M ⟶ₛ* N) → substTypeInTerm k τ M ⟶ₛ* substTypeInTerm k τ N := by
  intro M N h
  induction h with
  | refl => exact StrongMultiStep.refl _
  | step hstep _ ih =>
    exact StrongMultiStep.step (substTypeInTerm_preserves_step k τ hstep) ih

/-! ## Weakening in the Type-Variable World -/

theorem red_wk : ∀ {k : Nat} {ρ : TyEnv} {A : Ty} {M : Term},
    Red k ρ A M → Red (k + 1) ρ A (shiftTypeInTerm 1 0 M) := by
  intro k ρ A
  induction A generalizing k ρ with
  | tvar n =>
    intro M hM
    exact (ρ n).wk hM
  | arr A B ihA ihB =>
    intro M hM
    intro k' hk' N hN
    have hk : k ≤ k' := Nat.le_trans (Nat.le_succ k) hk'
    have hApp : Red k' ρ B (app (shiftTypeInTerm (k' - k) 0 M) N) := hM k' hk N hN
    have hsub : (k' - (k + 1)) + 1 = k' - k := by omega
    have hEq :
        shiftTypeInTerm (k' - (k + 1)) 0 (shiftTypeInTerm 1 0 M) =
          shiftTypeInTerm (k' - k) 0 M := by
      simpa [hsub] using
        (shiftTypeInTerm_add (d₁ := k' - (k + 1)) (d₂ := 1) (c := 0) M)
    simpa [hEq] using hApp
  | all A ih =>
    intro M hM
    intro k' hk' R
    have hk : k ≤ k' := Nat.le_trans (Nat.le_succ k) hk'
    have hInst :
        Red (k' + 1) (extendTyEnv ρ R) A
          (tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0)) :=
      hM k' hk R
    have hsub : (k' - (k + 1)) + 1 = k' - k := by omega
    have hEq :
        shiftTypeInTerm (k' - (k + 1)) 1 (shiftTypeInTerm 1 0 (shiftTypeInTerm 1 0 M)) =
          shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M) := by
      -- Commute the outer shift past the head shift, then reassociate.
      have hcomm :
          shiftTypeInTerm (k' - (k + 1)) 1 (shiftTypeInTerm 1 0 (shiftTypeInTerm 1 0 M)) =
            shiftTypeInTerm 1 0 (shiftTypeInTerm (k' - (k + 1)) 0 (shiftTypeInTerm 1 0 M)) := by
        simpa using
          (shiftTypeInTerm_comm_succ (d := k' - (k + 1)) (b := 0) (c := 0) (Nat.zero_le 0)
            (shiftTypeInTerm 1 0 M))
      -- Similarly for the RHS.
      have hcommR :
          shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M) =
            shiftTypeInTerm 1 0 (shiftTypeInTerm (k' - k) 0 M) := by
        simpa using
          (shiftTypeInTerm_comm_succ (d := k' - k) (b := 0) (c := 0) (Nat.zero_le 0) M)
      -- Now reduce to the old arithmetic identity under the outer `shiftTypeInTerm 1 0`.
      calc
        shiftTypeInTerm (k' - (k + 1)) 1 (shiftTypeInTerm 1 0 (shiftTypeInTerm 1 0 M))
            = shiftTypeInTerm 1 0 (shiftTypeInTerm (k' - (k + 1)) 0 (shiftTypeInTerm 1 0 M)) := hcomm
        _ = shiftTypeInTerm 1 0 (shiftTypeInTerm (k' - k) 0 M) := by
              -- reassociate the shifts at cutoff 0
              have : shiftTypeInTerm (k' - (k + 1)) 0 (shiftTypeInTerm 1 0 M) =
                    shiftTypeInTerm (k' - k) 0 M := by
                      simpa [hsub] using
                        (shiftTypeInTerm_add (d₁ := k' - (k + 1)) (d₂ := 1) (c := 0) M)
              simp [this]
        _ = shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M) := by simp [hcommR]
    simpa [hEq] using hInst

theorem red_wkN {k k' : Nat} {ρ : TyEnv} {A : Ty} {M : Term}
    (hM : Red k ρ A M) (hk : k ≤ k') : Red k' ρ A (shiftTypeInTerm (k' - k) 0 M) := by
  -- First prove the additive form `k + d`.
  have hwk_add : ∀ d : Nat, Red k ρ A M → Red (k + d) ρ A (shiftTypeInTerm d 0 M) := by
    intro d
    induction d with
    | zero =>
      intro h
      simpa [shiftTypeInTerm_zero] using h
    | succ d ih =>
      intro h
      have h' : Red (k + d + 1) ρ A (shiftTypeInTerm 1 0 (shiftTypeInTerm d 0 M)) := by
        -- `red_wk` at world `k+d` applied to the IH.
        simpa [Nat.add_assoc] using (red_wk (k := k + d) (ρ := ρ) (A := A) (M := shiftTypeInTerm d 0 M) (ih h))
      -- Reassociate the shifts.
      simpa [shiftTypeInTerm_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'
  -- Use `k' = k + (k' - k)` for `k ≤ k'`.
  have hk' : k + (k' - k) = k' := Nat.add_sub_of_le hk
  simpa [hk'] using hwk_add (k' - k) hM

/-! ## Strong Normalization from Shifted Terms -/

theorem sn_of_shiftTypeInTerm (d c : Nat) {M : Term} (h : SN (shiftTypeInTerm d c M)) : SN M := by
  have : ∀ T, SN T → ∀ M, T = shiftTypeInTerm d c M → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M hEq
      subst hEq
      apply sn_intro
      intro M' hstep
      have hstep' : shiftTypeInTerm d c M ⟶ₛ shiftTypeInTerm d c M' :=
        shiftTypeInTerm_preserves_step (d := d) (c := c) hstep
      exact ih (shiftTypeInTerm d c M') hstep' M' rfl
  exact this (shiftTypeInTerm d c M) h M rfl

theorem sn_shiftTypeInTerm (d c : Nat) {M : Term} (h : SN M) : SN (shiftTypeInTerm d c M) := by
  induction h with
  | intro M hacc ih =>
    apply sn_intro
    intro N hstep
    rcases step_of_shiftTypeInTerm_step (d := d) (c := c) hstep with ⟨N', hN', rfl⟩
    exact ih N' hN'

/-- Any reduction step on a term-shifted term comes from a step on the original term. -/
theorem step_of_shiftTermUp_step {M N' : Term} (d c : Nat) (h : shiftTermUp d c M ⟶ₛ N') :
    ∃ N, M ⟶ₛ N ∧ N' = shiftTermUp d c N := by
  generalize hM_eq : shiftTermUp d c M = M' at h
  induction h generalizing M c with
  | beta τ body arg =>
    cases M with
    | app A B =>
      simp only [shiftTermUp] at hM_eq
      injection hM_eq with hA hB
      cases A with
      | lam τ' A' =>
        simp only [shiftTermUp] at hA
        injection hA with _ hA'
        refine ⟨substTerm0 B A', StrongStep.beta τ' A' B, ?_⟩
        simp only [shiftTermUp_substTerm0, hA', hB]
      | var _ => simp only [shiftTermUp] at hA; split at hA <;> cases hA
      | app _ _ => simp only [shiftTermUp] at hA; cases hA
      | tlam _ => simp only [shiftTermUp] at hA; cases hA
      | tapp _ _ => simp only [shiftTermUp] at hA; cases hA
    | var _ => simp only [shiftTermUp] at hM_eq; split at hM_eq <;> cases hM_eq
    | lam _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | tlam _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | tapp _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
  | tbeta body τ =>
    cases M with
    | tapp A σ =>
      simp only [shiftTermUp] at hM_eq
      injection hM_eq with hA hσ
      cases A with
      | tlam A' =>
        simp only [shiftTermUp] at hA
        injection hA with hA'
        refine ⟨substTypeInTerm0 σ A', StrongStep.tbeta A' σ, ?_⟩
        unfold substTypeInTerm0
        rw [← hA', ← hσ]
        exact substTypeInTerm_shiftTermUp_comm 0 σ d c A'
      | var _ => simp only [shiftTermUp] at hA; split at hA <;> cases hA
      | lam _ _ => simp only [shiftTermUp] at hA; cases hA
      | app _ _ => simp only [shiftTermUp] at hA; cases hA
      | tapp _ _ => simp only [shiftTermUp] at hA; cases hA
    | var _ => simp only [shiftTermUp] at hM_eq; split at hM_eq <;> cases hM_eq
    | lam _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | app _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | tlam _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
  | lam h ih =>
    cases M with
    | lam τ A =>
      simp only [shiftTermUp] at hM_eq
      injection hM_eq with hτ hA
      obtain ⟨N, hN, rfl⟩ := ih (c+1) hA
      exact ⟨lam τ N, StrongStep.lam hN, by simp only [shiftTermUp, hτ]⟩
    | var _ => simp only [shiftTermUp] at hM_eq; split at hM_eq <;> cases hM_eq
    | app _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | tlam _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | tapp _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
  | appL h ih =>
    cases M with
    | app A B =>
      simp only [shiftTermUp] at hM_eq
      injection hM_eq with hA hB
      obtain ⟨N, hN, rfl⟩ := ih c hA
      exact ⟨app N B, StrongStep.appL hN, by simp [shiftTermUp, hB]⟩
    | var _ => simp only [shiftTermUp] at hM_eq; split at hM_eq <;> cases hM_eq
    | lam _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | tlam _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | tapp _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
  | appR h ih =>
    cases M with
    | app A B =>
      simp only [shiftTermUp] at hM_eq
      injection hM_eq with hA hB
      obtain ⟨N, hN, rfl⟩ := ih c hB
      exact ⟨app A N, StrongStep.appR hN, by simp [shiftTermUp, hA]⟩
    | var _ => simp only [shiftTermUp] at hM_eq; split at hM_eq <;> cases hM_eq
    | lam _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | tlam _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | tapp _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
  | tlam h ih =>
    cases M with
    | tlam A =>
      simp only [shiftTermUp] at hM_eq
      injection hM_eq with hA
      obtain ⟨N, hN, rfl⟩ := ih c hA
      exact ⟨tlam N, StrongStep.tlam hN, by simp [shiftTermUp]⟩
    | var _ => simp only [shiftTermUp] at hM_eq; split at hM_eq <;> cases hM_eq
    | lam _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | app _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | tapp _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
  | tappL h ih =>
    cases M with
    | tapp A σ =>
      simp only [shiftTermUp] at hM_eq
      injection hM_eq with hA hσ
      obtain ⟨N, hN, rfl⟩ := ih c hA
      exact ⟨tapp N σ, StrongStep.tappL hN, by simp [shiftTermUp, hσ]⟩
    | var _ => simp only [shiftTermUp] at hM_eq; split at hM_eq <;> cases hM_eq
    | lam _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | app _ _ => simp only [shiftTermUp] at hM_eq; cases hM_eq
    | tlam _ => simp only [shiftTermUp] at hM_eq; cases hM_eq

/-- SN is preserved by term variable shifting. -/
theorem sn_shiftTermUp (d c : Nat) {M : Term} (h : SN M) : SN (shiftTermUp d c M) := by
  induction h generalizing d c with
  | intro M _ ih =>
    apply sn_intro
    intro N' hstep
    obtain ⟨N, hMN, rfl⟩ := step_of_shiftTermUp_step d c hstep
    exact ih N hMN d c

theorem sn_of_substTypeInTerm (k : Nat) (σ : Ty) {M : Term} (h : SN (substTypeInTerm k σ M)) : SN M := by
  have : ∀ T, SN T → ∀ M, T = substTypeInTerm k σ M → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M hEq
      subst hEq
      apply sn_intro
      intro M' hstep
      have hstep' : substTypeInTerm k σ M ⟶ₛ substTypeInTerm k σ M' :=
        substTypeInTerm_preserves_step (k := k) (σ := σ) hstep
      exact ih (substTypeInTerm k σ M') hstep' M' rfl
  exact this (substTypeInTerm k σ M) h M rfl

theorem sn_substTypeInTerm (k : Nat) (σ : Ty) {M : Term} (h : SN M) : SN (substTypeInTerm k σ M) := by
  induction h with
  | intro M hacc ih =>
    apply sn_intro
    intro N hstep
    rcases step_of_substTypeInTerm_step (k := k) (σ := σ) hstep with ⟨N', hN', rfl⟩
    exact ih N' hN'

/-- The SN candidate: all strongly normalizing terms. -/
def SNCandidate : Candidate where
  pred _ M := SN M
  cr1 h := h
  cr2 := sn_of_step
  cr3 _hneut hsteps := sn_intro hsteps
  wk h := sn_shiftTypeInTerm 1 0 h
  tySubstLevelDrop σ h := sn_substTypeInTerm 0 σ h
  termStructInv h := h.sn_iff

/-- Default type environment mapping all type variables to the SN candidate. -/
def defaultTyEnv : TyEnv := fun _ => SNCandidate

theorem sn_lam {τ : Ty} {M : Term} (h : SN M) : SN (lam τ M) := by
  induction h with
  | intro M hacc ih =>
    apply sn_intro
    intro N hstep
    cases hstep with
    | lam hM =>
      exact ih _ hM

/-- If `lam τ M` is SN, then `M` is SN. -/
theorem sn_of_lam {τ : Ty} {M : Term} (h : SN (lam τ M)) : SN M := by
  generalize hEq : lam τ M = L at h
  induction h generalizing M with
  | intro L hL_acc ihL =>
    apply sn_intro
    intro M' hstep
    have hLstep : L ⟶ₛ lam τ M' := by subst hEq; exact StrongStep.lam hstep
    exact ihL (lam τ M') hLstep rfl

/-- If `tlam M` is SN, then `M` is SN. -/
theorem sn_of_tlam {M : Term} (h : SN (tlam M)) : SN M := by
  generalize hEq : tlam M = L at h
  induction h generalizing M with
  | intro L hL_acc ihL =>
    apply sn_intro
    intro M' hstep
    have hLstep : L ⟶ₛ tlam M' := by subst hEq; exact StrongStep.tlam hstep
    exact ihL (tlam M') hLstep rfl

theorem sn_tlam {M : Term} (h : SN M) : SN (tlam M) := by
  induction h with
  | intro M hacc ih =>
    apply sn_intro
    intro N hstep
    cases hstep with
    | tlam hM =>
      exact ih _ hM

theorem sn_of_instFresh {M : Term} (h : SN (instFresh M)) : SN M := by
  cases M with
  | tlam Mbody =>
    have hShift : SN (shiftTypeInTerm 1 1 Mbody) := by
      -- `instFresh` is a type-substitution on the shifted body.
      simpa [instFresh] using sn_of_substTypeInTerm (k := 0) (σ := tvar 0) (M := shiftTypeInTerm 1 1 Mbody) h
    have hBody : SN Mbody := sn_of_shiftTypeInTerm 1 1 hShift
    exact sn_tlam hBody
  | var n =>
    have hShift : SN (shiftTypeInTerm 1 0 (var n)) := by
      simpa [instFresh] using sn_tapp_left (M := shiftTypeInTerm 1 0 (var n)) (τ := tvar 0) h
    exact sn_of_shiftTypeInTerm 1 0 hShift
  | lam τ Mbody =>
    have hShift : SN (shiftTypeInTerm 1 0 (lam τ Mbody)) := by
      simpa [instFresh] using sn_tapp_left (M := shiftTypeInTerm 1 0 (lam τ Mbody)) (τ := tvar 0) h
    exact sn_of_shiftTypeInTerm 1 0 hShift
  | app M N =>
    have hShift : SN (shiftTypeInTerm 1 0 (app M N)) := by
      simpa [instFresh] using sn_tapp_left (M := shiftTypeInTerm 1 0 (app M N)) (τ := tvar 0) h
    exact sn_of_shiftTypeInTerm 1 0 hShift
  | tapp M τ =>
    have hShift : SN (shiftTypeInTerm 1 0 (tapp M τ)) := by
      simpa [instFresh] using sn_tapp_left (M := shiftTypeInTerm 1 0 (tapp M τ)) (τ := tvar 0) h
    exact sn_of_shiftTypeInTerm 1 0 hShift

theorem neutral_shiftTypeInTerm (d c : Nat) {M : Term} (h : IsNeutral M) :
    IsNeutral (shiftTypeInTerm d c M) := by
  induction M generalizing c with
  | var n =>
    simp [IsNeutral, shiftTypeInTerm] at h ⊢
  | lam τ M ih =>
    simp [IsNeutral] at h
  | app M N ihM ihN =>
    cases M <;> simp [IsNeutral, shiftTypeInTerm] at h ⊢ <;> first | exact h | trivial
  | tlam M ih =>
    simp [IsNeutral] at h
  | tapp M τ ih =>
    cases M <;> simp [IsNeutral, shiftTypeInTerm] at h ⊢ <;> first | exact h | trivial

theorem neutral_substTypeInTerm (k : Nat) (σ : Ty) {M : Term} (h : IsNeutral M) :
    IsNeutral (substTypeInTerm k σ M) := by
  cases M <;> simp [IsNeutral, substTypeInTerm] at h ⊢ <;> try trivial <;> exact h

/-! ## Term-Structure Equivalence Lemmas (Additional)

The basic TermStructEq lemmas (refl, symm, trans, sn_iff) are at the top of the file.
Here we prove additional lemmas used in the proof.
-/

/-- Type shifting preserves term-structure (with itself). -/
theorem shiftTypeInTerm_TermStructEq (d c : Nat) (M : Term) :
    shiftTypeInTerm d c M ≈ₜ M := by
  induction M generalizing c with
  | var n => simp [shiftTypeInTerm]; exact TermStructEq.var n
  | lam τ M ih => simp [shiftTypeInTerm]; exact TermStructEq.lam _ τ _ M (ih c)
  | app M N ihM ihN => simp [shiftTypeInTerm]; exact TermStructEq.app _ M _ N (ihM c) (ihN c)
  | tlam M ih => simp [shiftTypeInTerm]; exact TermStructEq.tlam _ M (ih (c + 1))
  | tapp M τ ih => simp [shiftTypeInTerm]; exact TermStructEq.tapp _ M _ τ (ih c)

/-- Type substitution preserves term-structure (with itself). -/
theorem substTypeInTerm_TermStructEq (k : Nat) (σ : Ty) (M : Term) :
    substTypeInTerm k σ M ≈ₜ M := by
  induction M generalizing k σ with
  | var n => simp [substTypeInTerm]; exact TermStructEq.var n
  | lam τ M ih => simp [substTypeInTerm]; exact TermStructEq.lam _ τ _ M (ih k σ)
  | app M N ihM ihN => simp [substTypeInTerm]; exact TermStructEq.app _ M _ N (ihM k σ) (ihN k σ)
  | tlam M ih => simp [substTypeInTerm]; exact TermStructEq.tlam _ M (ih (k + 1) (shiftTyUp 1 0 σ))
  | tapp M τ ih => simp [substTypeInTerm]; exact TermStructEq.tapp _ M _ τ (ih k σ)

/-- Composed type operations produce term-structure equivalent terms. -/
theorem shiftSubst_substShift_TermStructEq (d c k : Nat) (σ : Ty) (M : Term) :
    shiftTypeInTerm d c (substTypeInTerm k σ M) ≈ₜ substTypeInTerm k σ (shiftTypeInTerm d c M) := by
  have h1 : shiftTypeInTerm d c (substTypeInTerm k σ M) ≈ₜ M :=
    TermStructEq.trans (shiftTypeInTerm_TermStructEq d c _) (substTypeInTerm_TermStructEq k σ M)
  have h2 : substTypeInTerm k σ (shiftTypeInTerm d c M) ≈ₜ M :=
    TermStructEq.trans (substTypeInTerm_TermStructEq k σ _) (shiftTypeInTerm_TermStructEq d c M)
  exact TermStructEq.trans h1 (TermStructEq.symm h2)

/-- Term-structure equivalence preserves neutrality. -/
theorem TermStructEq.neutral {M N : Term} (h : M ≈ₜ N) : IsNeutral M ↔ IsNeutral N := by
  induction h with
  | var n => simp [IsNeutral]
  | lam _ _ _ _ _ => simp [IsNeutral]
  | app _ _ _ _ _ _ => simp [IsNeutral]
  | tlam _ _ _ => simp [IsNeutral]
  | tapp _ _ _ _ _ => simp [IsNeutral]

/-- Term substitution preserves term-structure equivalence. -/
theorem substTerm_TermStructEq {M₁ M₂ N₁ N₂ : Term} (k : Nat)
    (hM : M₁ ≈ₜ M₂) (hN : N₁ ≈ₜ N₂) : substTerm k N₁ M₁ ≈ₜ substTerm k N₂ M₂ := by
  induction hM generalizing k N₁ N₂ with
  | var n =>
    simp only [substTerm]
    by_cases hnk : n < k
    · simp [hnk]; exact TermStructEq.var n
    · by_cases heq : n = k
      · simp [heq]; exact hN
      · simp [hnk, heq]; exact TermStructEq.var (n - 1)
  | lam τ₁ τ₂ M₁ M₂ _ ih =>
    simp only [substTerm]
    have hN' : shiftTermUp 1 0 N₁ ≈ₜ shiftTermUp 1 0 N₂ := shiftTermUp_TermStructEq 1 0 hN
    exact TermStructEq.lam τ₁ τ₂ _ _ (ih (k + 1) hN')
  | app M₁ M₂ P₁ P₂ _ _ ihM ihP =>
    simp only [substTerm]
    exact TermStructEq.app _ _ _ _ (ihM k hN) (ihP k hN)
  | tlam M₁ M₂ _ ih =>
    simp only [substTerm]
    have hN' : shiftTypeInTerm 1 0 N₁ ≈ₜ shiftTypeInTerm 1 0 N₂ := shiftTypeInTerm_TermStructEq' 1 0 hN
    exact TermStructEq.tlam _ _ (ih k hN')
  | tapp M₁ M₂ τ₁ τ₂ _ ih =>
    simp only [substTerm]
    exact TermStructEq.tapp _ _ τ₁ τ₂ (ih k hN)
where
  shiftTermUp_TermStructEq (d c : Nat) {M N : Term} (h : M ≈ₜ N) : shiftTermUp d c M ≈ₜ shiftTermUp d c N := by
    induction h generalizing c with
    | var n =>
      simp only [shiftTermUp]
      by_cases hn : n < c <;> simp [hn] <;> exact TermStructEq.var _
    | lam τ₁ τ₂ M₁ M₂ _ ih =>
      simp only [shiftTermUp]; exact TermStructEq.lam τ₁ τ₂ _ _ (ih (c + 1))
    | app M₁ M₂ N₁ N₂ _ _ ihM ihN =>
      simp only [shiftTermUp]; exact TermStructEq.app _ _ _ _ (ihM c) (ihN c)
    | tlam M₁ M₂ _ ih =>
      simp only [shiftTermUp]; exact TermStructEq.tlam _ _ (ih c)
    | tapp M₁ M₂ τ₁ τ₂ _ ih =>
      simp only [shiftTermUp]; exact TermStructEq.tapp _ _ τ₁ τ₂ (ih c)
  shiftTypeInTerm_TermStructEq' (d c : Nat) {M N : Term} (h : M ≈ₜ N) :
      shiftTypeInTerm d c M ≈ₜ shiftTypeInTerm d c N := by
    induction h generalizing c with
    | var n => simp [shiftTypeInTerm]; exact TermStructEq.var n
    | lam τ₁ τ₂ M₁ M₂ _ ih =>
      simp [shiftTypeInTerm]; exact TermStructEq.lam _ _ _ _ (ih c)
    | app M₁ M₂ N₁ N₂ _ _ ihM ihN =>
      simp [shiftTypeInTerm]; exact TermStructEq.app _ _ _ _ (ihM c) (ihN c)
    | tlam M₁ M₂ _ ih =>
      simp [shiftTypeInTerm]; exact TermStructEq.tlam _ _ (ih (c + 1))
    | tapp M₁ M₂ τ₁ τ₂ _ ih =>
      simp [shiftTypeInTerm]; exact TermStructEq.tapp _ _ _ _ (ih c)

/-- If M ≈ₜ N and M steps, then N steps to a term-structure equivalent result. -/
theorem TermStructEq.step {M N : Term} (h : M ≈ₜ N) (hstep : M ⟶ₛ M') :
    ∃ N', (N ⟶ₛ N') ∧ (M' ≈ₜ N') := by
  induction h generalizing M' with
  | var n => cases hstep
  | lam τ₁ τ₂ M₁ M₂ hM ih =>
    cases hstep with
    | lam hM' =>
      obtain ⟨N', hN', hEq⟩ := ih hM'
      exact ⟨Term.lam τ₂ N', StrongStep.lam hN', TermStructEq.lam τ₁ τ₂ _ _ hEq⟩
  | app M₁ M₂ N₁ N₂ hM hN ihM ihN =>
    cases hstep with
    | beta τ body arg =>
      cases hM with
      | lam τ₁ τ₂ body₁ body₂ hbody =>
        -- M₁ = lam τ₁ body₁, M₂ = lam τ₂ body₂
        -- M' = substTerm0 N₁ body₁
        -- Need to show: app (lam τ₂ body₂) N₂ ⟶ₛ substTerm0 N₂ body₂ and substTerm0 N₁ body₁ ≈ₜ substTerm0 N₂ body₂
        exact ⟨substTerm0 N₂ body₂, StrongStep.beta τ₂ body₂ N₂,
               substTerm_TermStructEq 0 hbody hN⟩
    | appL hM' =>
      obtain ⟨M₂', hM₂', hEq⟩ := ihM hM'
      exact ⟨Term.app M₂' N₂, StrongStep.appL hM₂', TermStructEq.app _ _ _ _ hEq hN⟩
    | appR hN' =>
      obtain ⟨N₂', hN₂', hEq⟩ := ihN hN'
      exact ⟨Term.app M₂ N₂', StrongStep.appR hN₂', TermStructEq.app _ _ _ _ hM hEq⟩
  | tlam M₁ M₂ hM ih =>
    cases hstep with
    | tlam hM' =>
      obtain ⟨N', hN', hEq⟩ := ih hM'
      exact ⟨Term.tlam N', StrongStep.tlam hN', TermStructEq.tlam _ _ hEq⟩
  | tapp M₁ M₂ τ₁ τ₂ hM ih =>
    cases hstep with
    | tbeta body _ =>
      -- M₁ = tlam body, M' = substTypeInTerm0 τ₁ body
      cases hM with
      | tlam body₁ body₂ hbody =>
        -- body₁ = body, M₂ = tlam body₂, body₁ ≈ₜ body₂
        exact ⟨substTypeInTerm0 τ₂ body₂, StrongStep.tbeta body₂ τ₂,
               TermStructEq.trans (substTypeInTerm_TermStructEq 0 τ₁ body)
                 (TermStructEq.trans hbody (TermStructEq.symm (substTypeInTerm_TermStructEq 0 τ₂ body₂)))⟩
    | tappL hM' =>
      obtain ⟨M₂', hM₂', hEq⟩ := ih hM'
      exact ⟨Term.tapp M₂' τ₂, StrongStep.tappL hM₂', TermStructEq.tapp _ _ τ₁ τ₂ hEq⟩

/-! ## CR1/CR3 for the Logical Relation -/

def CR_Props (k : Nat) (ρ : TyEnv) (A : Ty) : Prop :=
  (∀ M, Red k ρ A M → SN M) ∧
  (∀ M, (∀ N, M ⟶ₛ N → Red k ρ A N) → IsNeutral M → Red k ρ A M)

theorem cr_props_all : ∀ (k : Nat) (ρ : TyEnv) (A : Ty), CR_Props k ρ A := by
  intro k ρ A
  induction A generalizing k ρ with
  | tvar n =>
    constructor
    · intro M hM
      exact (ρ n).cr1 hM
    · intro M hred hneut
      exact (ρ n).cr3 hneut hred
  | arr A B ihA ihB =>
    constructor
    · intro M hM
      -- Use a reducible neutral argument (var 0) to get SN of M.
      obtain ⟨_, cr3_A⟩ := ihA (k := k) (ρ := ρ)
      obtain ⟨cr1_B, _⟩ := ihB (k := k) (ρ := ρ)
      have hvar0 : Red k ρ A (var 0) := by
        apply cr3_A (var 0)
        · intro N hstep; cases hstep
        · exact neutral_var 0
      have happ : Red k ρ B (app M (var 0)) := by
        simpa [Nat.sub_self, shiftTypeInTerm_zero] using hM k (Nat.le_refl k) (var 0) hvar0
      have happ_sn : SN (app M (var 0)) := cr1_B _ happ
      exact sn_app_left happ_sn
    · intro M hred hneut
      -- Goal: `Red k ρ (A ⇒ B) M`, i.e. stable in all larger worlds.
      intro k' hk P hP
      obtain ⟨cr1_A, _⟩ := ihA (k := k') (ρ := ρ)
      obtain ⟨_, cr3_B⟩ := ihB (k := k') (ρ := ρ)
      have hP_sn : SN P := cr1_A _ hP
      have hneut' : IsNeutral (shiftTypeInTerm (k' - k) 0 M) :=
        neutral_shiftTypeInTerm (d := k' - k) (c := 0) hneut
      -- Strong induction on SN arguments.
      have : ∀ Q, SN Q → Red k' ρ A Q → Red k' ρ B (app (shiftTypeInTerm (k' - k) 0 M) Q) := by
        intro Q hQ_sn
        induction hQ_sn with
        | intro Q _ ihQ =>
          intro hQ
          have h_neut_app : IsNeutral (app (shiftTypeInTerm (k' - k) 0 M) Q) := by
            simp [IsNeutral]
          apply cr3_B (app (shiftTypeInTerm (k' - k) 0 M) Q)
          · intro R hstep
            cases neutral_app_step hneut' hstep with
            | inl hfun =>
              rcases hfun with ⟨M', hM', rfl⟩
              rcases step_of_shiftTypeInTerm_step (d := k' - k) (c := 0) hM' with ⟨M0, hM0, rfl⟩
              have hM0_red : Red k ρ (arr A B) M0 := hred M0 hM0
              exact hM0_red k' hk Q hQ
            | inr harg =>
              rcases harg with ⟨Q', hQ', rfl⟩
              have hQ'_red : Red k' ρ A Q' := red_cr2 (k := k') (ρ := ρ) (A := A) hQ hQ'
              exact (ihQ Q' hQ') hQ'_red
          · exact h_neut_app
      exact this P hP_sn hP
  | all A ih =>
    -- `A` is the body type, interpreted at world (k+1) and extended env.
    constructor
    · intro M hM
      -- Pick an arbitrary candidate (use ρ 0) to get SN of an instantiation.
      let R : Candidate := ρ 0
      have hBodyProps := ih (k := k + 1) (ρ := extendTyEnv ρ R)
      have cr1_body : ∀ T, Red (k + 1) (extendTyEnv ρ R) A T → SN T := hBodyProps.1
      have happ : Red (k + 1) (extendTyEnv ρ R) A (tapp (shiftTypeInTerm 1 0 M) (tvar 0)) := by
        -- At `k' = k`, the additional shift is `0` at cutoff `1`.
        simpa [shiftTypeInTerm_zero] using hM k (Nat.le_refl k) R
      have happ_sn : SN (tapp (shiftTypeInTerm 1 0 M) (tvar 0)) := cr1_body _ happ
      have hshift_sn : SN (shiftTypeInTerm 1 0 M) := sn_tapp_left happ_sn
      exact sn_of_shiftTypeInTerm 1 0 hshift_sn
    · intro M hred hneut
      intro k' hk R
      have hBodyProps := ih (k := k' + 1) (ρ := extendTyEnv ρ R)
      have cr3_body :
          ∀ T,
            (∀ U, T ⟶ₛ U → Red (k' + 1) (extendTyEnv ρ R) A U) →
              IsNeutral T → Red (k' + 1) (extendTyEnv ρ R) A T :=
        hBodyProps.2
      -- The instantiated term is neutral.
      have h_neut_shift : IsNeutral (shiftTypeInTerm 1 0 M) :=
        neutral_shiftTypeInTerm (d := 1) (c := 0) hneut
      have h_neut_inst : IsNeutral (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) :=
        neutral_shiftTypeInTerm (d := k' - k) (c := 1) h_neut_shift
      have h_neut_tapp :
          IsNeutral (tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0)) := by
        simp [IsNeutral]
      apply cr3_body (tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0))
      · intro T hstep
        rcases neutral_tapp_step h_neut_inst hstep with ⟨M', hM', rfl⟩
        rcases step_of_shiftTypeInTerm_step (d := k' - k) (c := 1) hM' with ⟨M1, hM1, rfl⟩
        rcases step_of_shiftTypeInTerm_step (d := 1) (c := 0) hM1 with ⟨M0, hM0, rfl⟩
        have hM0_red : Red k ρ (all A) M0 := hred M0 hM0
        exact hM0_red k' hk R
      · exact h_neut_tapp

/-! ## Term-Structure Invariance of Reducibility

The key insight: since beta reduction ignores type annotations, and reducibility is defined
in terms of reduction behavior, term-structure equivalent terms have the same reducibility.

This allows us to handle the non-commutativity of shiftTypeInTerm and substTypeInTerm:
while they produce syntactically different terms, those terms are term-structure equivalent
and hence have the same reducibility.
-/

/-- A candidate is term-structure invariant if its predicate respects term-structure equivalence.
    This is now always true since `termStructInv` is a field of `Candidate`. -/
def Candidate.TermStructInv (C : Candidate) : Prop :=
  ∀ k M N, M ≈ₜ N → (C.pred k M ↔ C.pred k N)

/-- Every candidate is term-structure invariant (by the struct field). -/
theorem Candidate.termStructInv_holds (C : Candidate) : C.TermStructInv := by
  intro k M N h
  exact C.termStructInv h

/-- SNCandidate is term-structure invariant. -/
theorem SNCandidate_TermStructInv : SNCandidate.TermStructInv :=
  SNCandidate.termStructInv_holds

/-- A type environment is term-structure invariant if all its candidates are. -/
def TyEnv.TermStructInv (ρ : TyEnv) : Prop :=
  ∀ n, (ρ n).TermStructInv

/-- Every type environment is term-structure invariant (since every candidate is). -/
theorem TyEnv.termStructInv_holds (ρ : TyEnv) : ρ.TermStructInv := by
  intro n
  exact (ρ n).termStructInv_holds

/-- Default type environment is term-structure invariant. -/
theorem defaultTyEnv_TermStructInv : defaultTyEnv.TermStructInv :=
  defaultTyEnv.termStructInv_holds

/-- Extension of term-structure invariant environment preserves invariance. -/
theorem extendTyEnv_TermStructInv {ρ : TyEnv} {R : Candidate}
    (_hρ : ρ.TermStructInv) (_hR : R.TermStructInv) : (extendTyEnv ρ R).TermStructInv :=
  (extendTyEnv ρ R).termStructInv_holds

/-- Red is term-structure invariant for all environments.
    We quantify over the environment in the statement so the IH can be applied with extended environments. -/
theorem Red_TermStructInv : ∀ A (ρ : TyEnv) k M N, M ≈ₜ N → (Red k ρ A M ↔ Red k ρ A N) := by
  intro A
  induction A with
  | tvar n =>
    intro ρ k M N h
    simp only [Red]
    exact ρ.termStructInv_holds n k M N h
  | arr A B ihA ihB =>
    intro ρ k M N hMN
    simp only [Red]
    constructor
    · intro hM k' hk P hP
      -- M reduces N, shift preserves term-struct equiv
      have hShiftEq : shiftTypeInTerm (k' - k) 0 M ≈ₜ shiftTypeInTerm (k' - k) 0 N :=
        substTerm_TermStructEq.shiftTypeInTerm_TermStructEq' (k' - k) 0 hMN
      have hAppEq : Term.app (shiftTypeInTerm (k' - k) 0 M) P ≈ₜ Term.app (shiftTypeInTerm (k' - k) 0 N) P :=
        TermStructEq.app _ _ _ _ hShiftEq (TermStructEq.refl P)
      have hApp := hM k' hk P hP
      exact (ihB ρ k' _ _ hAppEq).mp hApp
    · intro hN k' hk P hP
      have hShiftEq : shiftTypeInTerm (k' - k) 0 N ≈ₜ shiftTypeInTerm (k' - k) 0 M :=
        substTerm_TermStructEq.shiftTypeInTerm_TermStructEq' (k' - k) 0 hMN.symm
      have hAppEq : Term.app (shiftTypeInTerm (k' - k) 0 N) P ≈ₜ Term.app (shiftTypeInTerm (k' - k) 0 M) P :=
        TermStructEq.app _ _ _ _ hShiftEq (TermStructEq.refl P)
      have hApp := hN k' hk P hP
      exact (ihB ρ k' _ _ hAppEq).mp hApp
  | all A ih =>
    intro ρ k M N hMN
    simp only [Red]
    constructor
    · intro hM k' hk R
      have hShift1 : shiftTypeInTerm 1 0 M ≈ₜ shiftTypeInTerm 1 0 N :=
        substTerm_TermStructEq.shiftTypeInTerm_TermStructEq' 1 0 hMN
      have hShift2 : shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M) ≈ₜ
                     shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 N) :=
        substTerm_TermStructEq.shiftTypeInTerm_TermStructEq' (k' - k) 1 hShift1
      have hTappEq : Term.tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0) ≈ₜ
                     Term.tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 N)) (tvar 0) :=
        TermStructEq.tapp _ _ _ _ hShift2
      exact (ih (extendTyEnv ρ R) (k' + 1) _ _ hTappEq).mp (hM k' hk R)
    · intro hN k' hk R
      have hShift1 : shiftTypeInTerm 1 0 N ≈ₜ shiftTypeInTerm 1 0 M :=
        substTerm_TermStructEq.shiftTypeInTerm_TermStructEq' 1 0 hMN.symm
      have hShift2 : shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 N) ≈ₜ
                     shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M) :=
        substTerm_TermStructEq.shiftTypeInTerm_TermStructEq' (k' - k) 1 hShift1
      have hTappEq : Term.tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 N)) (tvar 0) ≈ₜ
                     Term.tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0) :=
        TermStructEq.tapp _ _ _ _ hShift2
      exact (ih (extendTyEnv ρ R) (k' + 1) _ _ hTappEq).mp (hN k' hk R)

/-! ## Parallel Term Substitution -/

abbrev Subst := Nat → Term

def liftSubst (σ : Subst) : Subst
  | 0 => var 0
  | n + 1 => shiftTermUp 1 0 (σ n)

def tshiftSubst (σ : Subst) : Subst :=
  fun n => shiftTypeInTerm 1 0 (σ n)

def extendSubst (σ : Subst) (N : Term) : Subst
  | 0 => N
  | n + 1 => σ n

def idSubst : Subst := var

def applySubst (σ : Subst) : Term → Term
  | var n => σ n
  | lam τ M => lam τ (applySubst (liftSubst σ) M)
  | app M N => app (applySubst σ M) (applySubst σ N)
  | tlam M => tlam (applySubst (tshiftSubst σ) M)
  | tapp M τ => tapp (applySubst σ M) τ

theorem liftSubst_ext {σ₁ σ₂ : Subst} (h : ∀ n, σ₁ n = σ₂ n) : ∀ n, liftSubst σ₁ n = liftSubst σ₂ n := by
  intro n
  cases n with
  | zero => simp [liftSubst]
  | succ n =>
    simp [liftSubst, h]

theorem tshiftSubst_ext {σ₁ σ₂ : Subst} (h : ∀ n, σ₁ n = σ₂ n) : ∀ n, tshiftSubst σ₁ n = tshiftSubst σ₂ n := by
  intro n
  simp [tshiftSubst, h]

theorem applySubst_ext {σ₁ σ₂ : Subst} (h : ∀ n, σ₁ n = σ₂ n) : ∀ M, applySubst σ₁ M = applySubst σ₂ M := by
  intro M
  induction M generalizing σ₁ σ₂ with
  | var n =>
    simp [applySubst, h]
  | lam τ M ih =>
    simp [applySubst, ih (σ₁ := liftSubst σ₁) (σ₂ := liftSubst σ₂) (liftSubst_ext h)]
  | app M N ihM ihN =>
    simp [applySubst, ihM h, ihN h]
  | tlam M ih =>
    simp [applySubst, ih (σ₁ := tshiftSubst σ₁) (σ₂ := tshiftSubst σ₂) (tshiftSubst_ext h)]
  | tapp M τ ih =>
    simp [applySubst, ih h]

theorem applySubst_id : ∀ M, applySubst idSubst M = M := by
  intro M
  induction M with
  | var n =>
    simp [applySubst, idSubst]
  | lam τ M ih =>
    simp [applySubst]
    have hlift : ∀ n, liftSubst idSubst n = idSubst n := by
      intro n
      cases n with
      | zero => simp [liftSubst, idSubst]
      | succ n => simp [liftSubst, idSubst, shiftTermUp]
    have happly : applySubst (liftSubst idSubst) M = applySubst idSubst M :=
      applySubst_ext hlift M
    simp [happly, ih]
  | app M N ihM ihN =>
    simp [applySubst, ihM, ihN]
  | tlam M ih =>
    simp [applySubst]
    have htshift : ∀ n, tshiftSubst idSubst n = idSubst n := by
      intro n
      simp [tshiftSubst, idSubst, shiftTypeInTerm]
    have happly : applySubst (tshiftSubst idSubst) M = applySubst idSubst M :=
      applySubst_ext htshift M
    simp [happly, ih]
  | tapp M τ ih =>
    simp [applySubst, ih]

/-! ## Interaction of Parallel and Single Substitution -/

theorem shiftTermUp_zero (c : Nat) : ∀ M : Term, shiftTermUp 0 c M = M := by
  intro M
  induction M generalizing c with
  | var n =>
    by_cases hn : n < c <;> simp [shiftTermUp, hn]
  | lam τ M ih =>
    simp [shiftTermUp, ih (c := c + 1)]
  | app M N ihM ihN =>
    simp [shiftTermUp, ihM (c := c), ihN (c := c)]
  | tlam M ih =>
    simp [shiftTermUp, ih (c := c)]
  | tapp M τ ih =>
    simp [shiftTermUp, ih (c := c)]

theorem shiftTermUp_add (d₁ d₂ c : Nat) : ∀ M : Term,
    shiftTermUp d₁ c (shiftTermUp d₂ c M) = shiftTermUp (d₁ + d₂) c M := by
  intro M
  induction M generalizing c with
  | var n =>
    by_cases hn : n < c
    · simp [shiftTermUp, hn]
    · have hn' : ¬n + d₂ < c := by
        have : c ≤ n := Nat.le_of_not_gt hn
        exact Nat.not_lt.mpr (Nat.le_trans this (Nat.le_add_right n d₂))
      simp [shiftTermUp, hn, hn'] <;> omega
  | lam τ M ih =>
    simp [shiftTermUp, ih (c := c + 1)]
  | app M N ihM ihN =>
    simp [shiftTermUp, ihM (c := c), ihN (c := c)]
  | tlam M ih =>
    simp [shiftTermUp, ih (c := c)]
  | tapp M τ ih =>
    simp [shiftTermUp, ih (c := c)]

theorem shiftTermUp_succ_shiftTermUp (j c : Nat) : ∀ M : Term,
    shiftTermUp 1 (j + c) (shiftTermUp j c M) = shiftTermUp (j + 1) c M := by
  intro M
  induction M generalizing j c with
  | var n =>
    by_cases hnc : n < c
    · have hnjc : n < j + c := Nat.lt_of_lt_of_le hnc (Nat.le_add_left c j)
      simp [shiftTermUp, hnc, hnjc]
    · have hnjc : ¬n + j < j + c := by
        have : c ≤ n := Nat.le_of_not_gt hnc
        have : j + c ≤ n + j := by omega
        exact Nat.not_lt.mpr this
      simp [shiftTermUp, hnc, hnjc, Nat.add_assoc]
  | lam τ M ih =>
    simpa [shiftTermUp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (j := j) (c := c + 1)
  | app M N ihM ihN =>
    simp [shiftTermUp, ihM (j := j) (c := c), ihN (j := j) (c := c)]
  | tlam M ih =>
    simp [shiftTermUp, ih (j := j) (c := c)]
  | tapp M τ ih =>
    simp [shiftTermUp, ih (j := j) (c := c)]

def liftSubstN : Nat → Subst → Subst
  | 0, σ => σ
  | n + 1, σ => liftSubst (liftSubstN n σ)

theorem liftSubstN_zero (σ : Subst) : liftSubstN 0 σ = σ := rfl

theorem liftSubstN_succ (n : Nat) (σ : Subst) : liftSubstN (n + 1) σ = liftSubst (liftSubstN n σ) := rfl

theorem liftSubstN_spec : ∀ (j : Nat) (σ : Subst) (n : Nat),
    liftSubstN j σ n = if n < j then var n else shiftTermUp j 0 (σ (n - j)) := by
  intro j
  induction j with
  | zero =>
    intro σ n
    simp [liftSubstN, shiftTermUp_zero]
  | succ j ih =>
    intro σ n
    cases n with
    | zero =>
      simp [liftSubstN, liftSubst]
    | succ n =>
      have : liftSubstN (j + 1) σ (n + 1) = shiftTermUp 1 0 (liftSubstN j σ n) := by
        simp [liftSubstN, liftSubst]
      rw [this]
      -- Expand the IH and split on `n < j`.
      by_cases hnj : n < j
      · have hnjs : n + 1 < j + 1 := Nat.succ_lt_succ hnj
        simp [ih, hnj, hnjs, shiftTermUp]
      · have hnjs : ¬n + 1 < j + 1 := by
          simpa [Nat.succ_lt_succ_iff] using hnj
        have hsub : n + 1 - (j + 1) = n - j := by omega
        -- Use IH in the `n ≥ j` branch.
        simp [ih, hnj, hnjs, hsub]
        -- shiftTermUp 1 0 (shiftTermUp j 0 X) = shiftTermUp (j+1) 0 X
        simp [shiftTermUp_add, Nat.add_comm]

theorem tshiftSubst_liftSubst_comm (σ : Subst) : tshiftSubst (liftSubst σ) = liftSubst (tshiftSubst σ) := by
  funext n
  cases n with
  | zero =>
    simp [tshiftSubst, liftSubst, shiftTypeInTerm]
  | succ n =>
    simp [tshiftSubst, liftSubst]
    simpa using (shiftTypeInTerm_shiftTermUp_comm (d := 1) (c := 0) (d' := 1) (c' := 0) (σ n))

theorem tshiftSubst_extendSubst_comm (σ : Subst) (N : Term) :
    tshiftSubst (extendSubst σ N) = extendSubst (tshiftSubst σ) (shiftTypeInTerm 1 0 N) := by
  funext n
  cases n with
  | zero => simp [tshiftSubst, extendSubst]
  | succ n => simp [tshiftSubst, extendSubst]

theorem tshiftSubst_liftSubstN_comm (j : Nat) (σ : Subst) :
    tshiftSubst (liftSubstN j σ) = liftSubstN j (tshiftSubst σ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp [liftSubstN, tshiftSubst_liftSubst_comm, ih]

theorem tshiftSubst_liftSubstN_extendSubst_comm (j : Nat) (σ : Subst) (N : Term) :
    tshiftSubst (liftSubstN j (extendSubst σ N)) =
      liftSubstN j (extendSubst (tshiftSubst σ) (shiftTypeInTerm 1 0 N)) := by
  simpa [tshiftSubst_extendSubst_comm] using
    (tshiftSubst_liftSubstN_comm (j := j) (σ := extendSubst σ N))

theorem subst_applySubst_gen : ∀ (M : Term) (j : Nat) (σ : Subst) (N : Term),
    substTerm j (shiftTermUp j 0 N) (applySubst (liftSubstN (j + 1) σ) M) =
      applySubst (liftSubstN j (extendSubst σ N)) M := by
  intro M
  induction M with
  | var n =>
    intro j σ N
    simp only [applySubst]
    -- Expand both lifted substitutions at `n`.
    rw [liftSubstN_spec (j := j + 1) (σ := σ) (n := n)]
    rw [liftSubstN_spec (j := j) (σ := extendSubst σ N) (n := n)]
    by_cases hn_lt_j : n < j
    · have hn_lt_j1 : n < j + 1 := Nat.lt_succ_of_lt hn_lt_j
      simp [substTerm, hn_lt_j, hn_lt_j1]
    · have hn_ge_j : j ≤ n := Nat.le_of_not_gt hn_lt_j
      by_cases hn_lt_j1 : n < j + 1
      · -- Then `n = j`.
        have hn_eq_j : n = j := Nat.le_antisymm (Nat.lt_succ_iff.mp hn_lt_j1) hn_ge_j
        subst hn_eq_j
        simp [substTerm, extendSubst]
      · -- Then `n ≥ j+1`.
        have hn_ge_j1 : j + 1 ≤ n := Nat.le_of_not_gt hn_lt_j1
        have hn_gt_j : j < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hn_ge_j1
        have hsub : n - j = (n - (j + 1)) + 1 := by omega
        -- Reduce `extendSubst` on a positive index.
        have hExt : extendSubst σ N (n - j) = σ (n - (j + 1)) := by
          rw [hsub]
          simp [extendSubst]
        rw [hExt]
        -- Cancel the extra shift introduced by `liftSubstN (j+1)`.
        let X := σ (n - (j + 1))
        have hdecomp : shiftTermUp (j + 1) 0 X = shiftTermUp 1 j (shiftTermUp j 0 X) := by
          simpa using (shiftTermUp_succ_shiftTermUp (j := j) (c := 0) X).symm
        -- `substTerm` cancels the innermost shift.
        simpa [substTerm, hn_lt_j, hn_lt_j1, hdecomp, X] using
          (substTerm_shiftTermUp_cancel (k := j) (N := shiftTermUp j 0 N) (M := shiftTermUp j 0 X))
  | lam τ M ih =>
    intro j σ N
    simp [applySubst, substTerm]
    -- Under a binder, increment `j` and lift substitutions.
    have hshift : shiftTermUp 1 0 (shiftTermUp j 0 N) = shiftTermUp (j + 1) 0 N := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (shiftTermUp_add (d₁ := 1) (d₂ := j) (c := 0) N)
    -- Apply IH at `j+1`.
    -- Note: `liftSubst (liftSubstN (j+1) σ) = liftSubstN (j+2) σ` by definition.
    simpa [hshift, liftSubstN, Nat.add_assoc] using ih (j := j + 1) (σ := σ) (N := N)
  | app M N ihM ihN =>
    intro j σ P
    simp [applySubst, substTerm, ihM (j := j) (σ := σ) (N := P), ihN (j := j) (σ := σ) (N := P)]
  | tlam M ih =>
    intro j σ N
    simp [applySubst, substTerm]
    -- Commute the type shift through the term shift.
    have hShiftN : shiftTypeInTerm 1 0 (shiftTermUp j 0 N) = shiftTermUp j 0 (shiftTypeInTerm 1 0 N) := by
      simpa using (shiftTypeInTerm_shiftTermUp_comm (d := 1) (c := 0) (d' := j) (c' := 0) N)
    -- Apply IH in the shifted type-variable world.
    simpa [hShiftN, tshiftSubst_liftSubstN_comm, tshiftSubst_extendSubst_comm,
      tshiftSubst_liftSubstN_extendSubst_comm] using
      ih (j := j) (σ := tshiftSubst σ) (N := shiftTypeInTerm 1 0 N)
  | tapp M τ ih =>
    intro j σ N
    simp [applySubst, substTerm, ih (j := j) (σ := σ) (N := N)]

theorem substTerm0_applySubst_lift (σ : Subst) (N : Term) :
    ∀ M : Term, substTerm0 N (applySubst (liftSubst σ) M) = applySubst (extendSubst σ N) M := by
  intro M
  simpa [substTerm0, liftSubstN, shiftTermUp_zero] using
    (subst_applySubst_gen M 0 σ N)

/-- applySubst preserves term-structure equivalence.
    If M ≈ₜ N (same structure, possibly different type annotations),
    then applySubst σ M ≈ₜ applySubst σ N.
    This is because TermStructEq.var requires the SAME variable index. -/
theorem applySubst_TermStructEq {M N : Term} (σ : Subst) (h : M ≈ₜ N) :
    applySubst σ M ≈ₜ applySubst σ N := by
  induction h generalizing σ with
  | var n => simp [applySubst]; exact TermStructEq.refl (σ n)
  | lam τ₁ τ₂ M₁ M₂ _ ih =>
    simp [applySubst]; exact TermStructEq.lam _ _ _ _ (ih (liftSubst σ))
  | app M₁ M₂ N₁ N₂ _ _ ihM ihN =>
    simp [applySubst]; exact TermStructEq.app _ _ _ _ (ihM σ) (ihN σ)
  | tlam M₁ M₂ _ ih =>
    simp [applySubst]; exact TermStructEq.tlam _ _ (ih (tshiftSubst σ))
  | tapp M₁ M₂ τ₁ τ₂ _ ih =>
    simp [applySubst]; exact TermStructEq.tapp _ _ _ _ (ih σ)

/-- applySubst preserves term-structure equivalence when substitutions are pointwise TermStructEq. -/
theorem applySubst_TermStructEq_subst {σ₁ σ₂ : Subst} (h : ∀ n, σ₁ n ≈ₜ σ₂ n) (M : Term) :
    applySubst σ₁ M ≈ₜ applySubst σ₂ M := by
  induction M generalizing σ₁ σ₂ with
  | var n => simp [applySubst]; exact h n
  | lam τ M ih =>
    simp [applySubst]; apply TermStructEq.lam
    apply ih
    intro n
    cases n with
    | zero => simp [liftSubst]; exact TermStructEq.refl _
    | succ n =>
      simp [liftSubst]
      exact substTerm_TermStructEq.shiftTermUp_TermStructEq 1 0 (h n)
  | app M N ihM ihN =>
    simp [applySubst]; exact TermStructEq.app _ _ _ _ (ihM h) (ihN h)
  | tlam M ih =>
    simp [applySubst]; apply TermStructEq.tlam
    apply ih
    intro n
    simp only [tshiftSubst]
    exact shiftTypeInTerm_TermStructEq_early 1 0 (h n)
  | tapp M τ ih =>
    simp [applySubst]; exact TermStructEq.tapp _ _ _ _ (ih h)

/-! ## Shifting and Parallel Substitution -/

private def shiftSubst (d c : Nat) (σ : Subst) : Subst :=
  fun n => shiftTypeInTerm d c (σ n)

private theorem shiftSubst_liftSubst_comm (d c : Nat) (σ : Subst) :
    shiftSubst d c (liftSubst σ) = liftSubst (shiftSubst d c σ) := by
  funext n
  cases n with
  | zero =>
    simp [shiftSubst, liftSubst, shiftTypeInTerm]
  | succ n =>
    simp [shiftSubst, liftSubst]
    simpa using (shiftTypeInTerm_shiftTermUp_comm (d := d) (c := c) (d' := 1) (c' := 0) (σ n))

private theorem shiftSubst_tshiftSubst_comm (d c : Nat) (σ : Subst) :
    shiftSubst d (c + 1) (tshiftSubst σ) = tshiftSubst (shiftSubst d c σ) := by
  funext n
  -- Use commutation: shift (c+1) after tshift equals tshift after shift c.
  simpa [shiftSubst, tshiftSubst] using
    (shiftTypeInTerm_comm_succ d (b := 0) (c := c) (Nat.zero_le c) (σ n))

theorem shiftTypeInTerm_applySubst (d c : Nat) (σ : Subst) :
    ∀ M : Term,
      shiftTypeInTerm d c (applySubst σ M) =
        applySubst (shiftSubst d c σ) (shiftTypeInTerm d c M) := by
  intro M
  induction M generalizing c σ with
  | var n =>
    simp [applySubst, shiftSubst, shiftTypeInTerm]
  | lam τ M ih =>
    simp [applySubst, shiftTypeInTerm, ih (σ := liftSubst σ) (c := c)]
    -- Align the lifted substitutions.
    simp [shiftSubst_liftSubst_comm]
  | app M N ihM ihN =>
    simp [applySubst, shiftTypeInTerm, ihM (σ := σ) (c := c), ihN (σ := σ) (c := c)]
  | tlam M ih =>
    simp [applySubst, shiftTypeInTerm, ih (σ := tshiftSubst σ) (c := c + 1)]
    -- Align the type-shifted substitutions under the binder.
    simp [shiftSubst_tshiftSubst_comm]
  | tapp M τ ih =>
    simp [applySubst, shiftTypeInTerm, ih (σ := σ) (c := c)]

/-! ## Reducible Substitutions -/

def RedSubst (k : Nat) (ρ : TyEnv) (Γ : Context) (σ : Subst) : Prop :=
  ∀ n τ, lookup Γ n = some τ → Red k ρ τ (σ n)

theorem extendSubst_red {k : Nat} {ρ : TyEnv} {Γ : Context} {σ : Subst} {N : Term} {A : Ty} :
    RedSubst k ρ Γ σ → Red k ρ A N → RedSubst k ρ (A :: Γ) (extendSubst σ N) := by
  intro hσ hN n τ hlook
  cases n with
  | zero =>
    simp [lookup] at hlook
    subst hlook
    simpa [extendSubst] using hN
  | succ n =>
    have hlook' : lookup Γ n = some τ := by
      simpa [lookup] using hlook
    simpa [extendSubst] using hσ n τ hlook'

/-! ## Basic Reducible Terms/Substitutions -/

theorem red_var {k : Nat} {ρ : TyEnv} {A : Ty} (n : Nat) : Red k ρ A (var n) := by
  have hProps : CR_Props k ρ A := cr_props_all k ρ A
  -- Use CR3 on a neutral term with no reducts.
  exact hProps.2 (var n) (by intro N hstep; cases hstep) (neutral_var n)

theorem idSubst_red {k : Nat} {ρ : TyEnv} {Γ : Context} : RedSubst k ρ Γ idSubst := by
  intro n τ hlook
  simpa [idSubst] using (red_var (k := k) (ρ := ρ) (A := τ) n)

theorem shiftTermUp_substTypeInTerm (d c k : Nat) (σ : Ty) (M : Term) :
    shiftTermUp d c (substTypeInTerm k σ M) = substTypeInTerm k σ (shiftTermUp d c M) := by
  induction M generalizing c k σ with
  | var n =>
    simp [shiftTermUp, substTypeInTerm]
    by_cases hnc : n < c
    · simp [substTypeInTerm, hnc]
    · simp [substTypeInTerm, hnc]
  | lam τ M ih =>
    simp [shiftTermUp, substTypeInTerm, ih (c := c+1)]
  | app M N ihM ihN =>
    simp [shiftTermUp, substTypeInTerm, ihM, ihN]
  | tlam M ih =>
    simp [shiftTermUp, substTypeInTerm, ih]
  | tapp M τ ih =>
    simp [shiftTermUp, substTypeInTerm, ih]

theorem shiftTermUp_substTypeInTerm0 (d c : Nat) (τ : Ty) (M : Term) :
    shiftTermUp d c (substTypeInTerm0 τ M) = substTypeInTerm0 τ (shiftTermUp d c M) := by
  simp [substTypeInTerm0]
  rw [shiftTermUp_substTypeInTerm]

theorem shiftTermUp_strongStep {M N : Term} (d c : Nat) (h : M ⟶ₛ N) :
    shiftTermUp d c M ⟶ₛ shiftTermUp d c N := by
  induction h generalizing d c with
  | beta τ M N =>
    simp [shiftTermUp]
    rw [shiftTermUp_substTerm0]
    apply StrongStep.beta
  | tbeta M τ =>
    simp [shiftTermUp]
    rw [shiftTermUp_substTypeInTerm0]
    apply StrongStep.tbeta
  | lam h ih =>
    simp [shiftTermUp]
    apply StrongStep.lam
    exact ih d (c + 1)
  | appL h ih =>
    simp [shiftTermUp]
    apply StrongStep.appL
    exact ih d c
  | appR h ih =>
    simp [shiftTermUp]
    apply StrongStep.appR
    exact ih d c
  | tlam h ih =>
    simp [shiftTermUp]
    apply StrongStep.tlam
    exact ih d c
  | tappL h ih =>
    simp [shiftTermUp]
    apply StrongStep.tappL
    exact ih d c

theorem neutral_shiftTermUp (d c : Nat) {M : Term} (h : IsNeutral M) : IsNeutral (shiftTermUp d c M) := by
  induction M generalizing c with
  | var n =>
    simp only [shiftTermUp]
    split <;> simp [IsNeutral]
  | app M N ihM ihN => simp [shiftTermUp, IsNeutral]
  | tapp M τ ih => simp [shiftTermUp, IsNeutral]
  | lam τ M => simp [IsNeutral] at h
  | tlam M => simp [IsNeutral] at h

/-- If shiftTermUp d c M = lam τ body, then M must be lam τ body' for some body'
    with body = shiftTermUp d (c+1) body'. -/
theorem lam_of_shiftTermUp_eq_lam {d c : Nat} {M : Term} {τ : Ty} {body : Term}
    (h : shiftTermUp d c M = lam τ body) :
    ∃ body', M = lam τ body' ∧ body = shiftTermUp d (c + 1) body' := by
  cases M with
  | var n =>
    simp only [shiftTermUp] at h
    split at h <;> cases h
  | lam τ' body' =>
    simp only [shiftTermUp, Term.lam.injEq] at h
    exact ⟨body', ⟨congrArg (lam · _) h.1, h.2.symm⟩⟩
  | app M' N' => simp only [shiftTermUp] at h; cases h
  | tlam M' => simp only [shiftTermUp] at h; cases h
  | tapp M' τ' => simp only [shiftTermUp] at h; cases h

/-! ## Type-Environment Renaming -/

/-- Insert a new type-variable interpretation at de Bruijn index `c`. -/
def insertTyEnv (c : Nat) (ρ : TyEnv) (R : Candidate) : TyEnv :=
  fun n =>
    if n < c then ρ n
    else if n = c then R
    else ρ (n - 1)

theorem insertTyEnv_zero (ρ : TyEnv) (R : Candidate) : insertTyEnv 0 ρ R = extendTyEnv ρ R := by
  funext n
  cases n with
  | zero => simp [insertTyEnv, extendTyEnv]
  | succ n => simp [insertTyEnv, extendTyEnv]

theorem extendTyEnv_insertTyEnv_comm (c : Nat) (ρ : TyEnv) (R S : Candidate) :
    extendTyEnv (insertTyEnv c ρ R) S = insertTyEnv (c + 1) (extendTyEnv ρ S) R := by
  funext n
  cases n with
  | zero =>
    simp [extendTyEnv, insertTyEnv]
  | succ n =>
    by_cases hn : n < c
    · -- Then `n+1 < c+1`, and both sides pick out `ρ n`.
      have hn' : n + 1 < c + 1 := Nat.succ_lt_succ hn
      have hne : n + 1 ≠ c + 1 := by omega
      simp [extendTyEnv, insertTyEnv, hn, hn']
    · by_cases hEq : n = c
      · -- The inserted candidate.
        subst hEq
        simp [extendTyEnv, insertTyEnv, hn]
      · -- The shifted tail.
        have hn' : ¬n + 1 < c + 1 := by
          simpa [Nat.succ_lt_succ_iff] using hn
        have hne' : n + 1 ≠ c + 1 := by omega
        -- Here `n ≠ 0` (otherwise `c = 0` and we'd have `n = c`).
        cases n with
        | zero =>
          have hc0 : c = 0 := Nat.eq_zero_of_not_pos hn
          subst hc0
          cases hEq rfl
        | succ n =>
          simp [extendTyEnv, insertTyEnv, hn, hEq, hn']

theorem red_insertTyEnv_shiftTyUp_iff (c : Nat) (ρ : TyEnv) (R : Candidate) :
    ∀ {k : Nat} {A : Ty} {M : Term},
      Red k (insertTyEnv c ρ R) (shiftTyUp 1 c A) M ↔ Red k ρ A M := by
  intro k A
  induction A generalizing c ρ k with
  | tvar n =>
    intro M
    by_cases hn : n < c
    · -- No shift on the type index.
      simp [Red, Ty.shiftTyUp, insertTyEnv, hn]
    · -- Shifted type index, and insertion cancels the shift.
      have hn' : ¬n + 1 < c := by
        have : c ≤ n := Nat.le_of_not_gt hn
        exact Nat.not_lt.mpr (Nat.le_trans this (Nat.le_add_right n 1))
      have hne : n + 1 ≠ c := by omega
      simp [Red, Ty.shiftTyUp, insertTyEnv, hn, hn', hne]
  | arr A B ihA ihB =>
    intro M
    constructor
    · intro h k' hk N hN
      have hN' : Red k' (insertTyEnv c ρ R) (shiftTyUp 1 c A) N :=
        (ihA (c := c) (ρ := ρ) (k := k') (M := N)).2 hN
      have hApp :
          Red k' (insertTyEnv c ρ R) (shiftTyUp 1 c B)
            (app (shiftTypeInTerm (k' - k) 0 M) N) :=
        h k' hk N hN'
      exact
        (ihB (c := c) (ρ := ρ) (k := k') (M := app (shiftTypeInTerm (k' - k) 0 M) N)).1 hApp
    · intro h k' hk N hN
      have hN' : Red k' ρ A N :=
        (ihA (c := c) (ρ := ρ) (k := k') (M := N)).1 hN
      have hApp : Red k' ρ B (app (shiftTypeInTerm (k' - k) 0 M) N) :=
        h k' hk N hN'
      exact
        (ihB (c := c) (ρ := ρ) (k := k') (M := app (shiftTypeInTerm (k' - k) 0 M) N)).2 hApp
  | all A ih =>
    intro M
    constructor
    · intro h k' hk S
      have hBody :
          Red (k' + 1) (extendTyEnv (insertTyEnv c ρ R) S) (shiftTyUp 1 (c + 1) A)
            (tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0)) :=
        h k' hk S
      have hEnv :
          extendTyEnv (insertTyEnv c ρ R) S = insertTyEnv (c + 1) (extendTyEnv ρ S) R :=
        extendTyEnv_insertTyEnv_comm (c := c) (ρ := ρ) (R := R) (S := S)
      have hBody' :
          Red (k' + 1) (insertTyEnv (c + 1) (extendTyEnv ρ S) R) (shiftTyUp 1 (c + 1) A)
            (tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0)) := by
        simpa [hEnv] using hBody
      -- Switch to the unshifted world using the IH under the binder.
      exact
        (ih (c := c + 1) (ρ := extendTyEnv ρ S) (k := k' + 1)
          (M := tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0))).1 hBody'
    · intro h k' hk S
      have hBody :
          Red (k' + 1) (extendTyEnv ρ S) A
            (tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0)) :=
        h k' hk S
      have hEnv :
          extendTyEnv (insertTyEnv c ρ R) S = insertTyEnv (c + 1) (extendTyEnv ρ S) R :=
        extendTyEnv_insertTyEnv_comm (c := c) (ρ := ρ) (R := R) (S := S)
      simpa [hEnv] using
        (ih (c := c + 1) (ρ := extendTyEnv ρ S) (k := k' + 1)
          (M := tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0))).2 hBody

/-! ## Fundamental Lemma (Typing ⇒ Reducibility) -/

theorem redSubst_wkN {k k' : Nat} {ρ : TyEnv} {Γ : Context} {σ : Subst}
    (hσ : RedSubst k ρ Γ σ) (hk : k ≤ k') : RedSubst k' ρ Γ (shiftSubst (k' - k) 0 σ) := by
  intro n τ hlook
  have h := hσ n τ hlook
  simpa [shiftSubst] using (red_wkN (k := k) (k' := k') (ρ := ρ) (A := τ) (M := σ n) h hk)

theorem redSubst_shiftContext {k : Nat} {ρ : TyEnv} {Γ : Context} {σ : Subst} (hσ : RedSubst k ρ Γ σ)
    (R : Candidate) : RedSubst (k + 1) (extendTyEnv ρ R) (shiftContext Γ) (tshiftSubst σ) := by
  intro n τ hlook
  induction Γ generalizing n τ σ with
  | nil =>
    simp [shiftContext, lookup] at hlook
  | cons τhd Γ ih =>
    cases n with
    | zero =>
      simp [shiftContext, lookup] at hlook
      -- `τ` is the shifted head type.
      subst hlook
      have hRed : Red k ρ τhd (σ 0) := by
        have : lookup (τhd :: Γ) 0 = some τhd := by simp [lookup]
        simpa using hσ 0 τhd this
      have hRen : Red k (extendTyEnv ρ R) (shiftTyUp 1 0 τhd) (σ 0) := by
        simpa [insertTyEnv_zero] using
          (red_insertTyEnv_shiftTyUp_iff (c := 0) (ρ := ρ) (R := R) (k := k) (A := τhd) (M := σ 0)).2 hRed
      have hWk :
          Red (k + 1) (extendTyEnv ρ R) (shiftTyUp 1 0 τhd) (shiftTypeInTerm 1 0 (σ 0)) := by
        simpa [Nat.add_assoc] using
          (red_wk (k := k) (ρ := extendTyEnv ρ R) (A := shiftTyUp 1 0 τhd) (M := σ 0) hRen)
      simpa [tshiftSubst] using hWk
    | succ n =>
      -- Reduce to the tail context with the shifted substitution.
      have hlook' : lookup (shiftContext Γ) n = some τ := by
        simpa [shiftContext, lookup] using hlook
      let σtail : Subst := fun m => σ (m + 1)
      have hσtail : RedSubst k ρ Γ σtail := by
        intro m τ hm
        have : lookup (τhd :: Γ) (m + 1) = some τ := by
          simpa [lookup] using hm
        simpa [σtail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hσ (m + 1) τ this
      have ih' := ih (σ := σtail) (n := n) (τ := τ) hσtail hlook'
      simpa [tshiftSubst, σtail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih'


/-! ## Semantic Types and Substitution -/

/-- SN is preserved by type application. -/
theorem sn_tapp' {M : Term} (τ : Ty) (h : SN M) : SN (tapp M τ) := by
  induction h with
  | intro M hacc ih =>
    apply sn_intro
    intro N hstep
    cases hstep with
    | tbeta body =>
      -- After matching tbeta body, we know M = tlam body
      -- hacc : ∀ y, (tlam body) ⟶ₛ y → Acc ...
      have hSN_tlamBody : SN (tlam body) := Acc.intro (tlam body) hacc
      have hbody_SN : SN body := sn_tlam_inv hSN_tlamBody
      exact sn_substTypeInTerm 0 τ hbody_SN
    | tappL hM' =>
      exact ih _ hM'

/-- Level-drop with type substitution for reducibility at any type.
    This is the key lemma for SemTy.tySubstLevelDrop.
    The proof uses the tySubstLevelDrop property of candidates in the environment.

    Key insight: Type substitution only changes type annotations, not term structure.
    Since reducibility depends on reduction behavior (which is annotation-independent),
    type-substituted terms have the same reducibility properties.

    Reference: Girard, "Proofs and Types" (1989), Chapter 6. -/
theorem red_level_drop_subst {k : Nat} {ρ : TyEnv} {A : Ty} {M : Term} (σ : Ty)
    (h : Red (k + 1) ρ A M) : Red k ρ A (substTypeInTerm0 σ M) := by
  induction A generalizing k M ρ with
  | tvar n =>
    simp only [Red] at h ⊢
    exact (ρ n).tySubstLevelDrop σ h
  | arr A B ihA ihB =>
    simp only [Red] at h ⊢
    intro k' hk N hN
    -- Goal: Red k' ρ B (app (shiftTypeInTerm (k' - k) 0 (substTypeInTerm0 σ M)) N)
    -- Strategy: use h at level k'+1, then apply ihB to drop the level
    -- 1. Weaken N from level k' to k'+1
    have hN_wk : Red (k' + 1) ρ A (shiftTypeInTerm 1 0 N) := red_wk hN
    -- 2. Apply h at level k'+1 (which is ≥ k+1 since k' ≥ k)
    have hk_succ : k + 1 ≤ k' + 1 := Nat.succ_le_succ hk
    have hIdx : (k' + 1) - (k + 1) = k' - k := by omega
    have hApp : Red (k' + 1) ρ B (app (shiftTypeInTerm (k' - k) 0 M) (shiftTypeInTerm 1 0 N)) := by
      have := h (k' + 1) hk_succ (shiftTypeInTerm 1 0 N) hN_wk
      simp only [hIdx] at this
      exact this
    -- 3. Apply ihB to drop the level
    have hSubst : Red k' ρ B (substTypeInTerm0 σ (app (shiftTypeInTerm (k' - k) 0 M) (shiftTypeInTerm 1 0 N))) :=
      ihB hApp
    -- 4. Simplify: substTypeInTerm0 distributes over app
    simp only [substTypeInTerm] at hSubst
    -- 5. The argument simplifies: substTypeInTerm0 σ (shiftTypeInTerm 1 0 N) = N
    have hArgCancel : substTypeInTerm0 σ (shiftTypeInTerm 1 0 N) = N :=
      substTypeInTerm_shiftTypeInTerm_cancel 0 σ N
    simp only [substTypeInTerm0] at hArgCancel
    rw [hArgCancel] at hSubst
    -- 6. The function: use TermStructEq to relate
    --    substTypeInTerm0 σ (shiftTypeInTerm (k'-k) 0 M) ≈ₜ shiftTypeInTerm (k'-k) 0 (substTypeInTerm0 σ M)
    have hFuncEq : substTypeInTerm0 σ (shiftTypeInTerm (k' - k) 0 M) ≈ₜ
        shiftTypeInTerm (k' - k) 0 (substTypeInTerm0 σ M) := by
      have h1 : shiftTypeInTerm (k' - k) 0 (substTypeInTerm0 σ M) ≈ₜ
          substTypeInTerm0 σ (shiftTypeInTerm (k' - k) 0 M) :=
        shiftSubst_substShift_TermStructEq (k' - k) 0 0 σ M
      exact TermStructEq.symm h1
    have hAppEq : app (substTypeInTerm0 σ (shiftTypeInTerm (k' - k) 0 M)) N ≈ₜ
        app (shiftTypeInTerm (k' - k) 0 (substTypeInTerm0 σ M)) N :=
      TermStructEq.app _ _ _ _ hFuncEq (TermStructEq.refl N)
    exact (Red_TermStructInv B ρ k' _ _ hAppEq).mp hSubst
  | all A ih =>
    simp only [Red] at h ⊢
    intro k' hk R
    -- Goal: Red (k'+1) (extendTyEnv ρ R) A (tapp (shiftTypeInTerm (k'-k) 1 (shiftTypeInTerm 1 0 (substTypeInTerm0 σ M))) (tvar 0))
    -- Strategy: use h at level k'+1, then apply ih to drop the level, and use TermStructEq
    -- 1. Apply h at level k'+1 (which is ≥ k+1 since k' ≥ k)
    have hk_succ : k + 1 ≤ k' + 1 := Nat.succ_le_succ hk
    have hIdx : (k' + 1) - (k + 1) = k' - k := by omega
    have hInst : Red ((k' + 1) + 1) (extendTyEnv ρ R) A
        (tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0)) := by
      have := h (k' + 1) hk_succ R
      simp only [hIdx] at this
      exact this
    -- 2. Apply ih at the extended environment to drop the level
    have hSubst : Red (k' + 1) (extendTyEnv ρ R) A
        (substTypeInTerm0 σ (tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0))) :=
      ih hInst
    -- 3. Simplify the substituted term
    --    substTypeInTerm0 σ (tapp X (tvar 0)) = tapp (substTypeInTerm0 σ X) (substTy0 σ (tvar 0))
    --    = tapp (substTypeInTerm0 σ X) σ
    simp only [substTypeInTerm, Ty.substTy] at hSubst
    -- 4. Use TermStructEq: the two terms have the same structure
    --    tapp (substTypeInTerm0 σ (shiftTypeInTerm (k'-k) 1 (shiftTypeInTerm 1 0 M))) σ
    --    ≈ₜ tapp (shiftTypeInTerm (k'-k) 1 (shiftTypeInTerm 1 0 (substTypeInTerm0 σ M))) (tvar 0)
    have hTermEq : tapp (substTypeInTerm0 σ (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M))) σ ≈ₜ
        tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 (substTypeInTerm0 σ M))) (tvar 0) := by
      -- Both inner terms are ≈ₜ to M (by shiftTypeInTerm and substTypeInTerm preserving structure)
      have h1 : substTypeInTerm0 σ (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) ≈ₜ M := by
        exact TermStructEq.trans (substTypeInTerm_TermStructEq 0 σ _)
          (TermStructEq.trans (shiftTypeInTerm_TermStructEq (k' - k) 1 _)
            (shiftTypeInTerm_TermStructEq 1 0 M))
      have h2 : shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 (substTypeInTerm0 σ M)) ≈ₜ M := by
        exact TermStructEq.trans (shiftTypeInTerm_TermStructEq (k' - k) 1 _)
          (TermStructEq.trans (shiftTypeInTerm_TermStructEq 1 0 _)
            (substTypeInTerm_TermStructEq 0 σ M))
      exact TermStructEq.tapp _ _ σ (tvar 0) (TermStructEq.trans h1 (TermStructEq.symm h2))
    exact (Red_TermStructInv A (extendTyEnv ρ R) (k' + 1) _ _ hTermEq).mp hSubst

/-- Turn a type into a semantic candidate. -/
def SemTy (ρ : TyEnv) (τ : Ty) : Candidate where
  pred k M := Red k ρ τ M
  cr1 := fun {k} {M} h => (cr_props_all k ρ τ).1 M h
  cr2 := red_cr2 (ρ := ρ) (A := τ)
  cr3 := fun {k} {M} hneut hred => (cr_props_all k ρ τ).2 M hred hneut   
  wk h := red_wk (ρ := ρ) (A := τ) h
  tySubstLevelDrop σ h := red_level_drop_subst σ h
  termStructInv h := Red_TermStructInv τ ρ _ _ _ h

/-- SemTy is stable under environment extension + type shifting.
    This is the key property for the `all` case in red_subst_ty_ext. -/
theorem SemTy_shift_equiv (ρ : TyEnv) (R : Candidate) (τ : Ty) :
    ∀ k M, (SemTy ρ τ).pred k M ↔ (SemTy (extendTyEnv ρ R) (shiftTyUp 1 0 τ)).pred k M := by
  intro k M
  simp only [SemTy]
  rw [← insertTyEnv_zero ρ R]
  exact (red_insertTyEnv_shiftTyUp_iff 0 ρ R).symm

theorem red_env_congr {k A M} {ρ₁ ρ₂ : TyEnv}
    (h : ∀ n k' M', (ρ₁ n).pred k' M' ↔ (ρ₂ n).pred k' M') :
    Red k ρ₁ A M ↔ Red k ρ₂ A M := by
  induction A generalizing k M ρ₁ ρ₂ with
  | tvar n => exact h n k M
  | arr A B ihA ihB =>
    simp only [Red]
    constructor
    · intro hRed k' hk N hN
      have hN' := (ihA h).mpr hN
      exact (ihB h).mp (hRed k' hk N hN')
    · intro hRed k' hk N hN
      have hN' := (ihA h).mp hN
      exact (ihB h).mpr (hRed k' hk N hN')
  | all A ih =>
    simp only [Red]
    constructor
    · intro hRed k' hk R
      have henv : ∀ n k' M', (extendTyEnv ρ₁ R n).pred k' M' ↔ (extendTyEnv ρ₂ R n).pred k' M' := by
        intro n k' M'
        cases n with
        | zero => simp [extendTyEnv]
        | succ n => simp [extendTyEnv, h n k' M']
      exact (ih henv).mp (hRed k' hk R)
    · intro hRed k' hk R
      have henv : ∀ n k' M', (extendTyEnv ρ₁ R n).pred k' M' ↔ (extendTyEnv ρ₂ R n).pred k' M' := by
        intro n k' M'
        cases n with
        | zero => simp [extendTyEnv]
        | succ n => simp [extendTyEnv, h n k' M']
      exact (ih henv).mpr (hRed k' hk R)

/-- SemTy at two levels of shifting: SemTy ρ τ ↔ SemTy (ext (ext ρ R) S) (shift 2 0 τ). -/
theorem SemTy_shift2_equiv (ρ : TyEnv) (R S : Candidate) (τ : Ty) :
    ∀ k M, (SemTy ρ τ).pred k M ↔ (SemTy (extendTyEnv (extendTyEnv ρ R) S) (shiftTyUp 2 0 τ)).pred k M := by
  intro k M
  have h1 := SemTy_shift_equiv ρ R τ k M
  have h2 := SemTy_shift_equiv (extendTyEnv ρ R) S (shiftTyUp 1 0 τ) k M
  have hcomp : shiftTyUp 1 0 (shiftTyUp 1 0 τ) = shiftTyUp 2 0 τ := Ty.shiftTyUp_add 1 1 0 τ
  calc (SemTy ρ τ).pred k M
      ↔ (SemTy (extendTyEnv ρ R) (shiftTyUp 1 0 τ)).pred k M := h1
    _ ↔ (SemTy (extendTyEnv (extendTyEnv ρ R) S) (shiftTyUp 1 0 (shiftTyUp 1 0 τ))).pred k M := h2
    _ ↔ (SemTy (extendTyEnv (extendTyEnv ρ R) S) (shiftTyUp 2 0 τ)).pred k M := by rw [hcomp]

/-- Shifting by d at cutoff c makes Red depend only on type variables with index ≥ c.
    The key insight: shiftTyUp d c τ shifts indices ≥ c up by d, so Red looks them up
    at positions ≥ c+d in ρ. If ρ agrees with ρbase from position d onwards (for indices ≥ c),
    then the Red values match. -/
theorem red_shift_skip (d c : Nat) {k : Nat} {τ : Ty} {M : Term} {ρ ρbase : TyEnv}
    -- ρ agrees with ρbase for positions < c, and ρ(n+d) = ρbase(n) for n ≥ c
    (hlt : ∀ n, n < c → ρ n = ρbase n)
    (hge : ∀ n, c ≤ n → ρ (n + d) = ρbase n) :
    Red k ρ (shiftTyUp d c τ) M ↔ Red k ρbase τ M := by
  induction τ generalizing d c k M ρ ρbase with
  | tvar n =>
    by_cases hnc : n < c
    · -- n < c: shiftTyUp d c (tvar n) = tvar n (unchanged)
      simp only [Ty.shiftTyUp, hnc, ↓reduceIte, Red]
      have := hlt n hnc
      rw [this]
    · -- n ≥ c: shiftTyUp d c (tvar n) = tvar (n + d)
      simp only [Ty.shiftTyUp, hnc, ↓reduceIte, Red]
      have := hge n (Nat.le_of_not_lt hnc)
      rw [this]
  | arr A B ihA ihB =>
    simp only [Ty.shiftTyUp, Red]
    constructor
    · intro h k' hk N hN
      -- The term in Red for arr is: app (shiftTypeInTerm (k' - k) 0 M) N
      have hN' := (ihA d c (k := k') (M := N) hlt hge).mpr hN
      have hApp := h k' hk N hN'
      exact (ihB d c (k := k') (M := app (shiftTypeInTerm (k' - k) 0 M) N) hlt hge).mp hApp
    · intro h k' hk N hN
      have hN' := (ihA d c (k := k') (M := N) hlt hge).mp hN
      have hApp := h k' hk N hN'
      exact (ihB d c (k := k') (M := app (shiftTypeInTerm (k' - k) 0 M) N) hlt hge).mpr hApp
  | all A ih =>
    simp only [Ty.shiftTyUp, Red]
    -- Under a binder, the cutoff increases by 1
    -- For Red at (all A), the term is: tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0)
    constructor
    · intro h k' hk R
      have hlt' : ∀ n, n < c + 1 → (extendTyEnv ρ R) n = (extendTyEnv ρbase R) n := by
        intro n hnc1
        cases n with
        | zero => simp [extendTyEnv]
        | succ n =>
          simp only [extendTyEnv]
          exact hlt n (Nat.lt_of_succ_lt_succ hnc1)
      have hge' : ∀ n, c + 1 ≤ n → (extendTyEnv ρ R) (n + d) = (extendTyEnv ρbase R) n := by
        intro n hnc1
        cases n with
        | zero => omega
        | succ m =>
          have heq1 : m + 1 + d = (m + d) + 1 := by omega
          have heq2 : (extendTyEnv ρ R) ((m + d) + 1) = ρ (m + d) := rfl
          have heq3 : (extendTyEnv ρbase R) (m + 1) = ρbase m := rfl
          rw [heq1, heq2, heq3]
          exact hge m (Nat.le_of_succ_le_succ hnc1)
      exact (ih d (c + 1) (k := k' + 1)
        (M := tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0))
        (ρ := extendTyEnv ρ R) (ρbase := extendTyEnv ρbase R) hlt' hge').mp (h k' hk R)
    · intro h k' hk R
      have hlt' : ∀ n, n < c + 1 → (extendTyEnv ρ R) n = (extendTyEnv ρbase R) n := by
        intro n hnc1
        cases n with
        | zero => simp [extendTyEnv]
        | succ n =>
          simp only [extendTyEnv]
          exact hlt n (Nat.lt_of_succ_lt_succ hnc1)
      have hge' : ∀ n, c + 1 ≤ n → (extendTyEnv ρ R) (n + d) = (extendTyEnv ρbase R) n := by
        intro n hnc1
        cases n with
        | zero => omega
        | succ m =>
          have heq1 : m + 1 + d = (m + d) + 1 := by omega
          have heq2 : (extendTyEnv ρ R) ((m + d) + 1) = ρ (m + d) := rfl
          have heq3 : (extendTyEnv ρbase R) (m + 1) = ρbase m := rfl
          rw [heq1, heq2, heq3]
          exact hge m (Nat.le_of_succ_le_succ hnc1)
      exact (ih d (c + 1) (k := k' + 1)
        (M := tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0))
        (ρ := extendTyEnv ρ R) (ρbase := extendTyEnv ρbase R) hlt' hge').mpr (h k' hk R)

/-- Special case of red_shift_skip: shifting by c at cutoff 0 skips c positions in ρ. -/
theorem red_shift_skip_zero (c : Nat) {k : Nat} {τ : Ty} {M : Term} {ρ ρbase : TyEnv}
    (hρ : ∀ n, ρ (n + c) = ρbase n) :
    Red k ρ (shiftTyUp c 0 τ) M ↔ Red k ρbase τ M := by
  apply red_shift_skip c 0
  · intro n hn; omega
  · intro n _; exact hρ n

/-- Generalized helper: substTy at level c relates c-extended env to (c+1)-extended env with SemTy.
    Key: the base environment ρbase and type τ are fixed; we track c extensions on top. -/
theorem red_subst_ty_gen (c : Nat) (ρbase : TyEnv) (τ : Ty) {k : Nat} {A : Ty} {M : Term} {ρ : TyEnv}
    -- ρ is ρbase with c extensions: ρ(n+c) = ρbase(n)
    (hρ : ∀ n, ρ (n + c) = ρbase n) :
    Red k ρ (substTy c (shiftTyUp c 0 τ) A) M ↔
    Red k (insertTyEnv c ρ (SemTy ρbase τ)) A M := by
  induction A generalizing c k M ρ with
  | tvar n =>
    by_cases hnc : n < c
    · -- n < c: substTy doesn't change tvar n; both envs agree at n < c
      simp only [substTy, hnc, ↓reduceIte, Red]
      have hins : insertTyEnv c ρ (SemTy ρbase τ) n = ρ n := by
        simp [insertTyEnv, hnc]
      simp only [hins]
    · by_cases hneq : n = c
      · -- n = c: substTy c gives shiftTyUp c 0 τ; insertTyEnv gives SemTy ρbase τ
        rw [hneq]
        simp only [substTy, Nat.lt_irrefl, ↓reduceIte, Red]
        -- Goal: Red k ρ (shiftTyUp c 0 τ) M ↔ (insertTyEnv c ρ (SemTy ρbase τ) c).pred k M
        have hins : insertTyEnv c ρ (SemTy ρbase τ) c = SemTy ρbase τ := by
          simp [insertTyEnv, Nat.lt_irrefl]
        rw [hins]
        -- Goal: Red k ρ (shiftTyUp c 0 τ) M ↔ (SemTy ρbase τ).pred k M
        -- By definition: (SemTy ρbase τ).pred k M = Red k ρbase τ M
        simp only [SemTy]
        -- Goal: Red k ρ (shiftTyUp c 0 τ) M ↔ Red k ρbase τ M
        exact red_shift_skip_zero c hρ
      · -- n > c: substTy c gives tvar (n-1); insertTyEnv shifts indices > c
        have hngt : c < n := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hnc) (Ne.symm hneq)
        simp only [substTy, hnc, hneq, ↓reduceIte, Red]
        have hins : insertTyEnv c ρ (SemTy ρbase τ) n = ρ (n - 1) := by
          simp only [insertTyEnv]
          have h1 : ¬ n < c := hnc
          have h2 : n ≠ c := hneq
          simp [h1, h2]
        simp only [hins]
  | arr A B ihA ihB =>
    simp only [substTy, Red]
    constructor
    · intro h k' hk N hN
      have hN' := (ihA c (k := k') (M := N) hρ).mpr hN
      exact (ihB c (k := k') (M := app (shiftTypeInTerm (k' - k) 0 M) N) hρ).mp (h k' hk N hN')
    · intro h k' hk N hN
      have hN' := (ihA c (k := k') (M := N) hρ).mp hN
      exact (ihB c (k := k') (M := app (shiftTypeInTerm (k' - k) 0 M) N) hρ).mpr (h k' hk N hN')
  | all A ih =>
    simp only [substTy, Red]
    -- For all types, the term is: tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0)
    -- substTy c σ (all A) = all (substTy (c+1) (shiftTyUp 1 0 σ) A)
    -- So substTy c (shiftTyUp c 0 τ) (all A) = all (substTy (c+1) (shiftTyUp 1 0 (shiftTyUp c 0 τ)) A)
    --                                       = all (substTy (c+1) (shiftTyUp (c+1) 0 τ) A)
    have hShiftComp : shiftTyUp 1 0 (shiftTyUp c 0 τ) = shiftTyUp (c + 1) 0 τ := by
      rw [Ty.shiftTyUp_add 1 c 0 τ, Nat.add_comm]
    constructor
    · intro h k' hk S
      have hbody := h k' hk S
      rw [hShiftComp] at hbody
      -- Need: ext ρ S with substTy (c+1) ↔ ext (insertTyEnv c ρ (SemTy ρbase τ)) S
      have hρext : ∀ n, (extendTyEnv ρ S) (n + (c + 1)) = ρbase n := by
        intro n
        show ρ (n + c) = ρbase n
        exact hρ n
      have hEnvEq : extendTyEnv (insertTyEnv c ρ (SemTy ρbase τ)) S =
                    insertTyEnv (c + 1) (extendTyEnv ρ S) (SemTy ρbase τ) := by
        funext n
        cases n with
        | zero => simp [extendTyEnv, insertTyEnv]
        | succ n =>
          simp only [extendTyEnv, insertTyEnv, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
          by_cases hn1 : n < c
          · have hn2 : n + 1 < c + 1 := Nat.succ_lt_succ hn1
            have hn3 : n + 1 ≠ c + 1 := by omega
            simp [hn1, hn2]
          · by_cases hneq : n = c
            · simp only [hneq, Nat.lt_irrefl, ↓reduceIte]
            · have hn2 : ¬ n + 1 < c + 1 := by omega
              have hn3 : n + 1 ≠ c + 1 := by omega
              have hnpos : n ≥ 1 := by omega
              simp only [hn1, ↓reduceIte, hneq, hn2, hn3]
              match n, hnpos with
              | n + 1, _ => rfl
      rw [hEnvEq]
      exact (ih (c + 1) (k := k' + 1)
        (M := tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0))
        (ρ := extendTyEnv ρ S) hρext).mp hbody
    · intro h k' hk S
      -- Reverse direction: we have h from the insertTyEnv side, need to prove substTy side
      have hbody := h k' hk S
      have hρext : ∀ n, (extendTyEnv ρ S) (n + (c + 1)) = ρbase n := by
        intro n
        show ρ (n + c) = ρbase n
        exact hρ n
      have hEnvEq : extendTyEnv (insertTyEnv c ρ (SemTy ρbase τ)) S =
                    insertTyEnv (c + 1) (extendTyEnv ρ S) (SemTy ρbase τ) := by
        funext n
        cases n with
        | zero => simp [extendTyEnv, insertTyEnv]
        | succ n =>
          simp only [extendTyEnv, insertTyEnv, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
          by_cases hn1 : n < c
          · have hn2 : n + 1 < c + 1 := Nat.succ_lt_succ hn1
            have hn3 : n + 1 ≠ c + 1 := by omega
            simp [hn1, hn2]
          · by_cases hneq : n = c
            · simp only [hneq, Nat.lt_irrefl, ↓reduceIte]
            · have hn2 : ¬ n + 1 < c + 1 := by omega
              have hn3 : n + 1 ≠ c + 1 := by omega
              have hnpos : n ≥ 1 := by omega
              simp only [hn1, ↓reduceIte, hneq, hn2, hn3]
              -- Goal: ρ (n - 1) = match n with | 0 => S | succ m => ρ m
              -- Since n ≥ 1, n = succ m for some m, so match gives ρ m, and n - 1 = m
              match n, hnpos with
              | n + 1, _ => rfl
      rw [hEnvEq] at hbody
      rw [hShiftComp]
      exact (ih (c + 1) (k := k' + 1)
        (M := tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0))
        (ρ := extendTyEnv ρ S) hρext).mpr hbody

/-- Helper for red_subst_ty: relates substTy 1 with double-extended environment. -/
theorem red_subst_ty_ext {ρ : TyEnv} {τ : Ty} {R : Candidate} :
    ∀ {k : Nat} {A : Ty} {M : Term},
      Red k (extendTyEnv ρ R) (substTy 1 (shiftTyUp 1 0 τ) A) M ↔
      Red k (extendTyEnv (extendTyEnv ρ (SemTy ρ τ)) R) A M := by
  intro k A M
  -- Use red_subst_ty_gen with c = 1, ρbase = ρ
  have hρ : ∀ n, (extendTyEnv ρ R) (n + 1) = ρ n := by
    intro n
    simp [extendTyEnv]
  have hGen := red_subst_ty_gen 1 ρ τ (k := k) (A := A) (M := M) (ρ := extendTyEnv ρ R) hρ
  -- insertTyEnv 1 (extendTyEnv ρ R) (SemTy ρ τ) = extendTyEnv (extendTyEnv ρ (SemTy ρ τ)) R
  have hEnvEq : insertTyEnv 1 (extendTyEnv ρ R) (SemTy ρ τ) =
                extendTyEnv (extendTyEnv ρ (SemTy ρ τ)) R := by
    funext n
    cases n with
    | zero => simp [insertTyEnv, extendTyEnv]
    | succ n =>
      cases n with
      | zero => simp [insertTyEnv, extendTyEnv]
      | succ m => simp [insertTyEnv, extendTyEnv]
  rw [hEnvEq] at hGen
  exact hGen

theorem red_subst_ty :
    ∀ {k : Nat} {ρ : TyEnv} {A : Ty} {τ : Ty} {M : Term},
      Red k ρ (substTy 0 τ A) M ↔ Red k (extendTyEnv ρ (SemTy ρ τ)) A M := by
  intro k ρ A τ M
  induction A generalizing k ρ M with
  | tvar n =>
    cases n with
    | zero =>
      simp only [substTy, Nat.lt_irrefl, ↓reduceIte, Red, extendTyEnv, SemTy]
    | succ n =>
      simp only [substTy, Nat.not_lt_zero, Nat.succ_ne_zero, ↓reduceIte,
                 Red, extendTyEnv, Nat.add_sub_cancel]
  | arr A B ihA ihB =>
    simp only [Red, substTy]
    constructor
    · intro hRed k' hk N hN
      have hN' := ihA.mpr hN
      exact ihB.mp (hRed k' hk N hN')
    · intro hRed k' hk N hN
      have hN' := ihA.mp hN
      exact ihB.mpr (hRed k' hk N hN')
  | all A ih =>
    simp only [Red, substTy]
    -- Use red_subst_ty_ext for the all case
    constructor
    · intro hRed k' hk R
      exact red_subst_ty_ext.mp (hRed k' hk R)
    · intro hRed k' hk R
      exact red_subst_ty_ext.mpr (hRed k' hk R)

theorem red_shift {k : Nat} {ρ : TyEnv} {A : Ty} {M : Term}
    (h : Red k ρ A M) (R : Candidate) :
    Red (k + 1) (extendTyEnv ρ R) (shiftTyUp 1 0 A) (shiftTypeInTerm 1 0 M) := by
  have hRen : Red k (extendTyEnv ρ R) (shiftTyUp 1 0 A) M := by
    simpa [insertTyEnv_zero] using (red_insertTyEnv_shiftTyUp_iff 0 ρ R).2 h
  exact red_wk hRen

/-- General identity: substTy k (tvar k) (shiftTyUp 1 (k+1) τ) = τ. -/
theorem Ty.substTy_tvar_shiftTyUp_succ_id (k : Nat) :
    ∀ τ : Ty, substTy k (tvar k) (shiftTyUp 1 (k + 1) τ) = τ := by
  intro τ
  induction τ generalizing k with
  | tvar n =>
    by_cases hnk1 : n < k + 1
    · -- n ≤ k: shift leaves it unchanged, n < k or n = k
      by_cases hnk : n < k
      · simp [shiftTyUp, substTy, hnk1, hnk]
      · -- n = k: shift leaves it, subst replaces with tvar k
        have heq : n = k := Nat.eq_of_lt_succ_of_not_lt hnk1 hnk
        simp [shiftTyUp, substTy, heq]
    · -- n > k: shift makes it n+1, subst decrements back to n
      have hge : k + 1 ≤ n := Nat.le_of_not_gt hnk1
      have hnp1_gtk : ¬ n + 1 < k := by omega
      have hnp1_nek : n + 1 ≠ k := by omega
      simp [shiftTyUp, substTy, hnk1, hnp1_gtk, hnp1_nek]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp [shiftTyUp, substTy, ih₁ k, ih₂ k]
  | all τ ih =>
    simp only [shiftTyUp, substTy]
    -- Under binder: shift at (k+1)+1, subst at k+1 with shiftTyUp 1 0 (tvar k)
    -- shiftTyUp 1 0 (tvar k) = tvar (k + 1) since k >= 0
    simp only [Nat.not_lt_zero, ↓reduceIte]
    -- Now goal is: (substTy (k + 1) (tvar (k + 1)) (shiftTyUp 1 (k + 1 + 1) τ)).all = τ.all
    exact congrArg all (ih (k + 1))

/-- substTy 0 (tvar 0) (shiftTyUp 1 1 τ) = τ: substituting tvar 0 after shift at cutoff 1 is identity. -/
theorem Ty.substTy0_tvar0_shiftTyUp11_id : ∀ τ : Ty, substTy 0 (tvar 0) (shiftTyUp 1 1 τ) = τ :=
  Ty.substTy_tvar_shiftTyUp_succ_id 0

/-- General identity: substTypeInTerm k (tvar k) (shiftTypeInTerm 1 (k+1) M) = M. -/
theorem substTypeInTerm_tvar_shiftTypeInTerm_succ_id (k : Nat) :
    ∀ M : Term, substTypeInTerm k (tvar k) (shiftTypeInTerm 1 (k + 1) M) = M := by
  intro M
  induction M generalizing k with
  | var n =>
    simp [substTypeInTerm, shiftTypeInTerm]
  | lam τ M ih =>
    have hτ := Ty.substTy_tvar_shiftTyUp_succ_id k τ
    simp [substTypeInTerm, shiftTypeInTerm, hτ, ih k]
  | app M N ihM ihN =>
    simp [substTypeInTerm, shiftTypeInTerm, ihM k, ihN k]
  | tlam M ih =>
    simp only [substTypeInTerm, shiftTypeInTerm]
    -- Under tlam: shift at (k+1)+1, subst at k+1 with shiftTyUp 1 0 (tvar k)
    -- shiftTyUp 1 0 (tvar k) = tvar (k + 1) since k >= 0
    simp only [shiftTyUp, Nat.not_lt_zero, ↓reduceIte]
    -- Now goal is: (substTypeInTerm (k + 1) (tvar (k + 1)) (shiftTypeInTerm 1 (k + 1 + 1) M)).tlam = M.tlam
    exact congrArg tlam (ih (k + 1))
  | tapp M τ ihM =>
    have hτ := Ty.substTy_tvar_shiftTyUp_succ_id k τ
    simp [substTypeInTerm, shiftTypeInTerm, hτ, ihM k]

/-- substTypeInTerm 0 (tvar 0) (shiftTypeInTerm 1 1 M) = M: the composition is identity. -/
theorem substTypeInTerm0_tvar0_shiftTypeInTerm11_id :
    ∀ M : Term, substTypeInTerm0 (tvar 0) (shiftTypeInTerm 1 1 M) = M := by
  intro M
  simp [substTypeInTerm0]
  exact substTypeInTerm_tvar_shiftTypeInTerm_succ_id 0 M

/-- SNCandidate pred is level-independent: it doesn't depend on k. -/
theorem SNCandidate_pred_level_indep {k₁ k₂ : Nat} {M : Term} :
    SNCandidate.pred k₁ M ↔ SNCandidate.pred k₂ M := by
  simp only [SNCandidate]

/-- SN is preserved by type substitution (both directions). -/
theorem sn_substTypeInTerm_iff (k : Nat) (σ : Ty) {M : Term} :
    SN M ↔ SN (substTypeInTerm k σ M) :=
  ⟨sn_substTypeInTerm k σ, sn_of_substTypeInTerm k σ⟩

/-- Key semantic lemma: Reducibility at level k+1 in extended env implies reducibility
    of type-substituted term at level k. This is the key property of Kripke-style
    reducibility that handles type variable instantiation.
    Reference: Girard, "Proofs and Types" (1989), Chapter 6, Lemma 6.1.5. -/
theorem red_level_subst_mp {k : Nat} {ρ : TyEnv} {τ : Ty} {A : Ty} {M : Term}
    (h : Red (k + 1) (extendTyEnv ρ (SemTy ρ τ)) A M) :
    Red k (extendTyEnv ρ (SemTy ρ τ)) A (substTypeInTerm0 τ M) := by
  -- Proof by induction on the type A
  let env := extendTyEnv ρ (SemTy ρ τ)
  induction A generalizing k M with
  | tvar n =>
    -- Reducibility at tvar n uses the candidate at position n
    cases n with
    | zero =>
      -- env 0 = SemTy ρ τ, so (env 0).pred k M = Red k ρ τ M
      simp only [Red, extendTyEnv, SemTy] at h ⊢
      -- h : Red (k + 1) ρ τ M
      -- goal : Red k ρ τ (substTypeInTerm0 τ M)
      -- Use red_level_drop_subst at type τ
      exact red_level_drop_subst τ h
    | succ n =>
      -- env (n+1) = ρ n
      simp only [Red, extendTyEnv] at h ⊢
      -- h : (ρ n).pred (k + 1) M
      -- goal : (ρ n).pred k (substTypeInTerm0 τ M)
      -- Use the tySubstLevelDrop property of the candidate at position n
      exact (ρ n).tySubstLevelDrop τ h
  | arr A B ihA ihB =>
    -- Arrow type: need to show shifted application is reducible
    simp only [Red] at h ⊢
    intro k' hk N hN
    -- We need: Red k' env B (app (shiftTypeInTerm (k' - k) 0 (substTypeInTerm0 τ M)) N)
    -- From h: ∀ k'' ≥ k+1, ∀ N' red at A, Red k'' env B (app (shiftTypeInTerm (k'' - (k+1)) 0 M) N')
    -- Apply h at k' + 1 with N shifted appropriately
    have hk'1 : k + 1 ≤ k' + 1 := Nat.succ_le_succ hk
    -- We need N reducible at A in the environment at level k'+1
    -- Since k' ≥ k, N at level k' can be weakened to level k'+1 using red_wk
    have hN_wk : Red (k' + 1) env A (shiftTypeInTerm 1 0 N) := red_wk hN
    have hApp := h (k' + 1) hk'1 (shiftTypeInTerm 1 0 N) hN_wk
    -- hApp : Red (k' + 1) env B (app (shiftTypeInTerm (k' + 1 - (k + 1)) 0 M) (shiftTypeInTerm 1 0 N))
    -- Simplify: k' + 1 - (k + 1) = k' - k
    have hIdx : k' + 1 - (k + 1) = k' - k := by omega
    rw [hIdx] at hApp
    -- Now use IH on B to get result at level k'
    have hB := ihB hApp
    -- hB : Red k' env B (substTypeInTerm0 τ (app (shiftTypeInTerm (k' - k) 0 M) (shiftTypeInTerm 1 0 N)))
    -- Need to simplify the term structure
    simp only [substTypeInTerm0, substTypeInTerm] at hB
    -- The substitution distributes: substTypeInTerm0 τ (app ...) = app (substTypeInTerm0 τ ...) (substTypeInTerm0 τ ...)
    --
    -- We have: Red k' env B (app (substTypeInTerm0 τ (shiftTypeInTerm (k'-k) 0 M)) (substTypeInTerm0 τ (shiftTypeInTerm 1 0 N)))
    -- Need:   Red k' env B (app (shiftTypeInTerm (k'-k) 0 (substTypeInTerm0 τ M)) N)
    --
    -- Step 1: For the argument, use the cancel lemma
    have hArgCancel : substTypeInTerm0 τ (shiftTypeInTerm 1 0 N) = N :=
      substTypeInTerm_shiftTypeInTerm_cancel 0 τ N
    simp only [substTypeInTerm0] at hArgCancel
    rw [hArgCancel] at hB
    -- Step 2: For the function, use TermStructEq
    have hFuncEq : substTypeInTerm0 τ (shiftTypeInTerm (k' - k) 0 M) ≈ₜ
        shiftTypeInTerm (k' - k) 0 (substTypeInTerm0 τ M) := by
      have h1 : shiftTypeInTerm (k' - k) 0 (substTypeInTerm0 τ M) ≈ₜ
          substTypeInTerm0 τ (shiftTypeInTerm (k' - k) 0 M) :=
        shiftSubst_substShift_TermStructEq (k' - k) 0 0 τ M
      exact TermStructEq.symm h1
    have hAppEq : app (substTypeInTerm0 τ (shiftTypeInTerm (k' - k) 0 M)) N ≈ₜ
        app (shiftTypeInTerm (k' - k) 0 (substTypeInTerm0 τ M)) N :=
      TermStructEq.app _ _ _ _ hFuncEq (TermStructEq.refl N)
    exact (Red_TermStructInv B env k' _ _ hAppEq).mp hB
  | all A ih =>
    -- Universal type: Red k ρ (all A) M means ∀ k' ≥ k, ∀ R, Red (k'+1) (ρ,R) A (instFresh ...)
    simp only [Red] at h ⊢
    intro k' hk R
    -- Goal: Red (k'+1) (extendTyEnv env R) A (tapp (shiftTypeInTerm (k'-k) 1 (shiftTypeInTerm 1 0 (substTypeInTerm0 τ M))) (tvar 0))
    -- Strategy: use h at k'+1, apply red_level_drop_subst (not ih) to drop level, use TermStructEq
    -- 1. Apply h at k'' = k'+1 with R' = R
    have hk_succ : k + 1 ≤ k' + 1 := Nat.succ_le_succ hk
    have hIdx : (k' + 1) - (k + 1) = k' - k := by omega
    have hInst : Red ((k' + 1) + 1) (extendTyEnv env R) A
        (tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0)) := by
      have := h (k' + 1) hk_succ R
      simp only [hIdx] at this
      exact this
    -- 2. Apply red_level_drop_subst at the extended environment to drop the level
    --    Note: we use red_level_drop_subst which generalizes over ρ, not the IH which doesn't
    have hSubst : Red (k' + 1) (extendTyEnv env R) A
        (substTypeInTerm0 τ (tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) (tvar 0))) :=
      red_level_drop_subst τ hInst
    -- 3. Simplify the substituted term
    simp only [substTypeInTerm, Ty.substTy] at hSubst
    -- 4. Use TermStructEq: both terms have the same structure (related to M)
    have hTermEq : tapp (substTypeInTerm0 τ (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M))) τ ≈ₜ
        tapp (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 (substTypeInTerm0 τ M))) (tvar 0) := by
      have h1 : substTypeInTerm0 τ (shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 M)) ≈ₜ M := by
        exact TermStructEq.trans (substTypeInTerm_TermStructEq 0 τ _)
          (TermStructEq.trans (shiftTypeInTerm_TermStructEq (k' - k) 1 _)
            (shiftTypeInTerm_TermStructEq 1 0 M))
      have h2 : shiftTypeInTerm (k' - k) 1 (shiftTypeInTerm 1 0 (substTypeInTerm0 τ M)) ≈ₜ M := by
        exact TermStructEq.trans (shiftTypeInTerm_TermStructEq (k' - k) 1 _)
          (TermStructEq.trans (shiftTypeInTerm_TermStructEq 1 0 _)
            (substTypeInTerm_TermStructEq 0 τ M))
      exact TermStructEq.tapp _ _ τ (tvar 0) (TermStructEq.trans h1 (TermStructEq.symm h2))
    exact (Red_TermStructInv A (extendTyEnv env R) (k' + 1) _ _ hTermEq).mp hSubst

/-- Alias for red_level_subst_mp using Iff syntax for compatibility. -/
theorem red_level_subst {k : Nat} {ρ : TyEnv} {τ : Ty} {A : Ty} {M : Term} :
    Red (k + 1) (extendTyEnv ρ (SemTy ρ τ)) A M →
    Red k (extendTyEnv ρ (SemTy ρ τ)) A (substTypeInTerm0 τ M) :=
  red_level_subst_mp

theorem red_tapp {k : Nat} {ρ : TyEnv} {A : Ty} {M : Term}
    (h : Red k ρ (all A) M) (τ : Ty) :
    Red k ρ (substTy0 τ A) (tapp M τ) := by
  have hSN : SN M := (cr_props_all k ρ (all A)).1 M h
  rw [red_subst_ty]
  let env := extendTyEnv ρ (SemTy ρ τ)
  have hCR := cr_props_all k env A
  induction hSN with
  | intro M hM ih =>
    cases M with
    | tlam body =>
      apply hCR.2 (tapp (tlam body) τ)
      · intro P hstep
        cases hstep with
        | tbeta body' τ' =>
          have hInst := h k (Nat.le_refl k) (SemTy ρ τ)
          simp only [Nat.sub_self, shiftTypeInTerm_zero] at hInst
          have hbody_eq : substTypeInTerm0 (tvar 0) (shiftTypeInTerm 1 1 body) = body :=
            substTypeInTerm0_tvar0_shiftTypeInTerm11_id body
          have hbeta : tapp (tlam (shiftTypeInTerm 1 1 body)) (tvar 0) ⟶ₛ
              substTypeInTerm0 (tvar 0) (shiftTypeInTerm 1 1 body) :=
            StrongStep.tbeta (shiftTypeInTerm 1 1 body) (tvar 0)
          have hbody_red : Red (k + 1) env A body := by
            rw [← hbody_eq]
            exact red_cr2 hInst hbeta
          exact red_level_subst hbody_red
        | tappL hstep' =>
          cases hstep' with
          | tlam hbody =>
            rename_i body''
            have hstep_tlam : tlam body ⟶ₛ tlam body'' := StrongStep.tlam hbody
            have h' : Red k ρ (all A) (tlam body'') := red_cr2 h hstep_tlam
            exact ih (tlam body'') hstep_tlam h'
      · simp [IsNeutral]
    | var n =>
      apply hCR.2 (tapp (var n) τ)
      · intro P hstep
        cases hstep with
        | tappL hstep' => cases hstep'
      · simp [IsNeutral]
    | lam τ' body =>
      apply hCR.2 (tapp (lam τ' body) τ)
      · intro P hstep
        cases hstep with
        | tappL hstep' =>
          have h' := red_cr2 h hstep'
          exact ih _ hstep' h'
      · simp [IsNeutral]
    | app M' N' =>
      apply hCR.2 (tapp (app M' N') τ)
      · intro P hstep
        cases hstep with
        | tappL hstep' =>
          have h' := red_cr2 h hstep'
          exact ih _ hstep' h'
      · simp [IsNeutral]
    | tapp M' τ' =>
      apply hCR.2 (tapp (tapp M' τ') τ)
      · intro P hstep
        cases hstep with
        | tappL hstep' =>
          have h' := red_cr2 h hstep'
          exact ih _ hstep' h'
      · simp [IsNeutral]

/-- Fundamental Lemma: well-typed terms are reducible under reducible substitutions.
    This is the main semantic lemma of the strong normalization proof.
    The proof uses induction on the typing derivation, with nested SN inductions
    for the lambda and type abstraction cases.
    Reference: Girard, "Proofs and Types" (1989), Chapter 6, Theorem 6.2.1. -/
theorem fundamental_lemma {k : Nat} {Γ : Context} {M : Term} {τ : Ty} (h : HasType k Γ M τ) :
    ∀ {k' : Nat} (_hk : k ≤ k') {ρ : TyEnv} {σ : Subst},
      RedSubst k' ρ Γ σ → Red k' ρ τ (applySubst σ M) := by
  induction h with
  | var hlook =>
    -- Variable case: σ(n) is reducible at τ by the RedSubst hypothesis
    intro k' hk ρ σ hσ
    simp only [applySubst]
    exact hσ _ _ hlook
  | @lam k Γ τ₁ τ₂ body hτ₁_wf hbody ih =>
    -- Lambda case: need to show λx:τ₁. body is reducible at τ₁ ⇒ τ₂
    intro k' hk ρ σ hσ
    simp only [applySubst, Red]
    intro k'' hk' N hN
    -- Goal: Red k'' ρ τ₂ (app (shiftTypeInTerm δ 0 (lam τ₁ body')) N)
    -- where δ = k'' - k' and body' = applySubst (liftSubst σ) body
    let δ := k'' - k'
    let body' := applySubst (liftSubst σ) body
    have hCR := cr_props_all k'' ρ τ₂
    -- Get SN for nested induction
    have hSN_lam : SN (lam τ₁ body') := by
      -- The lambda is SN because its body is SN (from reducibility)
      have hRedSubst' : RedSubst k' ρ (τ₁ :: Γ) (extendSubst σ (var 0)) :=
        extendSubst_red hσ (red_var 0)
      have hBody_Red := ih hk hRedSubst'
      have hCR' := cr_props_all k' ρ τ₂
      have hBody_SN := hCR'.1 (applySubst (extendSubst σ (var 0)) body) hBody_Red
      -- Relate applySubst (extendSubst σ (var 0)) body to body'
      have hEq : applySubst (extendSubst σ (var 0)) body =
          substTerm0 (var 0) (applySubst (liftSubst σ) body) :=
        (substTerm0_applySubst_lift σ (var 0) body).symm
      rw [hEq] at hBody_SN
      have hSN_body' : SN body' := sn_of_substTerm 0 (var 0) hBody_SN
      exact sn_lam hSN_body'
    have hSN_N : SN N := (cr_props_all k'' ρ τ₁).1 N hN
    -- Key insight: track multi-step from body' to current body for CR2 transfer
    -- First establish reducibility of the beta-reduct at the original body'
    have hk'' : k ≤ k'' := Nat.le_trans hk hk'
    have hσ_wk : RedSubst k'' ρ Γ (shiftSubst δ 0 σ) := redSubst_wkN hσ hk'
    -- Nested SN induction on body (from lambda) and argument
    -- We track: body0 is a multi-step reduct of body', and body0 is SN
    -- Key: intro hbody_multi AFTER the SN pattern match so IH includes it properly
    have hMainGoal : ∀ body0, SN body0 → body' ⟶ₛ* body0 → ∀ arg, SN arg →
        Red k'' ρ τ₁ arg →
        Red k'' ρ τ₂ (app (lam (shiftTyUp δ 0 τ₁) (shiftTypeInTerm δ 0 body0)) arg) := by
      intro body0 hSN_body0
      induction hSN_body0 with
      | intro body0_inner _ ih_body =>
        intro hbody_multi arg hSN_arg
        induction hSN_arg with
        | intro arg_inner harg_acc ih_arg =>
          intro harg_Red
          apply hCR.2
          · intro P hstep
            cases hstep with
            | beta τ'' body'' =>
              -- Beta case: show substTerm0 arg_inner (shiftTypeInTerm δ 0 body0_inner) is reducible
              -- Key: use typing IH for body', then CR2 multi-step to get to body0_inner
              have hRedSubst'' : RedSubst k'' ρ (τ₁ :: Γ) (extendSubst (shiftSubst δ 0 σ) arg_inner) :=
                extendSubst_red hσ_wk harg_Red
              -- Apply the typing IH to get reducibility at body' (the original)
              have hBody_Red := ih hk'' hRedSubst''
              -- hBody_Red : Red k'' ρ τ₂ (applySubst (extendSubst (shiftSubst δ 0 σ) arg_inner) body)
              -- Transform to: Red k'' ρ τ₂ (substTerm0 arg_inner (shiftTypeInTerm δ 0 body'))
              have h1 : shiftTypeInTerm δ 0 (applySubst (liftSubst σ) body) =
                  applySubst (shiftSubst δ 0 (liftSubst σ)) (shiftTypeInTerm δ 0 body) :=
                shiftTypeInTerm_applySubst δ 0 (liftSubst σ) body
              have h2 : shiftSubst δ 0 (liftSubst σ) = liftSubst (shiftSubst δ 0 σ) :=
                shiftSubst_liftSubst_comm δ 0 σ
              have h3 : substTerm0 arg_inner (applySubst (liftSubst (shiftSubst δ 0 σ)) (shiftTypeInTerm δ 0 body)) =
                  applySubst (extendSubst (shiftSubst δ 0 σ) arg_inner) (shiftTypeInTerm δ 0 body) :=
                substTerm0_applySubst_lift (shiftSubst δ 0 σ) arg_inner (shiftTypeInTerm δ 0 body)
              -- TermStructEq transfer
              have hStructEq : shiftTypeInTerm δ 0 body ≈ₜ body := shiftTypeInTerm_TermStructEq δ 0 body
              have hApplyStructEq : applySubst (extendSubst (shiftSubst δ 0 σ) arg_inner) (shiftTypeInTerm δ 0 body) ≈ₜ
                  applySubst (extendSubst (shiftSubst δ 0 σ) arg_inner) body :=
                applySubst_TermStructEq (extendSubst (shiftSubst δ 0 σ) arg_inner) hStructEq
              have hRedAtShiftBody := (Red_TermStructInv τ₂ ρ k'' _ _ (TermStructEq.symm hApplyStructEq)).mp hBody_Red
              -- Now: hRedAtShiftBody : Red k'' ρ τ₂ (applySubst ... (shiftTypeInTerm δ 0 body))
              -- Rewrite to substTerm0 arg_inner (shiftTypeInTerm δ 0 body')
              have hRedAtBody' : Red k'' ρ τ₂ (substTerm0 arg_inner (shiftTypeInTerm δ 0 body')) := by
                simp only [body', h1, h2, h3] at hRedAtShiftBody ⊢
                exact hRedAtShiftBody
              -- Now use CR2 multi-step: body' ⟶ₛ* body0_inner, so substTerm0 ... body' ⟶ₛ* substTerm0 ... body0_inner
              have hShiftMulti : shiftTypeInTerm δ 0 body' ⟶ₛ* shiftTypeInTerm δ 0 body0_inner :=
                shiftTypeInTerm_preserves_multi_step δ 0 hbody_multi
              have hSubstMulti : substTerm0 arg_inner (shiftTypeInTerm δ 0 body') ⟶ₛ*
                  substTerm0 arg_inner (shiftTypeInTerm δ 0 body0_inner) :=
                substTerm_preserves_multi_step 0 arg_inner hShiftMulti
              exact red_cr2_multi hRedAtBody' hSubstMulti
            | appL hstepL =>
              -- Congruence under lambda
              cases hstepL with
              | lam hbody_step =>
                obtain ⟨body0'', hbody0_step, hbody''_eq⟩ := step_of_shiftTypeInTerm_step δ 0 hbody_step
                subst hbody''_eq
                -- Extend the multi-step: body' ⟶ₛ* body0_inner ⟶ₛ body0''
                have hbody_multi' : body' ⟶ₛ* body0'' :=
                  StrongMultiStep.trans hbody_multi (StrongMultiStep.single hbody0_step)
                exact ih_body body0'' hbody0_step hbody_multi' arg_inner (Acc.intro arg_inner harg_acc) harg_Red
            | appR hstepR =>
              have harg' := red_cr2 harg_Red hstepR
              exact ih_arg _ hstepR harg'
          · simp [IsNeutral]
    -- Apply hMainGoal with body0 = body' (refl multi-step)
    have hShiftLam : shiftTypeInTerm δ 0 (lam τ₁ body') =
        lam (shiftTyUp δ 0 τ₁) (shiftTypeInTerm δ 0 body') := by simp [shiftTypeInTerm]
    rw [hShiftLam]
    have hSN_body' : SN body' := sn_lam_inv hSN_lam
    exact hMainGoal body' hSN_body' (StrongMultiStep.refl _) N hSN_N hN
  | @app k Γ M N τ₁ τ₂ hM hN ihM ihN =>
    intro k' hk ρ σ hσ
    simp only [applySubst]
    have hM_Red := ihM hk hσ
    have hN_Red := ihN hk hσ
    -- Apply the function reducibility at level k' with argument N
    simpa [Nat.sub_self, shiftTypeInTerm_zero] using hM_Red k' (Nat.le_refl k') (applySubst σ N) hN_Red
  | @tlam k Γ M τ hbody ih =>
    intro k' hk ρ σ hσ
    simp only [applySubst, Red]
    intro k'' hk' R
    -- Goal: Red (k''+1) (extendTyEnv ρ R) τ (tapp (shift...(tlam body')) (tvar 0))
    -- where body' = applySubst (tshiftSubst σ) M
    let δ := k'' - k'
    let body' := applySubst (tshiftSubst σ) M
    have hCR := cr_props_all (k'' + 1) (extendTyEnv ρ R) τ
    have hk1 : k + 1 ≤ k'' + 1 := Nat.succ_le_succ (Nat.le_trans hk hk')
    -- Get RedSubst at the right level for the typing IH
    have hσ_wk : RedSubst k'' ρ Γ (shiftSubst δ 0 σ) := redSubst_wkN hσ hk'
    have hRedSubst' : RedSubst (k'' + 1) (extendTyEnv ρ R) (shiftContext Γ) (tshiftSubst (shiftSubst δ 0 σ)) :=
      redSubst_shiftContext hσ_wk R
    -- Apply typing IH to get reducibility
    have hBody_Red := ih hk1 hRedSubst'
    -- hBody_Red : Red (k''+1) (extendTyEnv ρ R) τ (applySubst (tshiftSubst (shiftSubst δ 0 σ)) M)
    -- The tlam itself is SN
    have hSN_tlam : SN (tlam body') := by
      have hRedSubst0 : RedSubst (k' + 1) (extendTyEnv ρ R) (shiftContext Γ) (tshiftSubst σ) :=
        redSubst_shiftContext hσ R
      have hk01 : k + 1 ≤ k' + 1 := Nat.succ_le_succ hk
      have hBody_Red0 := ih hk01 hRedSubst0
      have hCR' := cr_props_all (k' + 1) (extendTyEnv ρ R) τ
      have hBody_SN := hCR'.1 _ hBody_Red0
      exact sn_tlam hBody_SN
    have hSN_body' : SN body' := sn_tlam_inv hSN_tlam
    -- Simplify the goal term
    have hShiftTlam : shiftTypeInTerm δ 1 (shiftTypeInTerm 1 0 (tlam body')) =
        tlam (shiftTypeInTerm δ 2 (shiftTypeInTerm 1 1 body')) := by
      simp only [shiftTypeInTerm]
    rw [hShiftTlam]
    -- Main goal via SN induction on body, tracking multi-step from body'
    have hMainGoal : ∀ body0, SN body0 → body' ⟶ₛ* body0 →
        Red (k'' + 1) (extendTyEnv ρ R) τ (tapp (tlam (shiftTypeInTerm δ 2 (shiftTypeInTerm 1 1 body0))) (tvar 0)) := by
      intro body0 hSN_body0
      induction hSN_body0 with
      | intro body0_inner _ ih_body =>
        intro hbody_multi
        apply hCR.2
        · intro P hstep
          cases hstep with
          | tbeta body'' τ' =>
            -- Type beta case: substTypeInTerm0 (tvar 0) (shiftTypeInTerm δ 2 (shiftTypeInTerm 1 1 body0_inner))
            -- Key: all these type-level operations preserve term structure
            -- So the reduct is TermStructEq to body0_inner
            have hStructEq1 : shiftTypeInTerm 1 1 body0_inner ≈ₜ body0_inner :=
              shiftTypeInTerm_TermStructEq 1 1 body0_inner
            have hStructEq2 : shiftTypeInTerm δ 2 (shiftTypeInTerm 1 1 body0_inner) ≈ₜ body0_inner :=
              TermStructEq.trans (shiftTypeInTerm_TermStructEq δ 2 _) hStructEq1
            have hStructEq3 : substTypeInTerm0 (tvar 0) (shiftTypeInTerm δ 2 (shiftTypeInTerm 1 1 body0_inner)) ≈ₜ body0_inner :=
              TermStructEq.trans (substTypeInTerm_TermStructEq 0 (tvar 0) _) hStructEq2
            -- Similarly for body'
            have hStructEq1' : shiftTypeInTerm 1 1 body' ≈ₜ body' := shiftTypeInTerm_TermStructEq 1 1 body'
            have hStructEq2' : shiftTypeInTerm δ 2 (shiftTypeInTerm 1 1 body') ≈ₜ body' :=
              TermStructEq.trans (shiftTypeInTerm_TermStructEq δ 2 _) hStructEq1'
            have hStructEq3' : substTypeInTerm0 (tvar 0) (shiftTypeInTerm δ 2 (shiftTypeInTerm 1 1 body')) ≈ₜ body' :=
              TermStructEq.trans (substTypeInTerm_TermStructEq 0 (tvar 0) _) hStructEq2'
            -- The IH term ≈ₜ body': use applySubst_TermStructEq_subst
            -- Both tshiftSubst (shiftSubst δ 0 σ) and tshiftSubst σ are pointwise ≈ₜ
            have hSubstEq : ∀ n, tshiftSubst (shiftSubst δ 0 σ) n ≈ₜ tshiftSubst σ n := fun n => by
              simp only [tshiftSubst, shiftSubst]
              have h1 : shiftTypeInTerm 1 0 (shiftTypeInTerm δ 0 (σ n)) ≈ₜ σ n :=
                TermStructEq.trans (shiftTypeInTerm_TermStructEq 1 0 _) (shiftTypeInTerm_TermStructEq δ 0 _)
              have h2 : shiftTypeInTerm 1 0 (σ n) ≈ₜ σ n := shiftTypeInTerm_TermStructEq 1 0 _
              exact TermStructEq.trans h1 (TermStructEq.symm h2)
            have hBodyEq : applySubst (tshiftSubst (shiftSubst δ 0 σ)) M ≈ₜ body' :=
              applySubst_TermStructEq_subst hSubstEq M
            -- Transfer from hBody_Red to body' using Red_TermStructInv
            have hRed' : Red (k'' + 1) (extendTyEnv ρ R) τ body' :=
              (Red_TermStructInv τ (extendTyEnv ρ R) (k'' + 1) _ _ hBodyEq).mp hBody_Red
            -- Transfer from body' to substTypeInTerm0 ... body'
            have hRedAtBody' : Red (k'' + 1) (extendTyEnv ρ R) τ
                (substTypeInTerm0 (tvar 0) (shiftTypeInTerm δ 2 (shiftTypeInTerm 1 1 body'))) :=
              (Red_TermStructInv τ (extendTyEnv ρ R) (k'' + 1) _ _ (TermStructEq.symm hStructEq3')).mp hRed'
            -- Now transfer via CR2 multi-step from body' to body0_inner
            have hShiftMulti1 : shiftTypeInTerm 1 1 body' ⟶ₛ* shiftTypeInTerm 1 1 body0_inner :=
              shiftTypeInTerm_preserves_multi_step 1 1 hbody_multi
            have hShiftMulti2 : shiftTypeInTerm δ 2 (shiftTypeInTerm 1 1 body') ⟶ₛ*
                shiftTypeInTerm δ 2 (shiftTypeInTerm 1 1 body0_inner) :=
              shiftTypeInTerm_preserves_multi_step δ 2 hShiftMulti1
            have hSubstMulti : substTypeInTerm0 (tvar 0) (shiftTypeInTerm δ 2 (shiftTypeInTerm 1 1 body')) ⟶ₛ*
                substTypeInTerm0 (tvar 0) (shiftTypeInTerm δ 2 (shiftTypeInTerm 1 1 body0_inner)) :=
              substTypeInTerm_preserves_multi_step 0 (tvar 0) hShiftMulti2
            exact red_cr2_multi hRedAtBody' hSubstMulti
          | tappL hstep' =>
            -- Step under tlam
            cases hstep' with
            | tlam hbody_step =>
              -- The step is: shiftTypeInTerm δ 2 (shiftTypeInTerm 1 1 body0_inner) ⟶ₛ body''
              -- Invert through both shifts to get the underlying body step
              obtain ⟨M1, hM1_step, hM1_eq⟩ := step_of_shiftTypeInTerm_step δ 2 hbody_step
              obtain ⟨M0, hM0_step, hM0_eq⟩ := step_of_shiftTypeInTerm_step 1 1 hM1_step
              -- M0 is the stepped body, so body0_inner ⟶ₛ M0
              subst hM0_eq hM1_eq
              have hbody_multi' : body' ⟶ₛ* M0 :=
                StrongMultiStep.trans hbody_multi (StrongMultiStep.single hM0_step)
              exact ih_body M0 hM0_step hbody_multi'
        · simp [IsNeutral]
    exact hMainGoal body' hSN_body' (StrongMultiStep.refl _)
  | tapp hfun hτ_wf ihfun =>
    -- Type application case: M [σ] is reducible at τ[σ/α]
    intro k' hk ρ σ hσ
    simp only [applySubst]
    have hfun_red := ihfun hk hσ
    -- hfun_red : Red k' ρ (all τ) (applySubst σ M)
    -- Need: Red k' ρ (substTy0 σ τ) (tapp (applySubst σ M) σ)
    exact red_tapp hfun_red _

theorem strong_normalization {Γ : Context} {M : Term} {τ : Ty} (h : HasType 0 Γ M τ) : SN M := by
  have hRed := fundamental_lemma h (Nat.le_refl 0) (ρ := defaultTyEnv) (σ := idSubst) idSubst_red
  rw [applySubst_id] at hRed
  exact (cr_props_all 0 defaultTyEnv τ).1 M hRed

end Metatheory.SystemF

