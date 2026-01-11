/-
# System F Types

This module defines types for System F (polymorphic lambda calculus).

## Overview

System F extends simple types with universal quantification:
- Type variables (α, β, ...) represented with de Bruijn indices
- Arrow types (τ → σ)
- Universal types (∀α. τ)

## De Bruijn Representation

Type variables use de Bruijn indices to avoid α-conversion issues.
- `tvar 0` refers to the innermost bound type variable
- `tvar 1` refers to the next outer one, etc.

## References

- Girard, "Interprétation fonctionnelle et élimination des coupures" (1972)
- Reynolds, "Towards a theory of type structure" (1974)
- Pierce, "Types and Programming Languages" (2002), Chapter 23
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
-/

namespace Metatheory.SystemF

/-! ## Type Syntax -/

/-- System F types with de Bruijn indices for type variables. -/
inductive Ty : Type where
  /-- Type variable (de Bruijn index) -/
  | tvar : Nat → Ty
  /-- Arrow type (function type) -/
  | arr : Ty → Ty → Ty
  /-- Universal type (∀α. τ) -/
  | all : Ty → Ty
  deriving Repr, DecidableEq

namespace Ty

/-- Notation for arrow types -/
infixr:25 " ⇒ " => arr

/-! ## Type Shifting

Shifting adjusts de Bruijn indices when moving under binders.
We use Nat arithmetic (with saturation at 0) instead of Int for simplicity. -/

/-- Shift type variables up by d at cutoff c -/
def shiftTyUp (d : Nat) (c : Nat) : Ty → Ty
  | tvar n => if n < c then tvar n else tvar (n + d)
  | arr τ₁ τ₂ => arr (shiftTyUp d c τ₁) (shiftTyUp d c τ₂)
  | all τ => all (shiftTyUp d (c + 1) τ)

/-- Shift type variables down by 1 at cutoff c (used after substitution) -/
def shiftTyDown (c : Nat) : Ty → Ty
  | tvar n => if n < c then tvar n else tvar (n - 1)
  | arr τ₁ τ₂ => arr (shiftTyDown c τ₁) (shiftTyDown c τ₂)
  | all τ => all (shiftTyDown (c + 1) τ)

/-! ## Type Substitution

`substTy k σ τ` substitutes σ for type variable k in τ. -/

/-- Substitute type σ for type variable k in type τ -/
def substTy (k : Nat) (σ : Ty) : Ty → Ty
  | tvar n =>
    if n < k then tvar n
    else if n = k then σ
    else tvar (n - 1)  -- Decrement indices above k
  | arr τ₁ τ₂ => arr (substTy k σ τ₁) (substTy k σ τ₂)
  | all τ => all (substTy (k + 1) (shiftTyUp 1 0 σ) τ)

/-- Substitute for the outermost type variable (index 0) -/
abbrev substTy0 (σ τ : Ty) : Ty := substTy 0 σ τ

/-! ## Basic Properties -/

/-- Shifting up by 0 is identity -/
theorem shiftTyUp_zero (τ : Ty) (c : Nat) : shiftTyUp 0 c τ = τ := by
  induction τ generalizing c with
  | tvar n =>
    unfold shiftTyUp
    split
    · rfl
    · rfl
  | arr τ₁ τ₂ ih₁ ih₂ =>
    unfold shiftTyUp
    rw [ih₁ c, ih₂ c]
  | all τ ih =>
    unfold shiftTyUp
    rw [ih (c + 1)]

/-- Shifting up then down cancels -/
theorem shiftTyDown_shiftTyUp_cancel (τ : Ty) (c : Nat) :
    shiftTyDown c (shiftTyUp 1 c τ) = τ := by
  induction τ generalizing c with
  | tvar n =>
    unfold shiftTyUp
    by_cases h : n < c
    · simp only [if_pos h]
      unfold shiftTyDown
      exact if_pos h
    · simp only [if_neg h]
      unfold shiftTyDown
      have h' : ¬(n + 1 < c) := Nat.not_lt_of_le (Nat.le_step (Nat.le_of_not_lt h))
      rw [if_neg h']
      exact congrArg tvar (Nat.succ_sub_one n)
  | arr τ₁ τ₂ ih₁ ih₂ =>
    unfold shiftTyUp shiftTyDown
    rw [ih₁, ih₂]
  | all τ ih =>
    unfold shiftTyUp shiftTyDown
    rw [ih]

/-! ## Well-Formedness

A type is well-formed if all its free type variables are bound.
`WF n τ` means τ is well-formed with n type variables in scope. -/

/-- Type well-formedness: all free type variables have index < n -/
def WF (n : Nat) : Ty → Prop
  | tvar k => k < n
  | arr τ₁ τ₂ => WF n τ₁ ∧ WF n τ₂
  | all τ => WF (n + 1) τ

/-- WF is monotonic: more variables in scope is fine -/
theorem WF_mono {n m : Nat} {τ : Ty} (h : WF n τ) (hnm : n ≤ m) : WF m τ := by
  induction τ generalizing n m with
  | tvar k =>
    unfold WF at h ⊢
    exact Nat.lt_of_lt_of_le h hnm
  | arr τ₁ τ₂ ih₁ ih₂ =>
    unfold WF at h ⊢
    exact ⟨ih₁ h.1 hnm, ih₂ h.2 hnm⟩
  | all τ ih =>
    unfold WF at h ⊢
    exact ih h (Nat.add_le_add_right hnm 1)

/-- Shifting up preserves well-formedness -/
theorem WF_shiftTyUp {n : Nat} {τ : Ty} (d c : Nat) (hτ : WF n τ) :
    WF (n + d) (shiftTyUp d c τ) := by
  induction τ generalizing n c with
  | tvar k =>
    -- hτ : k < n, goal: WF (n+d) (shiftTyUp d c (tvar k))
    unfold shiftTyUp
    by_cases h : k < c
    · -- k < c: result is tvar k, need k < n + d
      simp only [if_pos h]
      unfold WF
      exact Nat.lt_of_lt_of_le hτ (Nat.le_add_right n d)
    · -- k ≥ c: result is tvar (k + d), need k + d < n + d
      simp only [if_neg h]
      unfold WF
      exact Nat.add_lt_add_right hτ d
  | arr τ₁ τ₂ ih₁ ih₂ =>
    unfold shiftTyUp WF
    have ⟨h1, h2⟩ : WF n τ₁ ∧ WF n τ₂ := hτ
    exact ⟨ih₁ c h1, ih₂ c h2⟩
  | all τ ih =>
    unfold shiftTyUp WF
    have h := ih (c + 1) hτ
    rw [Nat.add_right_comm] at h
    exact h

/-! ## Substitution Preserves Well-Formedness -/

/-- General substitution preserves well-formedness -/
theorem WF_substTy {n k : Nat} {τ σ : Ty} (hk : k ≤ n)
    (hτ : WF (n + 1) τ) (hσ : WF n σ) : WF n (substTy k σ τ) := by
  induction τ generalizing n k σ with
  | tvar m =>
    unfold substTy
    by_cases h1 : m < k
    · simp only [if_pos h1]
      unfold WF
      -- m < k ≤ n, so m < n
      exact Nat.lt_of_lt_of_le h1 hk
    · simp only [if_neg h1]
      by_cases h2 : m = k
      · simp only [if_pos h2]
        exact hσ
      · simp only [if_neg h2]
        unfold WF
        -- m > k, so m ≥ 1. Also m < n + 1, so m - 1 < n
        have hm : m < n + 1 := hτ
        have hm_gt_k : k < m := Nat.lt_of_le_of_ne (Nat.not_lt.mp h1) (Ne.symm h2)
        have hm_pos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le k) hm_gt_k
        have h1 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm_pos
        exact Nat.lt_of_succ_lt_succ (h1 ▸ hm)
  | arr τ₁ τ₂ ih₁ ih₂ =>
    unfold substTy WF
    have ⟨h1, h2⟩ := hτ
    exact ⟨ih₁ hk h1 hσ, ih₂ hk h2 hσ⟩
  | all τ ih =>
    unfold substTy WF
    have hσ' : WF (n + 1) (shiftTyUp 1 0 σ) := WF_shiftTyUp 1 0 hσ
    exact ih (Nat.succ_le_succ hk) hτ hσ'

/-- Substitution at 0 preserves well-formedness -/
theorem WF_substTy0 {n : Nat} {τ σ : Ty}
    (hτ : WF (n + 1) τ) (hσ : WF n σ) : WF n (substTy0 σ τ) :=
  WF_substTy (Nat.zero_le n) hτ hσ

/-! ## Closed Types -/

/-- A type is closed if it has no free type variables -/
def Closed (τ : Ty) : Prop := WF 0 τ

/-- Arrow of closed types is closed -/
theorem Closed_arr {τ₁ τ₂ : Ty} (h₁ : Closed τ₁) (h₂ : Closed τ₂) : Closed (τ₁ ⇒ τ₂) :=
  ⟨h₁, h₂⟩

/-- ∀-type with closed body under one variable is closed -/
theorem Closed_all {τ : Ty} (h : WF 1 τ) : Closed (all τ) := h

/-! ## Examples -/

/-- The identity type: ∀α. α → α -/
def idTy : Ty := all (tvar 0 ⇒ tvar 0)

/-- The Church boolean type: ∀α. α → α → α -/
def boolTy : Ty := all (tvar 0 ⇒ tvar 0 ⇒ tvar 0)

/-- The Church natural type: ∀α. (α → α) → α → α -/
def natTy : Ty := all ((tvar 0 ⇒ tvar 0) ⇒ tvar 0 ⇒ tvar 0)

/-- Identity type is closed -/
theorem idTy_closed : Closed idTy := by
  unfold Closed idTy WF
  exact ⟨Nat.zero_lt_one, Nat.zero_lt_one⟩

/-- Bool type is closed -/
theorem boolTy_closed : Closed boolTy := by
  unfold Closed boolTy WF
  exact ⟨Nat.zero_lt_one, Nat.zero_lt_one, Nat.zero_lt_one⟩

/-- Nat type is closed -/
theorem natTy_closed : Closed natTy := by
  unfold Closed natTy WF
  exact ⟨⟨Nat.zero_lt_one, Nat.zero_lt_one⟩, Nat.zero_lt_one, Nat.zero_lt_one⟩

end Ty

end Metatheory.SystemF
