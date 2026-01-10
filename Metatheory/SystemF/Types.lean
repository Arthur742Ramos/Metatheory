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
    simp only [shiftTyUp]
    split <;> simp [Nat.add_zero]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp only [shiftTyUp, ih₁, ih₂]
  | all τ ih =>
    simp only [shiftTyUp, ih]

/-- Shifting up then down cancels -/
theorem shiftTyDown_shiftTyUp_cancel (τ : Ty) (c : Nat) :
    shiftTyDown c (shiftTyUp 1 c τ) = τ := by
  induction τ generalizing c with
  | tvar n =>
    simp only [shiftTyUp]
    by_cases h : n < c
    · simp only [h, ite_true, shiftTyDown]
    · simp only [h, ite_false]
      have h' : ¬(n + 1 < c) := by omega
      simp only [shiftTyDown, h', ite_false, Nat.add_sub_cancel]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp only [shiftTyUp, shiftTyDown]
    rw [ih₁, ih₂]
  | all τ ih =>
    simp only [shiftTyUp, shiftTyDown]
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
    simp only [WF] at h ⊢
    omega
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp only [WF] at h ⊢
    exact ⟨ih₁ h.1 hnm, ih₂ h.2 hnm⟩
  | all τ ih =>
    simp only [WF] at h ⊢
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
      simp only [h, ite_true, WF]
      have hk : k < n := hτ
      omega
    · -- k ≥ c: result is tvar (k + d), need k + d < n + d
      simp only [h, ite_false, WF]
      have hk : k < n := hτ
      omega
  | arr τ₁ τ₂ ih₁ ih₂ =>
    unfold shiftTyUp WF
    have ⟨h1, h2⟩ : WF n τ₁ ∧ WF n τ₂ := hτ
    exact ⟨ih₁ c h1, ih₂ c h2⟩
  | all τ ih =>
    unfold shiftTyUp WF
    have h := ih (c + 1) hτ
    simp only [Nat.add_right_comm] at h
    exact h

/-! ## Substitution Preserves Well-Formedness -/

/-- General substitution preserves well-formedness -/
theorem WF_substTy {n k : Nat} {τ σ : Ty} (hk : k ≤ n)
    (hτ : WF (n + 1) τ) (hσ : WF n σ) : WF n (substTy k σ τ) := by
  induction τ generalizing n k σ with
  | tvar m =>
    simp only [substTy]
    by_cases h1 : m < k
    · simp only [h1, ite_true, WF]
      have hm : m < n + 1 := hτ
      omega
    · simp only [h1, ite_false]
      by_cases h2 : m = k
      · simp only [h2, ite_true]
        exact hσ
      · simp only [h2, ite_false, WF]
        have hm : m < n + 1 := hτ
        omega
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp only [substTy, WF]
    have ⟨h1, h2⟩ := hτ
    exact ⟨ih₁ hk h1 hσ, ih₂ hk h2 hσ⟩
  | all τ ih =>
    simp only [substTy, WF]
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
  simp only [Closed, idTy, WF]
  constructor <;> omega

/-- Bool type is closed -/
theorem boolTy_closed : Closed boolTy := by
  simp only [Closed, boolTy, WF]
  constructor
  · omega
  · constructor <;> omega

/-- Nat type is closed -/
theorem natTy_closed : Closed natTy := by
  simp only [Closed, natTy, WF]
  constructor
  · constructor <;> omega
  · constructor <;> omega

end Ty

end Metatheory.SystemF
