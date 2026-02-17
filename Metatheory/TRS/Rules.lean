/-
# Rewriting Rules for Simple Expressions

This module defines the single-step rewriting relation for
simple arithmetic expressions.

## Rules

Our rewriting system includes:
- `addZeroR`: e + 0 → e (additive identity, right)
- `addZeroL`: 0 + e → e (additive identity, left)
- `mulOneR`: e * 1 → e (multiplicative identity, right)
- `mulOneL`: 1 * e → e (multiplicative identity, left)
- `mulZeroR`: e * 0 → 0 (zero annihilation, right)
- `mulZeroL`: 0 * e → 0 (zero annihilation, left)

Plus congruence rules for reducing subexpressions.

## Properties

This system is:
1. **Terminating**: Each rule reduces expression size
2. **Locally confluent**: We prove this by case analysis
3. **Therefore confluent**: By Newman's lemma
-/

import Metatheory.TRS.Syntax
import Metatheory.Rewriting.Basic

namespace Metatheory.TRS

open Expr

/-! ## Single-Step Reduction -/

/-- Single-step reduction relation for expressions.

    This includes both the base rules (simplifications) and
    congruence rules (reducing inside subexpressions). -/
inductive Step : Expr → Expr → Prop where
  -- Additive identity
  | addZeroR : ∀ e, Step (e ⊕ 𝟬) e
  | addZeroL : ∀ e, Step (𝟬 ⊕ e) e
  -- Multiplicative identity
  | mulOneR : ∀ e, Step (e ⊛ 𝟭) e
  | mulOneL : ∀ e, Step (𝟭 ⊛ e) e
  -- Zero annihilation
  | mulZeroR : ∀ e, Step (e ⊛ 𝟬) 𝟬
  | mulZeroL : ∀ e, Step (𝟬 ⊛ e) 𝟬
  -- Congruence: reduce inside add
  | addL : ∀ {e₁ e₁' e₂}, Step e₁ e₁' → Step (e₁ ⊕ e₂) (e₁' ⊕ e₂)
  | addR : ∀ {e₁ e₂ e₂'}, Step e₂ e₂' → Step (e₁ ⊕ e₂) (e₁ ⊕ e₂')
  -- Congruence: reduce inside mul
  | mulL : ∀ {e₁ e₁' e₂}, Step e₁ e₁' → Step (e₁ ⊛ e₂) (e₁' ⊛ e₂)
  | mulR : ∀ {e₁ e₂ e₂'}, Step e₂ e₂' → Step (e₁ ⊛ e₂) (e₁ ⊛ e₂')

/-- Notation for single step -/
scoped infix:50 " ⟶ " => Step

namespace Step

/-! ## Reduction Decreases Size

We prove that each reduction step strictly decreases expression size.
This is key for proving termination.
-/

/-- Every step decreases size -/
theorem size_decreasing {e₁ e₂ : Expr} (h : e₁ ⟶ e₂) : e₂.size < e₁.size := by
  induction h with
  | addZeroR e => simp only [Expr.size]; omega
  | addZeroL e => simp only [Expr.size]; omega
  | mulOneR e => simp only [Expr.size]; omega
  | mulOneL e => simp only [Expr.size]; omega
  | mulZeroR e =>
    simp only [Expr.size]
    have h := Expr.size_pos e
    omega
  | mulZeroL e =>
    simp only [Expr.size]
    have h := Expr.size_pos e
    omega
  | addL _ ih => simp only [Expr.size] at ih ⊢; omega
  | addR _ ih => simp only [Expr.size] at ih ⊢; omega
  | mulL _ ih => simp only [Expr.size] at ih ⊢; omega
  | mulR _ ih => simp only [Expr.size] at ih ⊢; omega

/-! ## No Infinite Chains

Since each step decreases size, there are no infinite reduction chains.
-/

/-- The measure for well-founded recursion -/
def measure (e : Expr) : Nat := e.size

/-- The relation "reduces to" in terms of size -/
def sizeOrder (e₁ e₂ : Expr) : Prop := e₁.size < e₂.size

/-- Size order is well-founded -/
theorem sizeOrder_wf : WellFounded sizeOrder :=
  InvImage.wf Expr.size Nat.lt_wfRel.wf

end Step

/-! ## Multi-Step Reduction -/

/-- Multi-step reduction (reflexive-transitive closure of Step) -/
def MultiStep : Expr → Expr → Prop := Rewriting.Star Step

/-- Notation for multi-step reduction -/
scoped infix:50 " ⟶* " => MultiStep

namespace MultiStep

/-- Reflexivity -/
theorem refl (e : Expr) : e ⟶* e := Rewriting.Star.refl e

/-- Single step implies multi-step -/
theorem single {e₁ e₂ : Expr} (h : e₁ ⟶ e₂) : e₁ ⟶* e₂ :=
  Rewriting.Star.single h

/-- Transitivity -/
theorem trans {e₁ e₂ e₃ : Expr} (h1 : e₁ ⟶* e₂) (h2 : e₂ ⟶* e₃) : e₁ ⟶* e₃ :=
  Rewriting.Star.trans h1 h2

/-! ## Congruence for Multi-Step -/

theorem addL {e₁ e₁' e₂ : Expr} (h : e₁ ⟶* e₁') : (e₁ ⊕ e₂) ⟶* (e₁' ⊕ e₂) := by
  induction h with
  | refl => exact refl _
  | tail _ hstep ih => exact trans ih (single (Step.addL hstep))

theorem addR {e₁ e₂ e₂' : Expr} (h : e₂ ⟶* e₂') : (e₁ ⊕ e₂) ⟶* (e₁ ⊕ e₂') := by
  induction h with
  | refl => exact refl _
  | tail _ hstep ih => exact trans ih (single (Step.addR hstep))

theorem mulL {e₁ e₁' e₂ : Expr} (h : e₁ ⟶* e₁') : (e₁ ⊛ e₂) ⟶* (e₁' ⊛ e₂) := by
  induction h with
  | refl => exact refl _
  | tail _ hstep ih => exact trans ih (single (Step.mulL hstep))

theorem mulR {e₁ e₂ e₂' : Expr} (h : e₂ ⟶* e₂') : (e₁ ⊛ e₂) ⟶* (e₁ ⊛ e₂') := by
  induction h with
  | refl => exact refl _
  | tail _ hstep ih => exact trans ih (single (Step.mulR hstep))

end MultiStep

end Metatheory.TRS
