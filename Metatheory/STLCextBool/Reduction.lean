/-
# Simply Typed Lambda Calculus with Booleans - Reduction

This module defines single-step reduction for STLC with booleans.

## Reduction Rules

- Beta reduction: (λM)N → M[N]
- Conditional reductions:
  - if true then N₁ else N₂ → N₁
  - if false then N₁ else N₂ → N₂

## References

- Pierce, "Types and Programming Languages" (2002), Chapter 11
-/

import Metatheory.STLCextBool.Terms

namespace Metatheory.STLCextBool

open Term

/-! ## Single-Step Reduction -/

/-- Single-step reduction for STLC with booleans. -/
inductive Step : Term → Term → Prop where
  | beta : ∀ M N, Step (app (lam M) N) (M[N])
  | iteTrue : ∀ N₁ N₂, Step (ite ttrue N₁ N₂) N₁
  | iteFalse : ∀ N₁ N₂, Step (ite tfalse N₁ N₂) N₂
  | appL : ∀ {M M' N}, Step M M' → Step (app M N) (app M' N)
  | appR : ∀ {M N N'}, Step N N' → Step (app M N) (app M N')
  | lamStep : ∀ {M M'}, Step M M' → Step (lam M) (lam M')
  | iteC : ∀ {M M' N₁ N₂}, Step M M' → Step (ite M N₁ N₂) (ite M' N₁ N₂)
  | iteT : ∀ {M N₁ N₁' N₂}, Step N₁ N₁' → Step (ite M N₁ N₂) (ite M N₁' N₂)
  | iteF : ∀ {M N₁ N₂ N₂'}, Step N₂ N₂' → Step (ite M N₁ N₂) (ite M N₁ N₂')

/-- Notation for reduction. -/
scoped infix:50 " ⟶ " => Step

namespace Step

/-- Beta reduction at root. -/
theorem beta_root (M N : Term) : app (lam M) N ⟶ M[N] :=
  Step.beta M N

/-- If-true reduction at root. -/
theorem ite_true_root (N₁ N₂ : Term) : ite ttrue N₁ N₂ ⟶ N₁ :=
  Step.iteTrue N₁ N₂

/-- If-false reduction at root. -/
theorem ite_false_root (N₁ N₂ : Term) : ite tfalse N₁ N₂ ⟶ N₂ :=
  Step.iteFalse N₁ N₂

end Step

/-! ## Multi-Step Reduction -/

/-- Multi-step reduction (reflexive-transitive closure of Step). -/
inductive MultiStep : Term → Term → Prop where
  | refl : ∀ M, MultiStep M M
  | step : ∀ {M N P}, Step M N → MultiStep N P → MultiStep M P

/-- Notation for multi-step reduction. -/
scoped infix:50 " ⟶* " => MultiStep

namespace MultiStep

/-- Single step implies multi-step. -/
theorem single {M N : Term} (h : Step M N) : M ⟶* N :=
  MultiStep.step h (MultiStep.refl N)

/-- Transitivity of multi-step. -/
theorem trans {M N P : Term} (h1 : M ⟶* N) (h2 : N ⟶* P) : M ⟶* P := by
  induction h1 with
  | refl => exact h2
  | step hMN _ ih => exact MultiStep.step hMN (ih h2)

/-- Congruence: application left. -/
theorem appL {M M' N : Term} (h : M ⟶* M') : app M N ⟶* app M' N := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.appL hstep) ih

/-- Congruence: application right. -/
theorem appR {M N N' : Term} (h : N ⟶* N') : app M N ⟶* app M N' := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.appR hstep) ih

/-- Congruence: lambda. -/
theorem lam {M M' : Term} (h : M ⟶* M') : lam M ⟶* lam M' := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.lamStep hstep) ih

/-- Congruence: if condition. -/
theorem iteC {M M' N₁ N₂ : Term} (h : M ⟶* M') : ite M N₁ N₂ ⟶* ite M' N₁ N₂ := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.iteC hstep) ih

/-- Congruence: if-then branch. -/
theorem iteT {M N₁ N₁' N₂ : Term} (h : N₁ ⟶* N₁') : ite M N₁ N₂ ⟶* ite M N₁' N₂ := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.iteT hstep) ih

/-- Congruence: if-else branch. -/
theorem iteF {M N₁ N₂ N₂' : Term} (h : N₂ ⟶* N₂') : ite M N₁ N₂ ⟶* ite M N₁ N₂' := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.iteF hstep) ih

end MultiStep

end Metatheory.STLCextBool
