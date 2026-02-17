/-
# Multi-Step Beta Reduction

This module defines the reflexive-transitive closure of beta reduction.

## Multi-Step Reduction

M →* N means M reduces to N in zero or more steps.
-/

import Metatheory.Lambda.Beta

namespace Metatheory.Lambda

open Term

/-! ## Reflexive-Transitive Closure -/

/-- Multi-step beta reduction (reflexive-transitive closure).
    M →* N means M reduces to N in zero or more steps. -/
inductive MultiStep : Term → Term → Prop where
  | refl : ∀ M, MultiStep M M
  | step : ∀ {M N P}, BetaStep M N → MultiStep N P → MultiStep M P

/-- Notation for multi-step reduction -/
scoped infix:50 " →* " => MultiStep

namespace MultiStep

/-! ## Basic Properties -/

/-- Single step implies multi-step -/
theorem single {M N : Term} (h : M →β N) : M →* N :=
  step h (refl N)

/-- Transitivity of multi-step reduction -/
theorem trans {M N P : Term} (h1 : M →* N) (h2 : N →* P) : M →* P := by
  induction h1 with
  | refl _ => exact h2
  | step s _ ih => exact step s (ih h2)

/-! ## Congruence Lemmas -/

/-- Multi-step reduction is preserved in left of application -/
theorem appL {M M' N : Term} (h : M →* M') : (M @ N) →* (M' @ N) := by
  induction h with
  | refl _ => exact refl _
  | step s _ ih => exact step (BetaStep.appL s) ih

/-- Multi-step reduction is preserved in right of application -/
theorem appR {M N N' : Term} (h : N →* N') : (M @ N) →* (M @ N') := by
  induction h with
  | refl _ => exact refl _
  | step s _ ih => exact step (BetaStep.appR s) ih

/-- Multi-step reduction is preserved under lambda -/
theorem lam {M M' : Term} (h : M →* M') : (ƛ M) →* (ƛ M') := by
  induction h with
  | refl _ => exact refl _
  | step s _ ih => exact step (BetaStep.lam s) ih

/-- Congruence for application on both sides -/
theorem app {M M' N N' : Term} (hM : M →* M') (hN : N →* N') :
    (M @ N) →* (M' @ N') :=
  trans (appL hM) (appR hN)

end MultiStep

end Metatheory.Lambda
