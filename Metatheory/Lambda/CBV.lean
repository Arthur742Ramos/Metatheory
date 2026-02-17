/-
# Call-by-Value Reduction

This module defines call-by-value (CBV) reduction for the lambda calculus.

## Overview

Call-by-value is a reduction strategy where:
- Arguments must be evaluated to values before being substituted
- No reduction occurs under lambda abstractions (weak reduction)
- Evaluation proceeds left-to-right in applications

## Reduction Rules

The CBV reduction rules are:
- (λM) V →cbv M[V]  (only when V is a value)
- M →cbv M' ⟹ M N →cbv M' N
- V →cbv V' ⟹ V N →cbv V N' (only when V is a value, so this is just for completeness)
- N →cbv N' ⟹ V N →cbv V N' (when V is a value)

## References

- Plotkin, "Call-by-Name, Call-by-Value and the Lambda Calculus" (1975)
- Pierce, "Types and Programming Languages" (2002), Chapter 5
-/

import Metatheory.Lambda.Term
import Metatheory.Lambda.Beta
import Metatheory.Lambda.MultiStep
import Metatheory.Rewriting.Basic

namespace Metatheory.Lambda

open Term

/-! ## Values -/

/-- In pure lambda calculus, values are lambda abstractions.
    This is the standard CBV notion of value. -/
def IsValue : Term → Prop
  | lam _ => True
  | _ => False

/-- Lambda abstractions are values -/
theorem isValue_lam (M : Term) : IsValue (lam M) := trivial

/-- Variables are not values -/
theorem not_isValue_var (n : Nat) : ¬IsValue (var n) := fun h => h

/-- Applications are not values -/
theorem not_isValue_app (M N : Term) : ¬IsValue (app M N) := fun h => h

/-- Decidability of IsValue -/
instance : DecidablePred IsValue := fun M =>
  match M with
  | lam _ => isTrue trivial
  | var _ => isFalse (fun h => h)
  | app _ _ => isFalse (fun h => h)

/-! ## Call-by-Value Reduction -/

/-- Single-step call-by-value reduction.
    M →cbv N means M reduces to N in exactly one CBV step.

    Key differences from full beta:
    1. Beta only fires when argument is a value
    2. No reduction under lambdas (weak reduction)
    3. Left-to-right evaluation order -/
inductive CBVStep : Term → Term → Prop where
  /-- Beta-value rule: (λM) V →cbv M[V] when V is a value -/
  | beta : ∀ M V, IsValue V → CBVStep (app (lam M) V) (M[V])
  /-- Congruence: evaluate function first -/
  | appL : ∀ {M M' N}, CBVStep M M' → CBVStep (app M N) (app M' N)
  /-- Congruence: evaluate argument when function is a value -/
  | appR : ∀ {V N N'}, IsValue V → CBVStep N N' → CBVStep (app V N) (app V N')

/-- Notation for CBV reduction -/
scoped infix:50 " →cbv " => CBVStep

namespace CBVStep

/-! ## Basic Properties -/

/-- Beta-value at root -/
theorem beta_value (M V : Term) (hV : IsValue V) : app (lam M) V →cbv M[V] :=
  CBVStep.beta M V hV

/-- CBV step implies beta step -/
theorem to_beta {M N : Term} (h : M →cbv N) : BetaStep M N := by
  induction h with
  | beta M V _ => exact BetaStep.beta M V
  | appL _ ih => exact BetaStep.appL ih
  | appR _ _ ih => exact BetaStep.appR ih

/-- Values don't step in CBV -/
theorem value_no_step {V N : Term} (hV : IsValue V) : ¬(V →cbv N) := by
  intro h
  cases V with
  | lam M => cases h
  | var n => exact hV
  | app _ _ => exact hV

/-- CBV is deterministic -/
theorem deterministic {M N₁ N₂ : Term} (h1 : M →cbv N₁) (h2 : M →cbv N₂) : N₁ = N₂ := by
  induction h1 generalizing N₂ with
  | beta M V hV =>
    cases h2 with
    | beta M' V' hV' => rfl
    | appL h => cases h
    | appR hV' h => exact absurd h (value_no_step hV)
  | appL hM ih =>
    cases h2 with
    | beta M' V' hV' => cases hM
    | appL hM' => rw [ih hM']
    | appR hV' hN' => exact absurd hM (value_no_step hV')
  | appR hV hN ih =>
    cases h2 with
    | beta M' V' hV' => exact absurd hN (value_no_step hV')
    | appL hM' => exact absurd hM' (value_no_step hV)
    | appR hV' hN' => rw [ih hN']

end CBVStep

/-! ## Confluence -/

/-- CBV reduction is deterministic. -/
theorem cbv_deterministic : Rewriting.Deterministic CBVStep := by
  intro M N₁ N₂ h1 h2
  exact CBVStep.deterministic h1 h2

/-- CBV reduction is confluent, since it is deterministic. -/
theorem cbv_confluent : Rewriting.Confluent CBVStep :=
  Rewriting.confluent_of_deterministic cbv_deterministic

/-! ## Unique Normal Forms -/

theorem isNormalForm_of_isValue {V : Term} (hV : IsValue V) : Rewriting.IsNormalForm CBVStep V := by
  intro N hstep
  exact CBVStep.value_no_step hV hstep

/-! ## Multi-Step CBV Reduction -/

/-- Multi-step CBV reduction (reflexive-transitive closure) -/
inductive CBVMultiStep : Term → Term → Prop where
  | refl : ∀ M, CBVMultiStep M M
  | step : ∀ {M N P}, CBVStep M N → CBVMultiStep N P → CBVMultiStep M P

/-- Notation for multi-step CBV reduction -/
scoped infix:50 " →cbv* " => CBVMultiStep

namespace CBVMultiStep

/-- Single step implies multi-step -/
theorem single {M N : Term} (h : M →cbv N) : M →cbv* N :=
  CBVMultiStep.step h (CBVMultiStep.refl N)

/-- Transitivity -/
theorem trans {M N P : Term} (h1 : M →cbv* N) (h2 : N →cbv* P) : M →cbv* P := by
  induction h1 with
  | refl => exact h2
  | step hstep _ ih => exact CBVMultiStep.step hstep (ih h2)

/-- Congruence: application left -/
theorem appL {M M' N : Term} (h : M →cbv* M') : app M N →cbv* app M' N := by
  induction h with
  | refl => exact CBVMultiStep.refl _
  | step hstep _ ih => exact CBVMultiStep.step (CBVStep.appL hstep) ih

/-- Congruence: application right (when left is value) -/
theorem appR {V N N' : Term} (hV : IsValue V) (h : N →cbv* N') : app V N →cbv* app V N' := by
  induction h with
  | refl => exact CBVMultiStep.refl _
  | step hstep _ ih => exact CBVMultiStep.step (CBVStep.appR hV hstep) ih

/-- CBV multi-step implies beta multi-step -/
theorem to_beta_multi {M N : Term} (h : M →cbv* N) : MultiStep M N := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hcbv _ ih => exact MultiStep.step (CBVStep.to_beta hcbv) ih

/-- CBV multi-step is the generic reflexive-transitive closure (`Rewriting.Star`). -/
theorem toStar {M N : Term} (h : M →cbv* N) : Rewriting.Star CBVStep M N := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | step hMN _ ih => exact Rewriting.Star.head hMN ih

/-- Convert generic `Rewriting.Star` back to CBV multi-step. -/
theorem ofStar {M N : Term} (h : Rewriting.Star CBVStep M N) : M →cbv* N := by
  induction h with
  | refl => exact CBVMultiStep.refl _
  | tail _ hstep ih => exact CBVMultiStep.trans ih (CBVMultiStep.single hstep)

theorem iff_star {M N : Term} : (M →cbv* N) ↔ Rewriting.Star CBVStep M N :=
  ⟨toStar, ofStar⟩

theorem normalForm_unique {M N₁ N₂ : Term}
    (h1 : M →cbv* N₁) (h2 : M →cbv* N₂)
    (hn1 : Rewriting.IsNormalForm CBVStep N₁) (hn2 : Rewriting.IsNormalForm CBVStep N₂) : N₁ = N₂ := by
  have h1' : Rewriting.Star CBVStep M N₁ := (iff_star).1 h1
  have h2' : Rewriting.Star CBVStep M N₂ := (iff_star).1 h2
  exact Rewriting.normalForm_unique_of_deterministic cbv_deterministic h1' h2' hn1 hn2

end CBVMultiStep

/-! ## Examples -/

/-- Identity applied to identity: (λx.x)(λy.y) →cbv λy.y -/
example : app I I →cbv* I := by
  apply CBVMultiStep.single
  apply CBVStep.beta
  exact isValue_lam _

/-! ## Stuck Terms -/

/-- A term is stuck if it's not a value and cannot step -/
def IsStuck (M : Term) : Prop := ¬IsValue M ∧ ¬∃ N, M →cbv N

/-- Variables are stuck -/
theorem var_stuck (n : Nat) : IsStuck (var n) :=
  ⟨not_isValue_var n, fun ⟨_, h⟩ => nomatch h⟩

/-- Application of variable to value is stuck -/
theorem app_var_value_stuck (n : Nat) (V : Term) (hV : IsValue V) :
    IsStuck (app (var n) V) :=
  ⟨not_isValue_app _ _, fun ⟨_, h⟩ => by cases h with
    | appL h => cases h
    | appR _ h => exact absurd h (CBVStep.value_no_step hV)⟩

/-! ## Progress Trichotomy -/

/-- Progress trichotomy: A term is either a value, can step, or is stuck.
    In untyped CBV lambda calculus, terms can get stuck (unlike typed calculus). -/
theorem progress_trichotomy (M : Term) :
    IsValue M ∨ (∃ N, M →cbv N) ∨ IsStuck M := by
  match M with
  | var n => right; right; exact var_stuck n
  | lam M' => left; exact isValue_lam M'
  | app M' N' =>
    have ihM : IsValue M' ∨ (∃ N, M' →cbv N) ∨ IsStuck M' := progress_trichotomy M'
    have ihN : IsValue N' ∨ (∃ N, N' →cbv N) ∨ IsStuck N' := progress_trichotomy N'
    cases ihM with
    | inl hValM =>
      cases ihN with
      | inl hValN =>
        -- Both M' and N' are values
        cases M' with
        | lam M'' =>
          -- (λM'') V →cbv M''[V]
          right; left
          exact ⟨M''[N'], CBVStep.beta M'' N' hValN⟩
        | var n => exact absurd hValM (not_isValue_var n)
        | app _ _ => exact absurd hValM (not_isValue_app _ _)
      | inr hN =>
        cases hN with
        | inl hStepN =>
          -- M' is value, N' can step
          obtain ⟨N'', hN'step⟩ := hStepN
          right; left
          exact ⟨app M' N'', CBVStep.appR hValM hN'step⟩
        | inr hStuckN =>
          -- M' is value, N' is stuck
          cases M' with
          | lam M'' =>
            -- Application is stuck because argument is stuck
            right; right
            constructor
            · exact not_isValue_app _ _
            · intro ⟨P, hP⟩
              cases hP with
              | beta _ _ hV => exact hStuckN.1 hV
              | appR _ hN' => exact hStuckN.2 ⟨_, hN'⟩
              | appL hM' => cases hM'
          | var n => exact absurd hValM (not_isValue_var n)
          | app _ _ => exact absurd hValM (not_isValue_app _ _)
    | inr hM =>
      cases hM with
      | inl hStepM =>
        -- M' can step
        obtain ⟨M'', hM'step⟩ := hStepM
        right; left
        exact ⟨app M'' N', CBVStep.appL hM'step⟩
      | inr hStuckM =>
        -- M' is stuck, so M' N' is stuck too
        right; right
        constructor
        · exact not_isValue_app _ _
        · intro ⟨P, hP⟩
          cases hP with
          | beta _ _ _ => exact hStuckM.1 (isValue_lam _)
          | appL hM' => exact hStuckM.2 ⟨_, hM'⟩
          | appR hV _ => exact hStuckM.1 hV

end Metatheory.Lambda
