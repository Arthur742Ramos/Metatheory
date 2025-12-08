/-
# Complete Development (Maximal Reduction)

This module defines the complete development of a term, which reduces
ALL redexes simultaneously. This is the key tool for proving the diamond property.

## Complete Development

For any term M, we define M⁺ (written `complete M`) as the result of
reducing every redex in M. The key property is:

**If M ⇒ N, then N ⇒ M⁺**

This immediately gives us the diamond property:
- M ⇒ N₁ implies N₁ ⇒ M⁺
- M ⇒ N₂ implies N₂ ⇒ M⁺
- So both N₁ and N₂ reduce to M⁺!
-/

import Metatheory.Lambda.Parallel

namespace Metatheory.Lambda

open Term

/-! ## Complete Development Definition -/

/-- Complete development: reduce ALL redexes in a term.

    IMPORTANT: The pattern matching order matters!
    The (app (lam M) N) case MUST come before the general (app M N) case. -/
def complete : Term → Term
  | var n => var n
  | lam M => lam (complete M)
  | app (lam M) N => (complete M)[complete N]  -- Reduce the redex!
  | app M N => app (complete M) (complete N)

/-! ## Basic Properties -/

/-- Complete development of a variable is itself -/
@[simp] theorem complete_var (n : Nat) : complete (var n) = var n := rfl

/-- Complete development of a lambda -/
@[simp] theorem complete_lam (M : Term) : complete (lam M) = lam (complete M) := rfl

/-- Complete development of a beta redex -/
@[simp] theorem complete_beta (M N : Term) :
    complete (app (lam M) N) = (complete M)[complete N] := rfl

/-- Complete development of a non-redex application -/
theorem complete_app_non_lam {M N : Term} (h : ∀ M', M ≠ lam M') :
    complete (app M N) = app (complete M) (complete N) := by
  cases M with
  | var n => rfl
  | app M₁ M₂ => rfl
  | lam M' => exact absurd rfl (h M')

/-! ## Inversion Lemma -/

/-- Inversion for parallel reduction under lambda -/
theorem par_lam_inv {M M' : Term} (h : lam M ⇒ lam M') : M ⇒ M' := by
  cases h with
  | lam hBody => exact hBody

/-! ## The Key Theorem: Parallel Reduction to Complete Development -/

/-- If M ⇒ N, then N ⇒ complete M.

    This is THE KEY LEMMA for Church-Rosser.
    It says that any parallel reduct of M can further reduce to M⁺. -/
theorem par_complete {M N : Term} (h : M ⇒ N) : N ⇒ complete M := by
  induction h with
  | var n =>
    -- var n ⇒ var n, need var n ⇒ complete (var n) = var n
    exact ParRed.refl _
  | app hM hN ih_M ih_N =>
    -- Case: M @ N ⇒ M' @ N' (non-beta case)
    -- Need: M' @ N' ⇒ complete (M @ N)
    -- complete (M @ N) depends on whether M is a lambda
    cases hM with
    | var n =>
      -- M = var n, so complete (M @ N) = app (complete M) (complete N)
      simp only [complete]
      exact ParRed.app ih_M ih_N
    | app _ _ =>
      -- M = app _ _, so complete (M @ N) = app (complete M) (complete N)
      simp only [complete]
      exact ParRed.app ih_M ih_N
    | lam hBody =>
      -- M = lam body, M' = lam body', and we're in the non-beta app case
      -- complete (app (lam body) N) = (complete body)[complete N]
      -- We have: ih_M : lam body' ⇒ lam (complete body)
      -- Need: app (lam body') N' ⇒ (complete body)[complete N]
      -- Use inversion to get body' ⇒ complete body, then ParRed.beta
      simp only [complete]
      exact ParRed.beta (par_lam_inv ih_M) ih_N
    | beta _ _ =>
      -- Can't happen: if M is (λ_)_, then the original app constructor
      -- would have matched beta, not app
      simp only [complete]
      exact ParRed.app ih_M ih_N
  | lam hM ih =>
    -- lam M ⇒ lam M', need lam M' ⇒ complete (lam M) = lam (complete M)
    exact ParRed.lam ih
  | beta hM hN ih_M ih_N =>
    -- (λM) @ N ⇒ M'[N'] via beta
    -- complete ((λM) @ N) = (complete M)[complete N]
    -- Need: M'[N'] ⇒ (complete M)[complete N]
    -- By ih: M' ⇒ complete M and N' ⇒ complete N
    -- So by ParRed.subst: M'[N'] ⇒ (complete M)[complete N]
    exact ParRed.subst ih_M ih_N

/-! ## Reflexivity of Parallel Reduction to Complete Development -/

/-- Every term parallel-reduces to its complete development -/
theorem par_to_complete (M : Term) : M ⇒ complete M :=
  par_complete (ParRed.refl M)

end Metatheory.Lambda
