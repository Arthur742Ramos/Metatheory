/-
# Complete Development (Maximal Reduction) for System F

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

## System F Redexes

System F has two kinds of redexes:
- Term beta: (λx:τ. M) N → M[N/x]
- Type beta: (Λα. M) [σ] → M[σ/α]

Complete development contracts all of these simultaneously.

## References

- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
-/

import Metatheory.SystemF.Parallel

namespace Metatheory.SystemF

open Ty Term

/-! ## Complete Development Definition -/

/-- Complete development: reduce ALL redexes in a term.

    IMPORTANT: The pattern matching order matters!
    - The `app (lam τ M) N` case MUST come before `app M N`
    - The `tapp (tlam M) τ` case MUST come before `tapp M τ` -/
def complete : Term → Term
  | Term.var n => Term.var n
  | Term.lam τ M => Term.lam τ (complete M)
  | Term.tlam M => Term.tlam (complete M)
  | Term.app (Term.lam _ body) N => substTerm0 (complete N) (complete body)
  | Term.app M N => Term.app (complete M) (complete N)
  | Term.tapp (Term.tlam body) τ => substTypeInTerm0 τ (complete body)
  | Term.tapp M τ => Term.tapp (complete M) τ

/-! ## Basic Properties -/

/-- Complete development of a variable is itself -/
@[simp] theorem complete_var (n : Nat) : complete (Term.var n) = Term.var n := rfl

/-- Complete development of a lambda -/
@[simp] theorem complete_lam (τ : Ty) (M : Term) :
    complete (Term.lam τ M) = Term.lam τ (complete M) := rfl

/-- Complete development of a type abstraction -/
@[simp] theorem complete_tlam (M : Term) : complete (Term.tlam M) = Term.tlam (complete M) := rfl

/-- Complete development of a term beta redex -/
@[simp] theorem complete_beta (τ : Ty) (body N : Term) :
    complete (Term.app (Term.lam τ body) N) = substTerm0 (complete N) (complete body) := rfl

/-- Complete development of a type beta redex -/
@[simp] theorem complete_tbeta (body : Term) (τ : Ty) :
    complete (Term.tapp (Term.tlam body) τ) = substTypeInTerm0 τ (complete body) := rfl

/-- Complete development of a non-redex application (M not a lambda) -/
theorem complete_app_non_lam {M N : Term} (h : ∀ τ M', M ≠ Term.lam τ M') :
    complete (Term.app M N) = Term.app (complete M) (complete N) := by
  cases M with
  | var n => rfl
  | app M₁ M₂ => rfl
  | lam τ M' => exact absurd rfl (h τ M')
  | tlam M' => rfl
  | tapp M' σ => rfl

/-- Complete development of a non-redex type application (M not a type abstraction) -/
theorem complete_tapp_non_tlam {M : Term} {τ : Ty} (h : ∀ M', M ≠ Term.tlam M') :
    complete (Term.tapp M τ) = Term.tapp (complete M) τ := by
  cases M with
  | var n => rfl
  | app M₁ M₂ => rfl
  | lam τ' M' => rfl
  | tlam M' => exact absurd rfl (h M')
  | tapp M' σ => rfl

/-! ## Inversion Lemmas -/

/-- Inversion for parallel reduction under lambda -/
theorem parRed_lam_inv {τ : Ty} {M M' : Term} (h : ParRed (Term.lam τ M) (Term.lam τ M')) : ParRed M M' := by
  cases h with
  | lam hBody => exact hBody

/-- Inversion for parallel reduction under type lambda -/
theorem parRed_tlam_inv {M M' : Term} (h : ParRed (Term.tlam M) (Term.tlam M')) : ParRed M M' := by
  cases h with
  | tlam hBody => exact hBody

/-! ## The Key Theorem: Parallel Reduction to Complete Development -/

/-- If M ⇒ N, then N ⇒ complete M.

    This is THE KEY LEMMA for Church-Rosser.
    It says that any parallel reduct of M can further reduce to M⁺. -/
theorem parRed_complete {M N : Term} (h : ParRed M N) : ParRed N (complete M) := by
  induction h with
  | var n =>
    exact ParRed.refl _
  | @lam τ M M' hBody ih =>
    simp only [complete_lam]
    exact ParRed.lam ih
  | @app M M' N N' hM hN ihM ihN =>
    cases M with
    | var n =>
      simp only [complete]
      exact ParRed.app ihM ihN
    | lam τ body =>
      cases hM with
      | lam hBody' =>
        simp only [complete]
        have hbody' : ParRed _ (complete body) := parRed_lam_inv ihM
        exact ParRed.beta hbody' ihN
    | app M₁ M₂ =>
      simp only [complete]
      exact ParRed.app ihM ihN
    | tlam body =>
      simp only [complete]
      exact ParRed.app ihM ihN
    | tapp M₁ σ =>
      simp only [complete]
      exact ParRed.app ihM ihN
  | @tlam M M' hBody ih =>
    simp only [complete_tlam]
    exact ParRed.tlam ih
  | @tapp M M' τ hM ih =>
    cases M with
    | var n =>
      simp only [complete]
      exact ParRed.tapp ih
    | lam τ' body =>
      simp only [complete]
      exact ParRed.tapp ih
    | app M₁ M₂ =>
      simp only [complete]
      exact ParRed.tapp ih
    | tlam body =>
      cases hM with
      | tlam hBody' =>
        simp only [complete]
        have hbody' : ParRed _ (complete body) := parRed_tlam_inv ih
        exact ParRed.tbeta hbody'
    | tapp M₁ σ =>
      simp only [complete]
      exact ParRed.tapp ih
  | @beta τ M M' N N' hM hN ihM ihN =>
    simp only [complete]
    exact ParRed.substTerm ihM ihN
  | @tbeta M M' τ hM ih =>
    simp only [complete]
    exact ParRed.substTypeInTerm τ ih

/-! ## Reflexivity of Parallel Reduction to Complete Development -/

/-- Every term parallel-reduces to its complete development -/
theorem parRed_to_complete (M : Term) : ParRed M (complete M) :=
  parRed_complete (ParRed.refl M)

end Metatheory.SystemF
