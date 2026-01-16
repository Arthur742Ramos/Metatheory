import Metatheory.STLCext.Parallel

/-!
# Complete Development for Extended STLC

This module defines complete development for STLC with products and sums.
It is used to prove the diamond property for parallel reduction.

## Key Lemma

If M ⇒ N, then N ⇒ complete M.

This yields diamond: N₁ ⇒ complete M and N₂ ⇒ complete M.

## References

- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
- Pierce, "Types and Programming Languages" (2002), Chapters 11-12
-/

namespace Metatheory.STLCext

open Term

/-! ## Complete Development -/

/-- Complete development: reduce all redexes in a term. -/
def complete : Term → Term
  | var n => var n
  | lam M => lam (complete M)
  | app (lam M) N => (complete M)[complete N]
  | app M N => app (complete M) (complete N)
  | pair M N => pair (complete M) (complete N)
  | fst (pair M _) => complete M
  | fst M => fst (complete M)
  | snd (pair _ N) => complete N
  | snd M => snd (complete M)
  | inl M => inl (complete M)
  | inr M => inr (complete M)
  | case (inl V) N₁ _ => (complete N₁)[complete V]
  | case (inr V) _ N₂ => (complete N₂)[complete V]
  | case M N₁ N₂ => case (complete M) (complete N₁) (complete N₂)
  | unit => unit

/-! ## Basic Properties -/

@[simp] theorem complete_var (n : Nat) : complete (var n) = var n := rfl
@[simp] theorem complete_lam (M : Term) : complete (lam M) = lam (complete M) := rfl
@[simp] theorem complete_beta (M N : Term) : complete (app (lam M) N) = (complete M)[complete N] := rfl
@[simp] theorem complete_fst_pair (M N : Term) : complete (fst (pair M N)) = complete M := rfl
@[simp] theorem complete_snd_pair (M N : Term) : complete (snd (pair M N)) = complete N := rfl
@[simp] theorem complete_case_inl (V N₁ N₂ : Term) :
    complete (case (inl V) N₁ N₂) = (complete N₁)[complete V] := rfl
@[simp] theorem complete_case_inr (V N₁ N₂ : Term) :
    complete (case (inr V) N₁ N₂) = (complete N₂)[complete V] := rfl

/-! ## Diamond Property via Complete Development -/

/-- Inversion for inl under parallel reduction. -/
theorem par_inl_inv {M M' : Term} (h : inl M ⇒ inl M') : M ⇒ M' := by
  cases h with
  | inl h' => exact h'

/-- Inversion for inr under parallel reduction. -/
theorem par_inr_inv {M M' : Term} (h : inr M ⇒ inr M') : M ⇒ M' := by
  cases h with
  | inr h' => exact h'

/-- Inversion for pairs under parallel reduction. -/
theorem par_pair_inv {M M' N N' : Term} (h : pair M N ⇒ pair M' N') : M ⇒ M' ∧ N ⇒ N' := by
  cases h with
  | pair hM hN => exact ⟨hM, hN⟩

/-- If M ⇒ N, then N ⇒ complete M. -/
theorem par_complete {M N : Term} (h : M ⇒ N) : N ⇒ complete M := by
  induction h with
  | var n =>
    exact ParRed.refl _
  | lam hM ih =>
    exact ParRed.lam ih
  | app hM hN ihM ihN =>
    cases hM with
    | var n =>
      simp [complete]
      exact ParRed.app ihM ihN
    | app _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | lam hBody =>
      simp [complete]
      exact ParRed.beta (by
        cases ihM with
        | lam ihBody => exact ihBody
        | _ => exact ParRed.refl _) ihN
    | beta _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | pair _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | fst _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | snd _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | inl _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | inr _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | case _ _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | fstPair _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | sndPair _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | caseInl _ _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | caseInr _ _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | unit =>
      simp [complete]
      exact ParRed.app ihM ihN
  | pair hM hN ihM ihN =>
    simp [complete]
    exact ParRed.pair ihM ihN
  | fst hM ih =>
    cases hM with
    | pair hM hN =>
      simp [complete]
      have hpair := par_pair_inv ih
      exact ParRed.fstPair hpair.1 hpair.2
    | _ =>
      simp [complete]
      exact ParRed.fst ih
  | snd hM ih =>
    cases hM with
    | pair hM hN =>
      simp [complete]
      have hpair := par_pair_inv ih
      exact ParRed.sndPair hpair.1 hpair.2
    | _ =>
      simp [complete]
      exact ParRed.snd ih
  | inl hM ih =>
    simp [complete]
    exact ParRed.inl ih
  | inr hM ih =>
    simp [complete]
    exact ParRed.inr ih
  | case hM hN₁ hN₂ ihM ihN₁ ihN₂ =>
    cases hM with
    | inl hV =>
      simp [complete]
      exact ParRed.caseInl (par_inl_inv ihM) ihN₁ ihN₂
    | inr hV =>
      simp [complete]
      exact ParRed.caseInr (par_inr_inv ihM) ihN₁ ihN₂
    | _ =>
      simp [complete]
      exact ParRed.case ihM ihN₁ ihN₂
  | beta hM hN ihM ihN =>
    simp [complete]
    exact ParRed.subst ihM ihN
  | fstPair hM hN ihM ihN =>
    simp [complete]
    exact ihM
  | sndPair hM hN ihM ihN =>
    simp [complete]
    exact ihN
  | caseInl hV hN₁ hN₂ ihV ihN₁ ihN₂ =>
    simp [complete]
    exact ParRed.subst ihN₁ ihV
  | caseInr hV hN₁ hN₂ ihV ihN₁ ihN₂ =>
    simp [complete]
    exact ParRed.subst ihN₂ ihV
  | unit =>
    simp [complete]
    exact ParRed.unit

/-- Parallel reduction satisfies diamond. -/
theorem diamond {M N₁ N₂ : Term} (h1 : M ⇒ N₁) (h2 : M ⇒ N₂) :
    ∃ P, (N₁ ⇒ P) ∧ (N₂ ⇒ P) :=
  ⟨complete M, par_complete h1, par_complete h2⟩

end Metatheory.STLCext
