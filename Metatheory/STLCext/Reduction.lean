/-
# Simply Typed Lambda Calculus with Products and Sums - Reduction

This module defines single-step reduction for the extended lambda calculus
with products and sums.

## Reduction Rules

### Beta Reduction (Lambda)
  (λM)N →β M[N]

### Product Reductions
  fst(pair M N) → M
  snd(pair M N) → N

### Sum Reductions
  case(inl V, N₁, N₂) → N₁[V]
  case(inr V, N₁, N₂) → N₂[V]

## References

- Pierce, "Types and Programming Languages" (2002), Chapters 11 and 12
-/

import Metatheory.STLCext.Terms

namespace Metatheory.STLCext

open Term

/-! ## Single-Step Reduction -/

/-- Single-step reduction for extended STLC.
    M → N means M reduces to N in exactly one step. -/
inductive Step : Term → Term → Prop where
  /-- Beta reduction: (λM)N → M[N] -/
  | beta : ∀ M N, Step (app (lam M) N) (M[N])
  /-- First projection: fst(pair M N) → M -/
  | fstPair : ∀ M N, Step (fst (pair M N)) M
  /-- Second projection: snd(pair M N) → N -/
  | sndPair : ∀ M N, Step (snd (pair M N)) N
  /-- Case on left injection: case(inl V, N₁, N₂) → N₁[V] -/
  | caseInl : ∀ V N₁ N₂, Step (case (inl V) N₁ N₂) (N₁[V])
  /-- Case on right injection: case(inr V, N₁, N₂) → N₂[V] -/
  | caseInr : ∀ V N₁ N₂, Step (case (inr V) N₁ N₂) (N₂[V])
  /-- Congruence: left of application -/
  | appL : ∀ {M M' N}, Step M M' → Step (app M N) (app M' N)
  /-- Congruence: right of application -/
  | appR : ∀ {M N N'}, Step N N' → Step (app M N) (app M N')
  /-- Congruence: under lambda -/
  | lam : ∀ {M M'}, Step M M' → Step (lam M) (lam M')
  /-- Congruence: left of pair -/
  | pairL : ∀ {M M' N}, Step M M' → Step (pair M N) (pair M' N)
  /-- Congruence: right of pair -/
  | pairR : ∀ {M N N'}, Step N N' → Step (pair M N) (pair M N')
  /-- Congruence: under fst -/
  | fst : ∀ {M M'}, Step M M' → Step (fst M) (fst M')
  /-- Congruence: under snd -/
  | snd : ∀ {M M'}, Step M M' → Step (snd M) (snd M')
  /-- Congruence: under inl -/
  | inl : ∀ {M M'}, Step M M' → Step (inl M) (inl M')
  /-- Congruence: under inr -/
  | inr : ∀ {M M'}, Step M M' → Step (inr M) (inr M')
  /-- Congruence: case scrutinee -/
  | caseS : ∀ {M M' N₁ N₂}, Step M M' → Step (case M N₁ N₂) (case M' N₁ N₂)
  /-- Congruence: case left branch -/
  | caseL : ∀ {M N₁ N₁' N₂}, Step N₁ N₁' → Step (case M N₁ N₂) (case M N₁' N₂)
  /-- Congruence: case right branch -/
  | caseR : ∀ {M N₁ N₂ N₂'}, Step N₂ N₂' → Step (case M N₁ N₂) (case M N₁ N₂')

/-- Notation for reduction -/
scoped infix:50 " ⟶ " => Step

namespace Step

/-! ## Basic Properties -/

/-- Beta reduction at root -/
theorem beta_root (M N : Term) : app (Term.lam M) N ⟶ M[N] := Step.beta M N

/-- First projection at root -/
theorem fst_root (M N : Term) : Term.fst (pair M N) ⟶ M := Step.fstPair M N

/-- Second projection at root -/
theorem snd_root (M N : Term) : Term.snd (pair M N) ⟶ N := Step.sndPair M N

/-- Case on inl at root -/
theorem caseInl_root (V N₁ N₂ : Term) : case (Term.inl V) N₁ N₂ ⟶ N₁[V] := Step.caseInl V N₁ N₂

/-- Case on inr at root -/
theorem caseInr_root (V N₁ N₂ : Term) : case (Term.inr V) N₁ N₂ ⟶ N₂[V] := Step.caseInr V N₁ N₂

end Step

/-! ## Multi-Step Reduction -/

/-- Multi-step reduction (reflexive transitive closure of Step) -/
inductive MultiStep : Term → Term → Prop where
  | refl : ∀ M, MultiStep M M
  | step : ∀ {M N P}, Step M N → MultiStep N P → MultiStep M P

/-- Notation for multi-step reduction -/
scoped infix:50 " ⟶* " => MultiStep

namespace MultiStep

/-- Single step implies multi-step -/
theorem single {M N : Term} (h : Step M N) : M ⟶* N :=
  MultiStep.step h (MultiStep.refl N)

/-- Transitivity of multi-step -/
theorem trans {M N P : Term} (h1 : M ⟶* N) (h2 : N ⟶* P) : M ⟶* P := by
  induction h1 with
  | refl => exact h2
  | step hMN _ ih => exact MultiStep.step hMN (ih h2)

/-- Congruence: application left -/
theorem appL {M M' N : Term} (h : M ⟶* M') : app M N ⟶* app M' N := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.appL hstep) ih

/-- Congruence: application right -/
theorem appR {M N N' : Term} (h : N ⟶* N') : app M N ⟶* app M N' := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.appR hstep) ih

/-- Congruence: lambda -/
theorem lam {M M' : Term} (h : M ⟶* M') : lam M ⟶* lam M' := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.lam hstep) ih

/-- Congruence: pair left -/
theorem pairL {M M' N : Term} (h : M ⟶* M') : pair M N ⟶* pair M' N := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.pairL hstep) ih

/-- Congruence: pair right -/
theorem pairR {M N N' : Term} (h : N ⟶* N') : pair M N ⟶* pair M N' := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.pairR hstep) ih

/-- Congruence: fst -/
theorem fst {M M' : Term} (h : M ⟶* M') : fst M ⟶* fst M' := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.fst hstep) ih

/-- Congruence: snd -/
theorem snd {M M' : Term} (h : M ⟶* M') : snd M ⟶* snd M' := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.snd hstep) ih

/-- Congruence: inl -/
theorem inl {M M' : Term} (h : M ⟶* M') : inl M ⟶* inl M' := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.inl hstep) ih

/-- Congruence: inr -/
theorem inr {M M' : Term} (h : M ⟶* M') : inr M ⟶* inr M' := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.inr hstep) ih

/-- Congruence: case scrutinee -/
theorem caseS {M M' N₁ N₂ : Term} (h : M ⟶* M') : case M N₁ N₂ ⟶* case M' N₁ N₂ := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.caseS hstep) ih

/-- Congruence: case left branch -/
theorem caseL {M N₁ N₁' N₂ : Term} (h : N₁ ⟶* N₁') : case M N₁ N₂ ⟶* case M N₁' N₂ := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.caseL hstep) ih

/-- Congruence: case right branch -/
theorem caseR {M N₁ N₂ N₂' : Term} (h : N₂ ⟶* N₂') : case M N₁ N₂ ⟶* case M N₁ N₂' := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.caseR hstep) ih

end MultiStep

/-! ## Compatibility Lemmas -/

/-- Substitution at any level preserves reduction -/
private theorem subst_preserves_step (j : Nat) {M M' N : Term} (hstep : Step M M') :
    Step (Term.subst j N M) (Term.subst j N M') := by
  induction hstep generalizing j N with
  | beta M₁ N₁ =>
    simp only [Term.subst]
    rw [← Term.subst_subst_gen]
    apply Step.beta
  | fstPair M₁ N₁ =>
    simp only [Term.subst]
    apply Step.fstPair
  | sndPair M₁ N₁ =>
    simp only [Term.subst]
    apply Step.sndPair
  | caseInl V N₁ N₂ =>
    simp only [Term.subst]
    rw [← Term.subst_subst_gen]
    apply Step.caseInl
  | caseInr V N₁ N₂ =>
    simp only [Term.subst]
    rw [← Term.subst_subst_gen]
    apply Step.caseInr
  | appL hstep ih =>
    simp only [Term.subst]
    apply Step.appL
    apply ih
  | appR hstep ih =>
    simp only [Term.subst]
    apply Step.appR
    apply ih
  | lam hstep ih =>
    simp only [Term.subst]
    apply Step.lam
    apply ih
  | pairL hstep ih =>
    simp only [Term.subst]
    apply Step.pairL
    apply ih
  | pairR hstep ih =>
    simp only [Term.subst]
    apply Step.pairR
    apply ih
  | fst hstep ih =>
    simp only [Term.subst]
    apply Step.fst
    apply ih
  | snd hstep ih =>
    simp only [Term.subst]
    apply Step.snd
    apply ih
  | inl hstep ih =>
    simp only [Term.subst]
    apply Step.inl
    apply ih
  | inr hstep ih =>
    simp only [Term.subst]
    apply Step.inr
    apply ih
  | caseS hstep ih =>
    simp only [Term.subst]
    apply Step.caseS
    apply ih
  | caseL hstep ih =>
    simp only [Term.subst]
    apply Step.caseL
    apply ih
  | caseR hstep ih =>
    simp only [Term.subst]
    apply Step.caseR
    apply ih

/-- Substitution preserves reduction in the substituted term -/
theorem subst0_step_left {M M' N : Term} (hstep : Step M M') :
    Step (M[N]) (M'[N]) := by
  unfold Term.subst0
  exact subst_preserves_step 0 hstep

/-- Helper: shift preserves reduction -/
private theorem shift_preserves_step (d : Nat) (c : Nat) {M M' : Term} (hstep : Step M M') :
    Step (Term.shift d c M) (Term.shift d c M') := by
  induction hstep generalizing c with
  | beta M N =>
    simp only [Term.shift, Term.subst0]
    rw [Term.shift_subst]
    apply Step.beta
  | fstPair M N =>
    simp only [Term.shift]
    apply Step.fstPair
  | sndPair M N =>
    simp only [Term.shift]
    apply Step.sndPair
  | caseInl V N₁ N₂ =>
    simp only [Term.shift, Term.subst0]
    rw [Term.shift_subst]
    apply Step.caseInl
  | caseInr V N₁ N₂ =>
    simp only [Term.shift, Term.subst0]
    rw [Term.shift_subst]
    apply Step.caseInr
  | appL _ ih =>
    simp only [Term.shift]
    apply Step.appL
    apply ih
  | appR _ ih =>
    simp only [Term.shift]
    apply Step.appR
    apply ih
  | lam _ ih =>
    simp only [Term.shift]
    apply Step.lam
    apply ih
  | pairL _ ih =>
    simp only [Term.shift]
    apply Step.pairL
    apply ih
  | pairR _ ih =>
    simp only [Term.shift]
    apply Step.pairR
    apply ih
  | fst _ ih =>
    simp only [Term.shift]
    apply Step.fst
    apply ih
  | snd _ ih =>
    simp only [Term.shift]
    apply Step.snd
    apply ih
  | inl _ ih =>
    simp only [Term.shift]
    apply Step.inl
    apply ih
  | inr _ ih =>
    simp only [Term.shift]
    apply Step.inr
    apply ih
  | caseS _ ih =>
    simp only [Term.shift]
    apply Step.caseS
    apply ih
  | caseL _ ih =>
    simp only [Term.shift]
    apply Step.caseL
    apply ih
  | caseR _ ih =>
    simp only [Term.shift]
    apply Step.caseR
    apply ih

/-- Substitution preserves reduction in argument (multi-step) -/
theorem subst0_step_right {M N N' : Term} (hstep : Step N N') :
    MultiStep (M[N]) (M[N']) := by
  suffices ∀ (j : Nat) (N N' M : Term), Step N N' →
      MultiStep (Term.subst j N M) (Term.subst j N' M) by
    exact this 0 N N' M hstep
  intro j N₀ N₀' M₀ hstep₀
  induction M₀ generalizing j N₀ N₀' with
  | var n =>
    simp only [Term.subst]
    by_cases h : n = j
    · simp only [h, ite_true]
      exact MultiStep.single hstep₀
    · simp only [h, ite_false]
      exact MultiStep.refl _
  | lam M ih =>
    simp only [Term.subst]
    have hshift := shift_preserves_step 1 0 hstep₀
    exact MultiStep.lam (ih (j + 1) (Term.shift1 N₀) (Term.shift1 N₀') hshift)
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [Term.subst]
    have h1 := ih₁ j N₀ N₀' hstep₀
    have h2 := ih₂ j N₀ N₀' hstep₀
    exact MultiStep.trans (MultiStep.appL h1) (MultiStep.appR h2)
  | pair M₁ M₂ ih₁ ih₂ =>
    simp only [Term.subst]
    have h1 := ih₁ j N₀ N₀' hstep₀
    have h2 := ih₂ j N₀ N₀' hstep₀
    exact MultiStep.trans (MultiStep.pairL h1) (MultiStep.pairR h2)
  | fst M ih =>
    simp only [Term.subst]
    exact MultiStep.fst (ih j N₀ N₀' hstep₀)
  | snd M ih =>
    simp only [Term.subst]
    exact MultiStep.snd (ih j N₀ N₀' hstep₀)
  | inl M ih =>
    simp only [Term.subst]
    exact MultiStep.inl (ih j N₀ N₀' hstep₀)
  | inr M ih =>
    simp only [Term.subst]
    exact MultiStep.inr (ih j N₀ N₀' hstep₀)
  | case M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp only [Term.subst]
    have hshift := shift_preserves_step 1 0 hstep₀
    have h0 := ihM j N₀ N₀' hstep₀
    have h1 := ihN₁ (j + 1) (Term.shift1 N₀) (Term.shift1 N₀') hshift
    have h2 := ihN₂ (j + 1) (Term.shift1 N₀) (Term.shift1 N₀') hshift
    exact MultiStep.trans (MultiStep.caseS h0) (MultiStep.trans (MultiStep.caseL h1) (MultiStep.caseR h2))
  | unit =>
    simp only [Term.subst]
    exact MultiStep.refl _

end Metatheory.STLCext
