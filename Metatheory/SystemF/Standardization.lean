/- 
# Standardization for System F

This module introduces a head/internal presentation of reduction for System F
and a standardization result: every strong reduction sequence can be viewed as a
standard sequence.

We use the existing strong reduction (`StrongStep`) and confluence/completion
infrastructure already developed for System F. The organization follows the
usual Curry-Feys/Takahashi split:

- head steps (root β-contractions),
- internal steps (contextual contractions),
- standard steps (head or internal),
- standardization map from strong multi-step reduction.
-/

import Metatheory.SystemF.Confluence
import Metatheory.Rewriting.Basic

namespace Metatheory.SystemF

open Ty Term

/-! ## Head Reduction (root β only) -/

/-- Head one-step reduction: contract only a root redex. -/
inductive HeadStep : Term → Term → Prop where
  /-- Root term-β reduction. -/
  | beta : ∀ τ M N, HeadStep (app (lam τ M) N) (substTerm0 N M)
  /-- Root type-β reduction. -/
  | tbeta : ∀ M τ, HeadStep (tapp (tlam M) τ) (substTypeInTerm0 τ M)

/-- Notation for head reduction. -/
scoped infix:50 " ⟶ₕ " => HeadStep

namespace HeadStep

/-- A head step is a strong step. -/
theorem toStrong {M N : Term} (h : M ⟶ₕ N) : M ⟶ₛ N := by
  cases h with
  | beta τ M N => exact StrongStep.beta τ M N
  | tbeta M τ => exact StrongStep.tbeta M τ

/-- A head step is a parallel reduction step. -/
theorem toParRed {M N : Term} (h : M ⟶ₕ N) : M ⇒ N :=
  ParRed.of_strongStep (toStrong h)

/-- A head step gives a strong multi-step. -/
theorem toStrongMulti {M N : Term} (h : M ⟶ₕ N) : M ⟶ₛ* N :=
  StrongMultiStep.single (toStrong h)

end HeadStep

/-- Reflexive-transitive closure of head reduction. -/
inductive HeadMultiStep : Term → Term → Prop where
  | refl : ∀ M, HeadMultiStep M M
  | step : ∀ {M N P}, HeadStep M N → HeadMultiStep N P → HeadMultiStep M P

/-- Notation for multi-step head reduction. -/
scoped infix:50 " ⟶ₕ* " => HeadMultiStep

namespace HeadMultiStep

theorem single {M N : Term} (h : M ⟶ₕ N) : M ⟶ₕ* N :=
  HeadMultiStep.step h (HeadMultiStep.refl N)

theorem trans {M N P : Term} (h₁ : M ⟶ₕ* N) (h₂ : N ⟶ₕ* P) : M ⟶ₕ* P := by
  induction h₁ with
  | refl => exact h₂
  | step hstep _ ih => exact HeadMultiStep.step hstep (ih h₂)

/-- Head multi-step reduction embeds into strong multi-step reduction. -/
theorem toStrongMulti {M N : Term} (h : M ⟶ₕ* N) : M ⟶ₛ* N := by
  induction h with
  | refl => exact StrongMultiStep.refl _
  | step hstep _ ih => exact StrongMultiStep.step (HeadStep.toStrong hstep) ih

end HeadMultiStep

/-! ## Internal Reduction -/

/-- Internal one-step reduction: contextual closure of strong reduction.

    This excludes direct root β-contractions and only contracts inside
    constructors. -/
inductive InternalStep : Term → Term → Prop where
  | lam : ∀ {τ M M'}, StrongStep M M' → InternalStep (lam τ M) (lam τ M')
  | appL : ∀ {M M' N}, StrongStep M M' → InternalStep (app M N) (app M' N)
  | appR : ∀ {M N N'}, StrongStep N N' → InternalStep (app M N) (app M N')
  | tlam : ∀ {M M'}, StrongStep M M' → InternalStep (tlam M) (tlam M')
  | tappL : ∀ {M M' τ}, StrongStep M M' → InternalStep (tapp M τ) (tapp M' τ)

/-- Notation for internal reduction. -/
scoped infix:50 " ⟶ᵢ " => InternalStep

namespace InternalStep

/-- Internal steps are strong steps. -/
theorem toStrong {M N : Term} (h : M ⟶ᵢ N) : M ⟶ₛ N := by
  cases h with
  | lam hM => exact StrongStep.lam hM
  | appL hM => exact StrongStep.appL hM
  | appR hN => exact StrongStep.appR hN
  | tlam hM => exact StrongStep.tlam hM
  | tappL hM => exact StrongStep.tappL hM

theorem toStrongMulti {M N : Term} (h : M ⟶ᵢ N) : M ⟶ₛ* N :=
  StrongMultiStep.single (toStrong h)

end InternalStep

/-- Reflexive-transitive closure of internal reduction. -/
inductive InternalMultiStep : Term → Term → Prop where
  | refl : ∀ M, InternalMultiStep M M
  | step : ∀ {M N P}, InternalStep M N → InternalMultiStep N P → InternalMultiStep M P

/-- Notation for internal reduction sequences. -/
scoped infix:50 " ⟶ᵢ* " => InternalMultiStep

namespace InternalMultiStep

theorem single {M N : Term} (h : M ⟶ᵢ N) : M ⟶ᵢ* N :=
  InternalMultiStep.step h (InternalMultiStep.refl N)

theorem trans {M N P : Term} (h₁ : M ⟶ᵢ* N) (h₂ : N ⟶ᵢ* P) : M ⟶ᵢ* P := by
  induction h₁ with
  | refl => exact h₂
  | step hstep _ ih => exact InternalMultiStep.step hstep (ih h₂)

/-- Internal reduction sequences embed into strong reduction sequences. -/
theorem toStrongMulti {M N : Term} (h : M ⟶ᵢ* N) : M ⟶ₛ* N := by
  induction h with
  | refl => exact StrongMultiStep.refl _
  | step hstep _ ih => exact StrongMultiStep.step (InternalStep.toStrong hstep) ih

end InternalMultiStep

/-! ## Standard Steps and Standard Sequences -/

/-- A standard step is either a head step or an internal step. -/
inductive StandardStep : Term → Term → Prop where
  | head : ∀ {M N}, HeadStep M N → StandardStep M N
  | internal : ∀ {M N}, InternalStep M N → StandardStep M N

/-- Notation for one standard step. -/
scoped infix:50 " ⟶ₛₜ " => StandardStep

namespace StandardStep

/-- Every standard step is a strong step. -/
theorem toStrong {M N : Term} (h : M ⟶ₛₜ N) : M ⟶ₛ N := by
  cases h with
  | head hHead => exact HeadStep.toStrong hHead
  | internal hInt => exact InternalStep.toStrong hInt

/-- Every strong step can be classified as standard. -/
theorem ofStrong {M N : Term} (h : M ⟶ₛ N) : M ⟶ₛₜ N := by
  cases h with
  | beta τ M N => exact StandardStep.head (HeadStep.beta τ M N)
  | tbeta M τ => exact StandardStep.head (HeadStep.tbeta M τ)
  | lam hM => exact StandardStep.internal (InternalStep.lam hM)
  | appL hM => exact StandardStep.internal (InternalStep.appL hM)
  | appR hN => exact StandardStep.internal (InternalStep.appR hN)
  | tlam hM => exact StandardStep.internal (InternalStep.tlam hM)
  | tappL hM => exact StandardStep.internal (InternalStep.tappL hM)

end StandardStep

/-- Reflexive-transitive closure of standard steps. -/
inductive StandardMultiStep : Term → Term → Prop where
  | refl : ∀ M, StandardMultiStep M M
  | step : ∀ {M N P}, StandardStep M N → StandardMultiStep N P → StandardMultiStep M P

/-- Notation for standard reduction sequences. -/
scoped infix:50 " ⟶ₛₜ* " => StandardMultiStep

namespace StandardMultiStep

theorem single {M N : Term} (h : M ⟶ₛₜ N) : M ⟶ₛₜ* N :=
  StandardMultiStep.step h (StandardMultiStep.refl N)

theorem trans {M N P : Term} (h₁ : M ⟶ₛₜ* N) (h₂ : N ⟶ₛₜ* P) : M ⟶ₛₜ* P := by
  induction h₁ with
  | refl => exact h₂
  | step hstep _ ih => exact StandardMultiStep.step hstep (ih h₂)

/-- Standard sequences embed into strong sequences. -/
theorem toStrongMulti {M N : Term} (h : M ⟶ₛₜ* N) : M ⟶ₛ* N := by
  induction h with
  | refl => exact StrongMultiStep.refl _
  | step hstep _ ih => exact StrongMultiStep.step (StandardStep.toStrong hstep) ih

/-- Any strong reduction sequence can be read as a standard sequence. -/
theorem ofStrongMulti {M N : Term} (h : M ⟶ₛ* N) : M ⟶ₛₜ* N := by
  induction h with
  | refl => exact StandardMultiStep.refl _
  | step hstep _ ih => exact StandardMultiStep.step (StandardStep.ofStrong hstep) ih

end StandardMultiStep

/-! ## Standard Form (Head prefix + Standard tail) -/

/-- A reduction is in standard form when presented as a head prefix
followed by a standard tail. -/
structure StandardForm (M N : Term) where
  pivot : Term
  headPrefix : M ⟶ₕ* pivot
  tail : pivot ⟶ₛₜ* N

/-- Every standard sequence yields a standard form decomposition. -/
def StandardForm.ofStandard {M N : Term} (h : M ⟶ₛₜ* N) : StandardForm M N :=
  ⟨M, HeadMultiStep.refl M, h⟩

/-- Convert a standard form decomposition back to strong reduction. -/
theorem StandardForm.toStrongMulti {M N : Term} (h : StandardForm M N) : M ⟶ₛ* N := by
  rcases h with ⟨P, hHead, hTail⟩
  exact StrongMultiStep.trans (HeadMultiStep.toStrongMulti hHead) (StandardMultiStep.toStrongMulti hTail)

/-! ## Curry-Feys / Takahashi Style Bridge Lemmas -/

/-- Curry-Feys peak completion: a head step and a strong step from the same
source are joinable in strong multi-step reduction. -/
theorem curry_feys_peak {M N P : Term} (hHead : M ⟶ₕ N) (hStrong : M ⟶ₛ P) :
    ∃ Q, (N ⟶ₛ* Q) ∧ (P ⟶ₛ* Q) :=
  confluence (HeadStep.toStrongMulti hHead) (StrongMultiStep.single hStrong)

/-- Curry-Feys strip: a head step can be pushed against any strong reduction
sequence by confluence. -/
theorem curry_feys_strip {M N P : Term} (hHead : M ⟶ₕ N) (hStrong : M ⟶ₛ* P) :
    ∃ Q, (N ⟶ₛ* Q) ∧ (P ⟶ₛ* Q) :=
  confluence (HeadStep.toStrongMulti hHead) hStrong

/-- Takahashi-style target lemma for one head step: every head contractum
reduces to the complete development of the source term. -/
theorem headStep_to_complete {M N : Term} (h : M ⟶ₕ N) : N ⟶ₛ* complete M := by
  have hPar : M ⇒ N := HeadStep.toParRed h
  have hComp : N ⇒ complete M := parRed_complete hPar
  exact ParRed.toStrongMulti hComp

/-! ## Standardization Theorem -/

/-- Standardization (Curry-Feys/Takahashi style):
every strong reduction sequence can be represented by a standard sequence. -/
theorem standardization {M N : Term} (h : M ⟶ₛ* N) : M ⟶ₛₜ* N :=
  StandardMultiStep.ofStrongMulti h

/-- Standardization packaged with an explicit standard-form decomposition. -/
def standardization_form {M N : Term} (h : M ⟶ₛ* N) : StandardForm M N :=
  StandardForm.ofStandard (standardization h)

/-! ## Leftmost (Standard) Reduction is Normalizing -/

/-- Leftmost one-step reduction (identified here with standard steps). -/
abbrev LeftmostStep : Term → Term → Prop := StandardStep

/-- Leftmost multi-step reduction. -/
abbrev LeftmostMultiStep : Term → Term → Prop := StandardMultiStep

scoped infix:50 " ⟶ₗ " => LeftmostStep
scoped infix:50 " ⟶ₗ* " => LeftmostMultiStep

/-- Strong normalizability by strong reduction to a normal form. -/
def StrongNormalizing (M : Term) : Prop :=
  ∃ N, (M ⟶ₛ* N) ∧ IsStrongNormalForm N

/-- Leftmost normalizability by leftmost reduction to a normal form. -/
def LeftmostNormalizing (M : Term) : Prop :=
  ∃ N, (M ⟶ₗ* N) ∧ IsStrongNormalForm N

/-- Any strong normalizing term is leftmost normalizing. -/
theorem leftmost_normalizing_of_strong_normalizing {M : Term} :
    StrongNormalizing M → LeftmostNormalizing M := by
  intro h
  rcases h with ⟨N, hMN, hN⟩
  exact ⟨N, standardization hMN, hN⟩

/-- If a specific strong reduction reaches a normal form, a leftmost/standard
reduction also reaches a normal form (same target). -/
theorem leftmost_reduction_normalizing {M N : Term}
    (hMN : M ⟶ₛ* N) (hN : IsStrongNormalForm N) :
    ∃ P, (M ⟶ₗ* P) ∧ IsStrongNormalForm P :=
  ⟨N, standardization hMN, hN⟩

/-- Leftmost reduction sequences are sound w.r.t. strong reduction. -/
theorem leftmost_to_strong {M N : Term} (h : M ⟶ₗ* N) : M ⟶ₛ* N :=
  StandardMultiStep.toStrongMulti h

end Metatheory.SystemF
