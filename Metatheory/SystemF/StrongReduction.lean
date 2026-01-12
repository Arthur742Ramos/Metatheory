/-
# System F Strong (Full) Reduction

This module defines *full* β-reduction for System F, closed under all term
constructors (including under `lam` and `tlam`).

`Metatheory.SystemF.Term.Step` is a weak/evaluation relation used for progress.
For strong normalization we work with the full relation `StrongStep` here.
-/

import Metatheory.SystemF.Terms
import Metatheory.Rewriting.Basic

namespace Metatheory.SystemF

open Ty
open Term

/-! ## Full Reduction -/

/-- Full one-step β-reduction for System F (closed under `lam` and `tlam`). -/
inductive StrongStep : Term → Term → Prop where
  /-- Term β-reduction: (λx:τ. M) N → M[N/x]. -/
  | beta : ∀ τ M N, StrongStep (app (lam τ M) N) (substTerm0 N M)
  /-- Type β-reduction: (Λα. M) [τ] → M[τ/α]. -/
  | tbeta : ∀ M τ, StrongStep (tapp (tlam M) τ) (substTypeInTerm0 τ M)
  /-- Congruence: reduce under `lam`. -/
  | lam : ∀ {τ M M'}, StrongStep M M' → StrongStep (lam τ M) (lam τ M')
  /-- Congruence: application left. -/
  | appL : ∀ {M M' N}, StrongStep M M' → StrongStep (app M N) (app M' N)
  /-- Congruence: application right. -/
  | appR : ∀ {M N N'}, StrongStep N N' → StrongStep (app M N) (app M N')
  /-- Congruence: reduce under `tlam`. -/
  | tlam : ∀ {M M'}, StrongStep M M' → StrongStep (tlam M) (tlam M')
  /-- Congruence: type application. -/
  | tappL : ∀ {M M' τ}, StrongStep M M' → StrongStep (tapp M τ) (tapp M' τ)

/-- Notation for full one-step reduction. -/
scoped infix:50 " ⟶ₛ " => StrongStep

/-! ## Multi-step (Reflexive-Transitive Closure) -/

/-- Reflexive-transitive closure of `StrongStep`. -/
inductive StrongMultiStep : Term → Term → Prop where
  | refl : ∀ M, StrongMultiStep M M
  | step : ∀ {M N P}, (M ⟶ₛ N) → StrongMultiStep N P → StrongMultiStep M P

/-- Notation for full multi-step reduction. -/
scoped infix:50 " ⟶ₛ* " => StrongMultiStep

namespace StrongMultiStep

theorem single {M N : Term} (h : M ⟶ₛ N) : M ⟶ₛ* N :=
  StrongMultiStep.step h (StrongMultiStep.refl N)

theorem trans {M N P : Term} (h₁ : M ⟶ₛ* N) (h₂ : N ⟶ₛ* P) : M ⟶ₛ* P := by
  induction h₁ with
  | refl => exact h₂
  | step hstep _ ih => exact StrongMultiStep.step hstep (ih h₂)

theorem lam {τ : Ty} {M M' : Term} (h : M ⟶ₛ* M') : lam τ M ⟶ₛ* lam τ M' := by
  induction h with
  | refl => exact StrongMultiStep.refl _
  | step hstep _ ih => exact StrongMultiStep.step (StrongStep.lam hstep) ih

theorem tlam {M M' : Term} (h : M ⟶ₛ* M') : tlam M ⟶ₛ* tlam M' := by
  induction h with
  | refl => exact StrongMultiStep.refl _
  | step hstep _ ih => exact StrongMultiStep.step (StrongStep.tlam hstep) ih

theorem appL {M M' N : Term} (h : M ⟶ₛ* M') : app M N ⟶ₛ* app M' N := by
  induction h with
  | refl => exact StrongMultiStep.refl _
  | step hstep _ ih => exact StrongMultiStep.step (StrongStep.appL hstep) ih

theorem appR {M N N' : Term} (h : N ⟶ₛ* N') : app M N ⟶ₛ* app M N' := by
  induction h with
  | refl => exact StrongMultiStep.refl _
  | step hstep _ ih => exact StrongMultiStep.step (StrongStep.appR hstep) ih

theorem tappL {M M' : Term} {τ : Ty} (h : M ⟶ₛ* M') : tapp M τ ⟶ₛ* tapp M' τ := by
  induction h with
  | refl => exact StrongMultiStep.refl _
  | step hstep _ ih => exact StrongMultiStep.step (StrongStep.tappL hstep) ih

/-! ### Conversion to/from Rewriting.Star -/

/-- Convert Rewriting.Star to StrongMultiStep -/
theorem of_star {M N : Term} (h : Rewriting.Star StrongStep M N) : M ⟶ₛ* N := by
  induction h with
  | refl => exact StrongMultiStep.refl _
  | tail _ hstep ih => exact StrongMultiStep.trans ih (StrongMultiStep.single hstep)

/-- Convert StrongMultiStep to Rewriting.Star -/
theorem to_star {M N : Term} (h : M ⟶ₛ* N) : Rewriting.Star StrongStep M N := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | step hstep _ ih => exact Rewriting.Star.head hstep ih

end StrongMultiStep

/-! ## Strong Normalization -/

/-- Strong normalization for `StrongStep`. -/
def SN (M : Term) : Prop := Acc (fun a b => (b ⟶ₛ a)) M

theorem sn_intro {M : Term} (h : ∀ N, M ⟶ₛ N → SN N) : SN M :=
  Acc.intro M h

theorem sn_of_step {M N : Term} (hM : SN M) (h : M ⟶ₛ N) : SN N :=
  Acc.inv hM h

theorem sn_of_multi {M N : Term} (hM : SN M) (h : M ⟶ₛ* N) : SN N := by
  induction h with
  | refl => exact hM
  | step hstep hrest ih =>
    exact ih (sn_of_step hM hstep)

theorem sn_var (n : Nat) : SN (var n) := by
  constructor
  intro y hy
  cases hy

theorem sn_app_left {M N : Term} (h : SN (app M N)) : SN M := by
  have : ∀ T, SN T → ∀ M N, T = app M N → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M N hTeq
      subst hTeq
      apply sn_intro
      intro M' hM'
      exact ih (app M' N) (StrongStep.appL hM') M' N rfl
  exact this (app M N) h M N rfl

theorem sn_app_right {M N : Term} (h : SN (app M N)) : SN N := by
  have : ∀ T, SN T → ∀ M N, T = app M N → SN N := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M N hTeq
      subst hTeq
      apply sn_intro
      intro N' hN'
      exact ih (app M N') (StrongStep.appR hN') M N' rfl
  exact this (app M N) h M N rfl

theorem sn_tapp_left {M : Term} {τ : Ty} (h : SN (tapp M τ)) : SN M := by
  have : ∀ T, SN T → ∀ M τ, T = tapp M τ → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M τ hTeq
      subst hTeq
      apply sn_intro
      intro M' hM'
      exact ih (tapp M' τ) (StrongStep.tappL hM') M' τ rfl
  exact this (tapp M τ) h M τ rfl

theorem sn_lam_inv {τ : Ty} {M : Term} (h : SN (lam τ M)) : SN M := by
  have : ∀ T, SN T → ∀ τ M, T = lam τ M → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro τ M hTeq
      subst hTeq
      apply sn_intro
      intro M' hM'
      exact ih (lam τ M') (StrongStep.lam hM') τ M' rfl
  exact this (lam τ M) h τ M rfl

theorem sn_tlam_inv {M : Term} (h : SN (tlam M)) : SN M := by
  have : ∀ T, SN T → ∀ M, T = tlam M → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M hTeq
      subst hTeq
      apply sn_intro
      intro M' hM'
      exact ih (tlam M') (StrongStep.tlam hM') M' rfl
  exact this (tlam M) h M rfl

end Metatheory.SystemF
