import Metatheory.STLCextBool.Typing
import Metatheory.Rewriting.Basic

/-!
# Call-by-Value Reduction for STLC with Booleans

Defines CBV reduction and proves determinism (hence confluence).
-/

namespace Metatheory.STLCextBool

open Term

/-! ## Call-by-Value Reduction -/

/-- Single-step call-by-value reduction. -/
inductive CBVStep : Term → Term → Prop where
  | beta : ∀ M V, IsValue V → CBVStep (app (lam M) V) (M[V])
  | appL : ∀ {M M' N}, CBVStep M M' → CBVStep (app M N) (app M' N)
  | appR : ∀ {V N N'}, IsValue V → CBVStep N N' → CBVStep (app V N) (app V N')
  | iteTrue : ∀ N₁ N₂, CBVStep (ite ttrue N₁ N₂) N₁
  | iteFalse : ∀ N₁ N₂, CBVStep (ite tfalse N₁ N₂) N₂
  | iteC : ∀ {M M' N₁ N₂}, CBVStep M M' → CBVStep (ite M N₁ N₂) (ite M' N₁ N₂)

/-- Notation for CBV reduction. -/
scoped infix:50 " →cbv " => CBVStep

namespace CBVStep

/-! ## Basic Properties -/

/-- Values do not step in CBV. -/
theorem value_no_step {V N : Term} (hV : IsValue V) : ¬(V →cbv N) := by
  intro h
  cases V with
  | var n => cases hV
  | app _ _ => cases hV
  | ite _ _ _ => cases hV
  | lam _ => cases h
  | ttrue => cases h
  | tfalse => cases h

/-- CBV is deterministic. -/
theorem deterministic {M N₁ N₂ : Term} (h1 : M →cbv N₁) (h2 : M →cbv N₂) : N₁ = N₂ := by
  induction h1 generalizing N₂ with
  | beta M V hV =>
    cases h2 with
    | beta M' V' hV' => rfl
    | appL h => cases h
    | appR hV' h => exact (value_no_step hV h).elim
  | appL hM ih =>
    cases h2 with
    | beta M' V' hV' => cases hM
    | appL hM' =>
      have h := ih hM'
      cases h
      rfl
    | appR hV' hN' => exact (value_no_step hV' hM).elim
  | appR hV hN ih =>
    cases h2 with
    | beta M' V' hV' => exact (value_no_step hV' hN).elim
    | appL hM' => exact (value_no_step hV hM').elim
    | appR hV' hN' =>
      have h := ih hN'
      cases h
      rfl
  | iteTrue N₁ N₂ =>
    cases h2 with
    | iteTrue _ _ => rfl
    | iteC h => cases h
  | iteFalse N₁ N₂ =>
    cases h2 with
    | iteFalse _ _ => rfl
    | iteC h => cases h
  | iteC hM ih =>
    cases h2 with
    | iteTrue _ _ => cases hM
    | iteFalse _ _ => cases hM
    | iteC hM' =>
      have h := ih hM'
      cases h
      rfl

end CBVStep

/-! ## Multi-Step CBV Reduction -/

/-- Multi-step CBV reduction (reflexive-transitive closure). -/
inductive CBVMultiStep : Term → Term → Prop where
  | refl : ∀ M, CBVMultiStep M M
  | step : ∀ {M N P}, CBVStep M N → CBVMultiStep N P → CBVMultiStep M P

/-- Notation for multi-step CBV reduction. -/
scoped infix:50 " →cbv* " => CBVMultiStep

namespace CBVMultiStep

/-- Single step implies multi-step. -/
theorem single {M N : Term} (h : M →cbv N) : M →cbv* N :=
  CBVMultiStep.step h (CBVMultiStep.refl N)

/-- Transitivity of multi-step CBV reduction. -/
theorem trans {M N P : Term} (h1 : M →cbv* N) (h2 : N →cbv* P) : M →cbv* P := by
  induction h1 with
  | refl => exact h2
  | step hstep _ ih => exact CBVMultiStep.step hstep (ih h2)

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

end CBVMultiStep

/-! ## Confluence via Determinism -/

/-- CBV reduction is deterministic. -/
theorem cbv_deterministic : Rewriting.Deterministic CBVStep := by
  intro M N₁ N₂ h1 h2
  exact CBVStep.deterministic h1 h2

/-- CBV reduction is confluent, since it is deterministic. -/
theorem cbv_confluent : Rewriting.Confluent CBVStep :=
  Rewriting.confluent_of_deterministic cbv_deterministic

/-! ## Typing and Safety for CBV -/

/-- CBV steps are also standard steps. -/
theorem cbv_to_step {M N : Term} (h : M →cbv N) : M ⟶ N := by
  induction h with
  | beta M V hV =>
    exact Step.beta M V
  | appL hM ih =>
    exact Step.appL ih
  | appR _ hN ih =>
    exact Step.appR ih
  | iteTrue N₁ N₂ =>
    exact Step.iteTrue N₁ N₂
  | iteFalse N₁ N₂ =>
    exact Step.iteFalse N₁ N₂
  | iteC hM ih =>
    exact Step.iteC ih

/-- CBV subject reduction: CBV steps preserve typing. -/
theorem subject_reduction_cbv {Γ : Context} {M N : Term} {A : Ty}
    (htype : Γ ⊢ M : A) (hstep : M →cbv N) : Γ ⊢ N : A :=
  subject_reduction htype (cbv_to_step hstep)

/-- Subject reduction for multi-step CBV. -/
theorem subject_reduction_cbv_multi {Γ : Context} {M N : Term} {A : Ty}
    (htype : Γ ⊢ M : A) (hsteps : M →cbv* N) : Γ ⊢ N : A := by
  induction hsteps with
  | refl => exact htype
  | step hstep _ ih => exact ih (subject_reduction_cbv htype hstep)

/-- Values are CBV-normal. -/
theorem isNormalForm_of_isValue {V : Term} (hV : IsValue V) : Rewriting.IsNormalForm CBVStep V := by
  intro N hstep
  exact CBVStep.value_no_step hV hstep

/-- CBV progress for closed, well-typed terms. -/
theorem progress_cbv {M : Term} {A : Ty} (htype : [] ⊢ M : A) :
    IsValue M ∨ ∃ N, M →cbv N := by
  match M with
  | Term.var n =>
    cases htype with
    | var h => cases h
  | Term.lam _ =>
    left
    exact trivial
  | Term.app M' N' =>
    cases htype with
    | app hfun harg =>
      have ihFun : IsValue M' ∨ ∃ N, M' →cbv N := progress_cbv hfun
      cases ihFun with
      | inl hvalFun =>
        obtain ⟨M'', hEq⟩ := canonical_forms_arr hfun hvalFun
        have ihArg : IsValue N' ∨ ∃ N, N' →cbv N := progress_cbv harg
        cases ihArg with
        | inl hvalArg =>
          right
          rw [hEq]
          exact ⟨_, CBVStep.beta M'' N' hvalArg⟩
        | inr hstepArg =>
          rcases hstepArg with ⟨N'', hstepArg⟩
          right
          exact ⟨_, CBVStep.appR hvalFun hstepArg⟩
      | inr hstepFun =>
        rcases hstepFun with ⟨M'', hstepFun⟩
        right
        exact ⟨_, CBVStep.appL hstepFun⟩
  | Term.ttrue =>
    left
    exact trivial
  | Term.tfalse =>
    left
    exact trivial
  | Term.ite M' N₁ N₂ =>
    cases htype with
    | ite hcond hthen helse =>
      have ihCond : IsValue M' ∨ ∃ N, M' →cbv N := progress_cbv hcond
      cases ihCond with
      | inl hvalCond =>
        have hbool := canonical_forms_bool hcond hvalCond
        cases hbool with
        | inl htrue =>
          right
          rw [htrue]
          exact ⟨_, CBVStep.iteTrue N₁ N₂⟩
        | inr hfalse =>
          right
          rw [hfalse]
          exact ⟨_, CBVStep.iteFalse N₁ N₂⟩
      | inr hstepCond =>
        rcases hstepCond with ⟨M'', hstepCond⟩
        right
        exact ⟨_, CBVStep.iteC hstepCond⟩

/-- CBV type safety: closed well-typed terms are values or can CBV step. -/
theorem cbv_type_safety {M N : Term} {A : Ty} (htype : [] ⊢ M : A) (hsteps : M →cbv* N) :
    IsValue N ∨ ∃ P, N →cbv P :=
  progress_cbv (subject_reduction_cbv_multi htype hsteps)

/-- CBV normal forms are unique (by determinism). -/
theorem cbv_normalForm_unique {M N₁ N₂ : Term}
    (h1 : M →cbv* N₁) (h2 : M →cbv* N₂)
    (hn1 : Rewriting.IsNormalForm CBVStep N₁) (hn2 : Rewriting.IsNormalForm CBVStep N₂) : N₁ = N₂ := by
  have h1' : Rewriting.Star CBVStep M N₁ := (CBVMultiStep.iff_star).1 h1
  have h2' : Rewriting.Star CBVStep M N₂ := (CBVMultiStep.iff_star).1 h2
  exact Rewriting.normalForm_unique_of_deterministic cbv_deterministic h1' h2' hn1 hn2

theorem cbv_normalForm_isValue {M N : Term} {A : Ty}
    (htype : [] ⊢ M : A) (hsteps : M →cbv* N) (hn : Rewriting.IsNormalForm CBVStep N) :
    IsValue N := by
  have hprog := cbv_type_safety htype hsteps
  cases hprog with
  | inl hval => exact hval
  | inr hstep =>
    rcases hstep with ⟨P, hstep⟩
    exact (hn _ hstep).elim

theorem cbv_normalForm_unique_of_isValue {V N₁ N₂ : Term}
    (h1 : V →cbv* N₁) (h2 : V →cbv* N₂) (hV : IsValue V) : N₁ = N₂ := by
  have hVnf : Rewriting.IsNormalForm CBVStep V := isNormalForm_of_isValue hV
  have hEq1 : V = N₁ := Rewriting.star_normalForm_eq (CBVMultiStep.toStar h1) hVnf
  have hEq2 : V = N₂ := Rewriting.star_normalForm_eq (CBVMultiStep.toStar h2) hVnf
  exact hEq1.symm.trans hEq2

/-! ## CBV Normalization -/

/-- Strong normalization for CBV reduction. -/
def CBVSN (M : Term) : Prop := Acc (fun a b => CBVStep b a) M

theorem cbvSn_intro {M : Term} (h : ∀ N, M →cbv N → CBVSN N) : CBVSN M :=
  Acc.intro M h

theorem cbvSn_of_step {M N : Term} (hM : CBVSN M) (h : M →cbv N) : CBVSN N :=
  Acc.inv hM h

theorem cbvSn_of_multi {M N : Term} (hM : CBVSN M) (h : M →cbv* N) : CBVSN N := by
  induction h with
  | refl => exact hM
  | step hstep _ ih =>
    exact ih (cbvSn_of_step hM hstep)

end Metatheory.STLCextBool
