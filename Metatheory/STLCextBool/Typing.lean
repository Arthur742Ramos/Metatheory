/-
# Simply Typed Lambda Calculus with Booleans - Typing

This module defines typing for STLC with booleans and proves
subject reduction and progress.

## References

- Pierce, "Types and Programming Languages" (2002), Chapter 11
-/

import Metatheory.STLCextBool.Reduction

namespace Metatheory.STLCextBool

/-! ## Typing Contexts -/

/-- A typing context is a list of types (de Bruijn indexed). -/
abbrev Context := List Ty

/-! ## Typing Relation -/

/-- Typing judgment: Γ ⊢ M : A. -/
inductive HasType : Context → Term → Ty → Prop where
  | var : ∀ {Γ : Context} {n : Nat} {A : Ty},
      Γ[n]? = some A →
      HasType Γ (Term.var n) A
  | lam : ∀ {Γ : Context} {M : Term} {A B : Ty},
      HasType (A :: Γ) M B →
      HasType Γ (Term.lam M) (A ⇒ B)
  | app : ∀ {Γ : Context} {M N : Term} {A B : Ty},
      HasType Γ M (A ⇒ B) →
      HasType Γ N A →
      HasType Γ (Term.app M N) B
  | ttrue : ∀ {Γ : Context},
      HasType Γ Term.ttrue Ty.bool
  | tfalse : ∀ {Γ : Context},
      HasType Γ Term.tfalse Ty.bool
  | ite : ∀ {Γ : Context} {M N₁ N₂ : Term} {A : Ty},
      HasType Γ M Ty.bool →
      HasType Γ N₁ A →
      HasType Γ N₂ A →
      HasType Γ (Term.ite M N₁ N₂) A

/-- Notation for typing judgment. -/
scoped notation:50 Γ " ⊢ " M " : " A => HasType Γ M A

/-! ## Basic Typing Examples -/

/-- Conditional selects the left branch at bool. -/
theorem ite_typed {A : Ty} {M N : Term}
    (hM : [A] ⊢ M : A) (hN : [A] ⊢ N : A) : [A] ⊢ Term.ite Term.ttrue M N : A := by
  apply HasType.ite
  · exact HasType.ttrue
  · exact hM
  · exact hN

/-! ## Weakening -/

/-- Weakening: if Γ ⊢ M : A and we preserve context lookups, then Γ' ⊢ M : A. -/
theorem weakening : ∀ {Γ Γ' : Context} {M : Term} {A : Ty},
    HasType Γ M A →
    (∀ (n : Nat) (B : Ty), Γ[n]? = some B → Γ'[n]? = some B) →
    HasType Γ' M A := by
  intro Γ Γ' M A htype hpres
  induction htype generalizing Γ' with
  | var hget =>
    exact HasType.var (hpres _ _ hget)
  | lam hbody ih =>
    apply HasType.lam
    apply ih
    intro n B hget
    cases n with
    | zero => exact hget
    | succ n' => exact hpres n' B hget
  | app hfun harg ihfun iharg =>
    exact HasType.app (ihfun hpres) (iharg hpres)
  | ttrue => exact HasType.ttrue
  | tfalse => exact HasType.tfalse
  | ite hcond hthen helse ihcond ihthen ihelse =>
    exact HasType.ite (ihcond hpres) (ihthen hpres) (ihelse hpres)

/-! ## Shift Typing -/

/-- Helper lemma for get? on appended lists. -/
theorem get?_append_of_lt {α : Type} (l₁ l₂ : List α) (n : Nat) (h : n < l₁.length) :
    (l₁ ++ l₂)[n]? = l₁[n]? := by
  simp [List.getElem?_append_left h]

/-- Helper lemma for get? on appended lists (right side). -/
theorem get?_append_of_ge {α : Type} (l₁ l₂ : List α) (n : Nat) (h : n ≥ l₁.length) :
    (l₁ ++ l₂)[n]? = l₂[n - l₁.length]? := by
  simp [List.getElem?_append_right h]

/-- Helper: shift typing with explicit context equality. -/
theorem typing_shift_at_aux {Γ Γ₁ Γ₂ : Context} {M : Term} {A B : Ty}
    (hΓ : Γ = Γ₁ ++ Γ₂)
    (h : HasType Γ M A) :
    HasType (Γ₁ ++ [B] ++ Γ₂) (Term.shift 1 Γ₁.length M) A := by
  induction h generalizing Γ₁ Γ₂ with
  | @var Γ' n A' hget =>
    simp [Term.shift]
    by_cases hn : n < Γ₁.length
    · simp [hn]
      apply HasType.var
      have h1 : n < (Γ₁ ++ [B]).length := by simp; omega
      have hcons : (Γ₁ ++ B :: Γ₂)[n]? = (Γ₁ ++ [B] ++ Γ₂)[n]? := by
        simp
      rw [hcons]
      rw [get?_append_of_lt (Γ₁ ++ [B]) Γ₂ n h1]
      rw [get?_append_of_lt Γ₁ [B] n hn]
      rw [hΓ, get?_append_of_lt Γ₁ Γ₂ n hn] at hget
      exact hget
    · simp [hn]
      apply HasType.var
      have hge : n ≥ Γ₁.length := Nat.le_of_not_lt hn
      rw [hΓ] at hget
      rw [get?_append_of_ge Γ₁ Γ₂ n hge] at hget
      have h1 : n + 1 ≥ (Γ₁ ++ [B]).length := by simp; omega
      have hcons : (Γ₁ ++ B :: Γ₂)[n + 1]? = (Γ₁ ++ [B] ++ Γ₂)[n + 1]? := by
        simp
      rw [hcons]
      rw [get?_append_of_ge (Γ₁ ++ [B]) Γ₂ (n + 1) h1]
      simp only [List.length_append, List.length_singleton]
      have heq : n + 1 - (Γ₁.length + 1) = n - Γ₁.length := by omega
      rw [heq]
      exact hget
  | @lam Γ' M' A' B' hbody ih =>
    simp only [Term.shift]
    apply HasType.lam
    have hΓ' : A' :: Γ' = (A' :: Γ₁) ++ Γ₂ := by rw [hΓ]; rfl
    have ih' := ih hΓ'
    simp only [List.cons_append, List.length_cons] at ih'
    exact ih'
  | @app Γ' M' N' A' B' hfun harg ihfun iharg =>
    simp only [Term.shift]
    exact HasType.app (ihfun hΓ) (iharg hΓ)
  | ttrue =>
    simp only [Term.shift]
    exact HasType.ttrue
  | tfalse =>
    simp only [Term.shift]
    exact HasType.tfalse
  | @ite Γ' M' N₁ N₂ A' hcond hthen helse ihcond ihthen ihelse =>
    simp only [Term.shift]
    exact HasType.ite (ihcond hΓ) (ihthen hΓ) (ihelse hΓ)

/-- Shifting preserves typing. -/
theorem typing_shift {Γ : Context} {N : Term} {A B : Ty}
    (h : HasType Γ N A) :
    HasType (B :: Γ) (Term.shift 1 0 N) A := by
  have h' := @typing_shift_at_aux Γ [] Γ N A B (by simp) h
  simp at h'
  exact h'

/-! ## Substitution Typing -/

/-- Helper for substitution typing. -/
theorem substitution_typing_gen_aux {Γ : Context} {M : Term} {B : Ty}
    (hM : HasType Γ M B) :
    ∀ {Γ₁ Γ₂ : Context} {N : Term} {A : Ty} (j : Nat),
    Γ = Γ₁ ++ [A] ++ Γ₂ →
    j = Γ₁.length →
    HasType (Γ₁ ++ Γ₂) N A →
    HasType (Γ₁ ++ Γ₂) (Term.subst j N M) B := by
  induction hM with
  | @var Γ' n A' hget =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp [Term.subst]
    by_cases hn_eq : n = j
    · simp [hn_eq]
      subst hn_eq
      rw [hΓ] at hget
      rw [hj] at hget
      have h1 : Γ₁.length < (Γ₁ ++ [A]).length := by simp
      rw [get?_append_of_lt (Γ₁ ++ [A]) Γ₂ Γ₁.length h1] at hget
      have h2 : Γ₁.length ≥ Γ₁.length := Nat.le_refl _
      rw [get?_append_of_ge Γ₁ [A] Γ₁.length h2] at hget
      simp at hget
      cases hget
      exact hN
    · by_cases hn_gt : n > j
      · simp [hn_eq, hn_gt]
        apply HasType.var
        rw [hΓ] at hget
        rw [hj] at hn_gt
        have hn_ge : n ≥ (Γ₁ ++ [A]).length := by simp; omega
        rw [get?_append_of_ge (Γ₁ ++ [A]) Γ₂ n hn_ge] at hget
        simp at hget
        have hn_ge' : n - 1 ≥ Γ₁.length := by omega
        rw [get?_append_of_ge Γ₁ Γ₂ (n - 1) hn_ge']
        have : n - 1 - Γ₁.length = n - Γ₁.length - 1 := by omega
        rw [this]
        exact hget
      · have hn_lt : n < j := by omega
        simp [hn_eq, hn_gt]
        apply HasType.var
        rw [hΓ] at hget
        rw [hj] at hn_lt
        have h1 : n < (Γ₁ ++ [A]).length := by simp; omega
        rw [get?_append_of_lt (Γ₁ ++ [A]) Γ₂ n h1] at hget
        have h2 : n < Γ₁.length := hn_lt
        rw [get?_append_of_lt Γ₁ [A] n h2] at hget
        rw [get?_append_of_lt Γ₁ Γ₂ n h2]
        exact hget
  | @lam Γ' M' A' B' hbody ih =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp [Term.subst]
    apply HasType.lam
    have h1 : (A' :: Γ₁) ++ [A] ++ Γ₂ = A' :: (Γ₁ ++ [A] ++ Γ₂) := by simp
    have h2 : (A' :: Γ₁) ++ Γ₂ = A' :: (Γ₁ ++ Γ₂) := by simp
    have hΓ' : A' :: Γ' = (A' :: Γ₁) ++ [A] ++ Γ₂ := by rw [hΓ]; exact h1
    have hN' : HasType ((A' :: Γ₁) ++ Γ₂) (Term.shift1 N) A := by
      rw [h2]
      exact typing_shift hN
    have hj' : j + 1 = (A' :: Γ₁).length := by simp [hj]
    have ih' := @ih (A' :: Γ₁) Γ₂ (Term.shift1 N) A (j + 1) hΓ' hj' hN'
    rw [h2] at ih'
    exact ih'
  | @app Γ' M₁ N₁ A' B' hfun harg ihfun iharg =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp [Term.subst]
    exact HasType.app (@ihfun Γ₁ Γ₂ N A j hΓ hj hN) (@iharg Γ₁ Γ₂ N A j hΓ hj hN)
  | ttrue =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp [Term.subst]
    exact HasType.ttrue
  | tfalse =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp [Term.subst]
    exact HasType.tfalse
  | @ite Γ' M' N₁ N₂ A' hcond hthen helse ihcond ihthen ihelse =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp [Term.subst]
    exact HasType.ite (@ihcond Γ₁ Γ₂ N A j hΓ hj hN) (@ihthen Γ₁ Γ₂ N A j hΓ hj hN) (@ihelse Γ₁ Γ₂ N A j hΓ hj hN)

/-- Substitution preserves typing. -/
theorem substitution_typing {Γ : Context} {M N : Term} {A B : Ty}
    (hM : HasType (A :: Γ) M B) (hN : HasType Γ N A) :
    HasType Γ (Term.subst0 N M) B := by
  unfold Term.subst0
  have hM' : HasType ([] ++ [A] ++ Γ) M B := by simp; exact hM
  have hN' : HasType ([] ++ Γ) N A := by simp; exact hN
  have h := @substitution_typing_gen_aux ([] ++ [A] ++ Γ) M B hM' [] Γ N A 0 (by simp) (by simp) hN'
  simp at h
  exact h

/-! ## Subject Reduction -/

/-- Subject reduction: reduction preserves typing. -/
theorem subject_reduction {Γ : Context} {M N : Term} {A : Ty}
    (htype : Γ ⊢ M : A) (hstep : M ⟶ N) : Γ ⊢ N : A := by
  induction hstep generalizing Γ A with
  | beta M' N' =>
    cases htype with
    | app hfun harg =>
      cases hfun with
      | lam hbody =>
        exact substitution_typing hbody harg
  | iteTrue N₁ N₂ =>
    cases htype with
    | ite _ hthen _ => exact hthen
  | iteFalse N₁ N₂ =>
    cases htype with
    | ite _ _ helse => exact helse
  | appL hstep ih =>
    cases htype with
    | app hfun harg => exact HasType.app (ih hfun) harg
  | appR hstep ih =>
    cases htype with
    | app hfun harg => exact HasType.app hfun (ih harg)
  | lamStep hstep ih =>
    cases htype with
    | lam hbody => exact HasType.lam (ih hbody)
  | iteC hstep ih =>
    cases htype with
    | ite hcond hthen helse => exact HasType.ite (ih hcond) hthen helse
  | iteT hstep ih =>
    cases htype with
    | ite hcond hthen helse => exact HasType.ite hcond (ih hthen) helse
  | iteF hstep ih =>
    cases htype with
    | ite hcond hthen helse => exact HasType.ite hcond hthen (ih helse)

/-- Subject reduction for multi-step reduction. -/
theorem subject_reduction_multi {Γ : Context} {M N : Term} {A : Ty}
    (htype : Γ ⊢ M : A) (hsteps : MultiStep M N) : Γ ⊢ N : A := by
  induction hsteps with
  | refl => exact htype
  | step hstep _ ih => exact ih (subject_reduction htype hstep)

/-! ## Progress -/

/-- Values for the boolean calculus. -/
def IsValue : Term → Prop
  | Term.lam _ => True
  | Term.ttrue => True
  | Term.tfalse => True
  | _ => False

/-- Canonical forms for arrow types. -/
theorem canonical_forms_arr {M : Term} {A B : Ty}
    (htype : [] ⊢ M : A ⇒ B) (hval : IsValue M) :
    ∃ M', M = Term.lam M' := by
  cases M with
  | var n => cases htype with | var h => cases h
  | lam M' => exact ⟨M', rfl⟩
  | app _ _ => cases hval
  | ttrue => cases htype
  | tfalse => cases htype
  | ite _ _ _ => cases hval

/-- Canonical forms for boolean type. -/
theorem canonical_forms_bool {M : Term}
    (htype : [] ⊢ M : Ty.bool) (hval : IsValue M) :
    M = Term.ttrue ∨ M = Term.tfalse := by
  cases M with
  | var n => cases htype with | var h => cases h
  | lam _ => cases htype
  | app _ _ => cases hval
  | ttrue => exact Or.inl rfl
  | tfalse => exact Or.inr rfl
  | ite _ _ _ => cases hval

/-- Progress: a closed well-typed term is a value or can step. -/
theorem progress {M : Term} {A : Ty} (htype : [] ⊢ M : A) :
    IsValue M ∨ ∃ N, Step M N := by
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
      have ihfun : IsValue M' ∨ ∃ N, Step M' N := progress hfun
      cases ihfun with
      | inl hval =>
        obtain ⟨M'', hEq⟩ := canonical_forms_arr hfun hval
        right
        rw [hEq]
        exact ⟨Term.subst0 N' M'', Step.beta _ _⟩
      | inr hstep =>
        obtain ⟨M'', hstep'⟩ := hstep
        right
        exact ⟨Term.app M'' N', Step.appL hstep'⟩
  | Term.ttrue =>
    left
    exact trivial
  | Term.tfalse =>
    left
    exact trivial
  | Term.ite M' N₁ N₂ =>
    cases htype with
    | ite hcond hthen helse =>
      have ihcond : IsValue M' ∨ ∃ N, Step M' N := progress hcond
      cases ihcond with
      | inl hval =>
        have hbool := canonical_forms_bool hcond hval
        cases hbool with
        | inl htrue =>
          right
          rw [htrue]
          exact ⟨N₁, Step.iteTrue _ _⟩
        | inr hfalse =>
          right
          rw [hfalse]
          exact ⟨N₂, Step.iteFalse _ _⟩
      | inr hstep =>
        obtain ⟨M'', hstep'⟩ := hstep
        right
        exact ⟨Term.ite M'' N₁ N₂, Step.iteC hstep'⟩

/-! ## Examples -/

/-- if true then false else true has type Bool. -/
example : [] ⊢ Term.ite Term.ttrue Term.tfalse Term.ttrue : Ty.bool := by
  apply HasType.ite
  · exact HasType.ttrue
  · exact HasType.tfalse
  · exact HasType.ttrue

end Metatheory.STLCextBool
