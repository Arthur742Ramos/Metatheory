/-
# Simply Typed Lambda Calculus - Typing

This module defines typing contexts and the typing relation for STLC.

## Overview

- Contexts are lists of types (de Bruijn style)
- The typing judgment Γ ⊢ M : A assigns types to terms
- Well-typed terms enjoy subject reduction (types preserved under reduction)

## References

- Pierce, "Types and Programming Languages" (2002)
- Barendregt, "Lambda Calculi with Types" (1992)
-/

import Metatheory.STLC.Terms

namespace Metatheory.STLC

/-! ## Typing Contexts -/

/-- A typing context is a list of types (de Bruijn indexed) -/
abbrev Context := List Ty

/-! ## Typing Relation -/

/-- Typing judgment: Γ ⊢ M : A

    In de Bruijn representation:
    - var n has type Γ[n] if n < |Γ|
    - lam M has type A ⇒ B if (A :: Γ) ⊢ M : B
    - app M N has type B if Γ ⊢ M : A ⇒ B and Γ ⊢ N : A -/
inductive HasType : Context → Term → Ty → Prop where
  | var : ∀ {Γ : Context} {n : Nat} {A : Ty},
      Γ[n]? = some A →
      HasType Γ (Lambda.Term.var n) A
  | lam : ∀ {Γ : Context} {M : Term} {A B : Ty},
      HasType (A :: Γ) M B →
      HasType Γ (Lambda.Term.lam M) (A ⇒ B)
  | app : ∀ {Γ : Context} {M N : Term} {A B : Ty},
      HasType Γ M (A ⇒ B) →
      HasType Γ N A →
      HasType Γ (Lambda.Term.app M N) B

/-- Notation for typing judgment -/
scoped notation:50 Γ " ⊢ " M " : " A => HasType Γ M A

/-! ## Basic Typing Examples -/

/-- The identity function λx.x has type A ⇒ A -/
theorem identity_typed (A : Ty) : [] ⊢ Lambda.Term.lam (Lambda.Term.var 0) : A ⇒ A := by
  apply HasType.lam
  apply HasType.var
  rfl

/-- The constant function λx.λy.x has type A ⇒ B ⇒ A -/
theorem const_typed (A B : Ty) : [] ⊢ Lambda.Term.lam (Lambda.Term.lam (Lambda.Term.var 1)) : A ⇒ B ⇒ A := by
  apply HasType.lam
  apply HasType.lam
  apply HasType.var
  rfl

/-! ## Context Operations -/

/-- Lookup in context -/
def Context.lookup (Γ : Context) (n : Nat) : Option Ty := Γ[n]?

/-- Context extension -/
def Context.extend (Γ : Context) (A : Ty) : Context := A :: Γ

/-! ## Weakening and Substitution Typing -/

/-- Weakening: if Γ ⊢ M : A and we insert a type at position k,
    then the term with shifted variables is typeable.

    This is the key structural lemma for typing. -/
theorem weakening : ∀ {Γ Γ' : Context} {M : Term} {A : Ty},
    HasType Γ M A →
    (∀ (n : Nat) (B : Ty), Γ[n]? = some B → Γ'[n]? = some B) →
    HasType Γ' M A := by
  intro Γ Γ' M A h_type h_pres
  induction h_type generalizing Γ' with
  | var h_get =>
    apply HasType.var
    exact h_pres _ _ h_get
  | @lam Γ M A B h_body ih =>
    apply HasType.lam
    apply ih
    intro n C h_get_ext
    cases n with
    | zero => exact h_get_ext
    | succ n' => exact h_pres n' C h_get_ext
  | app h_fun h_arg ih_fun ih_arg =>
    apply HasType.app
    · exact ih_fun h_pres
    · exact ih_arg h_pres

/-- Helper lemma for get? on appended lists -/
theorem get?_append_of_lt {α : Type} (l₁ l₂ : List α) (n : Nat) (h : n < l₁.length) :
    (l₁ ++ l₂)[n]? = l₁[n]? := by
  simp only [List.getElem?_append_left h]

theorem get?_append_of_ge {α : Type} (l₁ l₂ : List α) (n : Nat) (h : n ≥ l₁.length) :
    (l₁ ++ l₂)[n]? = l₂[n - l₁.length]? := by
  simp only [List.getElem?_append_right h]

/-- Helper: shift typing with explicit context equality -/
theorem typing_shift_at_aux {Γ Γ₁ Γ₂ : Context} {M : Term} {A B : Ty}
    (hΓ : Γ = Γ₁ ++ Γ₂)
    (h : HasType Γ M A) :
    HasType (Γ₁ ++ [B] ++ Γ₂) (Lambda.Term.shift 1 Γ₁.length M) A := by
  induction h generalizing Γ₁ Γ₂ with
  | @var Γ' n A' hget =>
    -- M = var n
    simp only [Lambda.Term.shift]
    by_cases hn : n < Γ₁.length
    · -- n < |Γ₁|: variable is in Γ₁, stays the same
      simp only [hn, ↓reduceIte]
      apply HasType.var
      -- Need: (Γ₁ ++ [B] ++ Γ₂).get? n = some A'
      have h1 : n < (Γ₁ ++ [B]).length := by simp; omega
      rw [get?_append_of_lt (Γ₁ ++ [B]) Γ₂ n h1]
      rw [get?_append_of_lt Γ₁ [B] n hn]
      rw [hΓ, get?_append_of_lt Γ₁ Γ₂ n hn] at hget
      exact hget
    · -- n ≥ |Γ₁|: variable is in Γ₂, shifts by 1
      simp only [hn, ↓reduceIte]
      -- Simplify (↑n + 1).toNat to n + 1
      have htonat : Int.toNat (↑n + 1) = n + 1 := by
        simp only [Int.toNat_natCast_add_one]
      simp only [htonat]
      apply HasType.var
      -- Need: (Γ₁ ++ [B] ++ Γ₂).get? (n + 1) = some A'
      have hge : n ≥ Γ₁.length := Nat.le_of_not_lt hn
      rw [hΓ] at hget
      rw [get?_append_of_ge Γ₁ Γ₂ n hge] at hget
      have h1 : n + 1 ≥ (Γ₁ ++ [B]).length := by simp; omega
      rw [get?_append_of_ge (Γ₁ ++ [B]) Γ₂ (n + 1) h1]
      simp only [List.length_append, List.length_singleton]
      have heq : n + 1 - (Γ₁.length + 1) = n - Γ₁.length := by omega
      rw [heq]
      exact hget
  | @lam Γ' M' A' B' hbody ih =>
    -- M = lam M'
    simp only [Lambda.Term.shift]
    apply HasType.lam
    -- IH with extended context: A' :: Γ' = (A' :: Γ₁) ++ Γ₂
    have hΓ' : A' :: Γ' = (A' :: Γ₁) ++ Γ₂ := by rw [hΓ]; rfl
    have ih' := ih hΓ'
    simp only [List.cons_append, List.length_cons] at ih'
    exact ih'
  | @app Γ' M' N' A' B' hM hN ihM ihN =>
    simp only [Lambda.Term.shift]
    exact HasType.app (ihM hΓ) (ihN hΓ)

/-- Generalized shift typing: inserting a type at position k in the context
    corresponds to shifting variables by 1 at cutoff k.

    If (Γ₁ ++ Γ₂) ⊢ M : A, then (Γ₁ ++ [B] ++ Γ₂) ⊢ shift 1 |Γ₁| M : A -/
theorem typing_shift_at {Γ₁ Γ₂ : Context} {M : Term} {A B : Ty}
    (h : HasType (Γ₁ ++ Γ₂) M A) :
    HasType (Γ₁ ++ [B] ++ Γ₂) (Lambda.Term.shift 1 Γ₁.length M) A :=
  typing_shift_at_aux rfl h

/-- Shifting preserves typing (weakening by shift).

    If Γ ⊢ N : A, then (B :: Γ) ⊢ shift 1 0 N : A.

    References:
    - Pierce et al. (2023): Software Foundations, Vol 2, "Stlc" chapter
    - Aydemir et al. (2008): "Engineering Formal Metatheory" -/
theorem typing_shift {Γ : Context} {N : Term} {A B : Ty}
    (h : HasType Γ N A) :
    HasType (B :: Γ) (Lambda.Term.shift 1 0 N) A := by
  have h' := @typing_shift_at [] Γ N A B (by simp; exact h)
  simp at h'
  exact h'

/-- Prepending types to context: if Γ ⊢ N : A, then (Δ ++ Γ) ⊢ shift |Δ| 0 N : A

    If N has type A in context Γ, and we shift N by |Δ| positions (starting from cutoff 0),
    then the shifted term has type A in context (Δ ++ Γ).

    The proof proceeds by induction on Δ, using shift_shift to decompose
    shift (|Δ'| + 1) 0 = shift 1 0 ∘ shift |Δ'| 0.

    References:
    - Pierce, "Types and Programming Languages" (2002), Chapter 9
    - Software Foundations, Vol 2, "Stlc" chapter -/
theorem typing_shift_prepend {Γ Δ : Context} {N : Term} {A : Ty}
    (hN : HasType Γ N A) :
    HasType (Δ ++ Γ) (Lambda.Term.shift Δ.length 0 N) A := by
  -- Induction on Δ
  induction Δ with
  | nil =>
    -- Base case: Δ = []
    simp only [List.nil_append, List.length_nil]
    -- shift 0 0 N = N
    have : Lambda.Term.shift (0 : Nat) 0 N = N := Lambda.Term.shift_zero 0 N
    rw [this]
    exact hN
  | cons B Δ' ih =>
    -- Inductive case: Δ = B :: Δ'
    -- Goal: (B :: Δ' ++ Γ) ⊢ shift ((B :: Δ').length) 0 N : A

    -- First apply IH to get: (Δ' ++ Γ) ⊢ shift Δ'.length 0 N : A
    have h1 : HasType (Δ' ++ Γ) (Lambda.Term.shift (↑Δ'.length) 0 N) A := ih

    -- Now apply typing_shift to get: (B :: (Δ' ++ Γ)) ⊢ shift 1 0 (shift Δ'.length 0 N) : A
    have h2 : HasType (B :: (Δ' ++ Γ)) (Lambda.Term.shift 1 0 (Lambda.Term.shift (↑Δ'.length) 0 N)) A :=
      typing_shift h1

    -- Rewrite context: B :: (Δ' ++ Γ) = (B :: Δ') ++ Γ
    simp at h2

    -- Now we need to show the terms are equal:
    -- shift ((B :: Δ').length) 0 N = shift 1 0 (shift Δ'.length 0 N)
    -- Using shift_shift: shift d₁ c (shift d₂ c M) = shift (d₁ + d₂) c M
    -- We have: shift 1 0 (shift Δ'.length 0 N) = shift (1 + Δ'.length) 0 N
    have heq : Lambda.Term.shift (↑(B :: Δ').length) 0 N =
               Lambda.Term.shift 1 0 (Lambda.Term.shift (↑Δ'.length) 0 N) := by
      simp only [List.length_cons]
      -- Goal: Lambda.Term.shift (↑(Δ'.length + 1)) 0 N = Lambda.Term.shift 1 0 (Lambda.Term.shift (↑Δ'.length) 0 N)
      rw [Nat.add_comm]
      -- Goal: Lambda.Term.shift (↑(1 + Δ'.length)) 0 N = Lambda.Term.shift 1 0 (Lambda.Term.shift (↑Δ'.length) 0 N)
      -- Apply shift_shift: shift d₁ c (shift d₂ c M) = shift (d₁ + d₂) c M
      exact (Lambda.Term.shift_shift 1 Δ'.length 0 N).symm
    rw [heq]
    exact h2

/-- Helper lemma: if N is typed in Γ₂, then shifting by |Γ₁| makes it typed in Γ₁ ++ Γ₂.

    This is just an application of typing_shift_prepend with renamed variables. -/
theorem typing_shift_from_suffix {Γ₁ Γ₂ : Context} {N : Term} {A : Ty}
    (hN : HasType Γ₂ N A) :
    HasType (Γ₁ ++ Γ₂) (Lambda.Term.shift Γ₁.length 0 N) A :=
  typing_shift_prepend hN

/-- Helper lemma for substitution typing with explicit context.

    This avoids the "index not a variable" issue with induction by taking an
    explicit equality parameter, following the pattern of typing_shift_at_aux. -/
theorem substitution_typing_gen_aux {Γ : Context} {M : Term} {B : Ty}
    (hM : HasType Γ M B) :
    ∀ {Γ₁ Γ₂ : Context} {N : Term} {A : Ty} (j : Nat),
    Γ = Γ₁ ++ [A] ++ Γ₂ →
    j = Γ₁.length →
    HasType (Γ₁ ++ Γ₂) N A →
    HasType (Γ₁ ++ Γ₂) (Lambda.Term.subst j N M) B := by
  induction hM with
  | @var Γ' n C hget =>
      -- M = var n
      intro Γ₁ Γ₂ N A j hΓ hj hN
      simp only [Lambda.Term.subst]
      by_cases hn_eq : n = j
      · -- Case: n = j
        simp only [hn_eq, ↓reduceIte]
        subst hn_eq
        rw [hΓ] at hget
        rw [hj] at hget
        have h1 : Γ₁.length < (Γ₁ ++ [A]).length := by simp
        rw [get?_append_of_lt (Γ₁ ++ [A]) Γ₂ Γ₁.length h1] at hget
        have h2 : Γ₁.length ≥ Γ₁.length := Nat.le_refl _
        rw [get?_append_of_ge Γ₁ [A] Γ₁.length h2] at hget
        simp at hget
        cases hget
        -- With corrected substitution, subst j N (var j) = N directly
        exact hN
      · -- Case: n ≠ j
        by_cases hn_gt : n > j
        · -- Case: n > j
          simp only [hn_eq, hn_gt, ↓reduceIte]
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
        · -- Case: n < j
          have hn_lt : n < j := by
            omega
          simp only [hn_eq, hn_gt, ↓reduceIte]
          apply HasType.var
          rw [hΓ] at hget
          rw [hj] at hn_lt
          have h1 : n < (Γ₁ ++ [A]).length := by simp; omega
          rw [get?_append_of_lt (Γ₁ ++ [A]) Γ₂ n h1] at hget
          have h2 : n < Γ₁.length := hn_lt
          rw [get?_append_of_lt Γ₁ [A] n h2] at hget
          rw [get?_append_of_lt Γ₁ Γ₂ n h2]
          exact hget
  | @lam Γ' M' C D hbody ih =>
      -- M = lam M'
      intro Γ₁ Γ₂ N A j hΓ hj hN
      simp only [Lambda.Term.subst]
      apply HasType.lam
      have h1 : (C :: Γ₁) ++ [A] ++ Γ₂ = C :: (Γ₁ ++ [A] ++ Γ₂) := by simp
      have h2 : (C :: Γ₁) ++ Γ₂ = C :: (Γ₁ ++ Γ₂) := by simp
      have hΓ' : C :: Γ' = (C :: Γ₁) ++ [A] ++ Γ₂ := by rw [hΓ]; exact h1
      have hN' : HasType ((C :: Γ₁) ++ Γ₂) (Lambda.Term.shift1 N) A := by
        rw [h2]
        exact typing_shift hN
      have hj' : j + 1 = (C :: Γ₁).length := by simp [hj]
      have ih' := @ih (C :: Γ₁) Γ₂ (Lambda.Term.shift1 N) A (j + 1) hΓ' hj' hN'
      rw [h2] at ih'
      exact ih'
  | @app Γ' M₁ M₂ C D hM₁ hM₂ ihM₁ ihM₂ =>
      -- M = app M₁ M₂
      intro Γ₁ Γ₂ N A j hΓ hj hN
      simp only [Lambda.Term.subst]
      apply HasType.app
      · exact @ihM₁ Γ₁ Γ₂ N A j hΓ hj hN
      · exact @ihM₂ Γ₁ Γ₂ N A j hΓ hj hN

/-- Generalized substitution typing.

    If M is typed in a context with an extra type A at position j, and N has type A
    in the context without that position, then substituting N for variable j in M
    preserves typing.

    References:
    - Pierce, "Types and Programming Languages" (2002), Chapter 9
    - Software Foundations, Vol 2, "Stlc" chapter
    - Aydemir et al., "Engineering Formal Metatheory" (2008) -/
theorem substitution_typing_gen : ∀ {Γ₁ Γ₂ : Context} {M N : Term} {A B : Ty} (j : Nat),
    j = Γ₁.length →
    HasType (Γ₁ ++ [A] ++ Γ₂) M B →
    HasType (Γ₁ ++ Γ₂) N A →
    HasType (Γ₁ ++ Γ₂) (Lambda.Term.subst j N M) B := by
  intro Γ₁ Γ₂ M N A B j hj hM hN
  exact @substitution_typing_gen_aux (Γ₁ ++ [A] ++ Γ₂) M B hM Γ₁ Γ₂ N A j rfl hj hN

/-- Substitution typing: if (A :: Γ) ⊢ M : B and Γ ⊢ N : A,
    then Γ ⊢ M[N] : B (where M[N] = subst0 N M = subst 0 N M)

    This is the substitution lemma for simply typed lambda calculus, proved by
    the generalized version with Γ₁ = [] and j = 0.

    References:
    - Pierce, "Types and Programming Languages" (2002), Chapter 9
    - Software Foundations, Vol 2, "Stlc" chapter -/
theorem substitution_typing {Γ : Context} {M N : Term} {A B : Ty}
    (hM : HasType (A :: Γ) M B)
    (hN : HasType Γ N A) :
    HasType Γ (Lambda.Term.subst0 N M) B := by
  unfold Lambda.Term.subst0
  have hM' : HasType ([] ++ [A] ++ Γ) M B := by simp; exact hM
  have hN' : HasType ([] ++ Γ) N A := by simp; exact hN
  have h := @substitution_typing_gen [] Γ M N A B 0 (by simp) hM' hN'
  simp at h
  exact h

/-! ## Subject Reduction -/

/-- Subject Reduction: if Γ ⊢ M : A and M →β N, then Γ ⊢ N : A

    Reference: Pierce TAPL, Chapter 9 -/
theorem subject_reduction {Γ : Context} {M N : Term} {A : Ty}
    (htype : Γ ⊢ M : A) (hstep : Lambda.BetaStep M N) : Γ ⊢ N : A := by
  induction hstep generalizing Γ A with
  | beta M' N' =>
    cases htype with
    | @app _ _ _ B _ hM hN =>
      cases hM with
      | @lam _ _ _ _ hBody =>
        exact substitution_typing hBody hN
  | appL _ ih =>
    cases htype with
    | app hM hN =>
      exact HasType.app (ih hM) hN
  | appR _ ih =>
    cases htype with
    | app hM hN =>
      exact HasType.app hM (ih hN)
  | lam _ ih =>
    cases htype with
    | lam hBody =>
      exact HasType.lam (ih hBody)

/-- Subject reduction for multi-step reduction -/
theorem subject_reduction_multi {Γ : Context} {M N : Term} {A : Ty}
    (htype : Γ ⊢ M : A) (hsteps : Lambda.MultiStep M N) : Γ ⊢ N : A := by
  induction hsteps with
  | refl => exact htype
  | step hstep _ ih =>
    exact ih (subject_reduction htype hstep)

/-! ## Note on Uniqueness of Types

    This STLC formalization uses **Curry-style** terms where lambdas don't carry
    type annotations: `lam M` rather than `lam (x : A). M`.

    In Curry-style systems, **uniqueness of types does not hold** in general.
    For example, `lam (var 1)` can have type `A → B` for any `A` if `var 1 : B`.

    For uniqueness of types, see the **System F** formalization which uses
    Church-style terms with explicit type annotations. -/

/-! ## Progress (for closed terms) -/

/-- A term is a value (normal form for STLC is lambda abstraction) -/
def IsValue : Term → Prop
  | Lambda.Term.lam _ => True
  | _ => False

/-- Canonical Forms Lemma -/
theorem canonical_forms_arr {M : Term} {A B : Ty}
    (htype : [] ⊢ M : A ⇒ B) (hval : IsValue M) :
    ∃ M', M = Lambda.Term.lam M' := by
  cases M with
  | var n =>
    cases htype with
    | var h => cases h
  | app _ _ =>
    cases hval
  | lam M' =>
    exact ⟨M', rfl⟩

/-- Progress: A closed well-typed term is either a value or can step.

    For STLC, this means: if [] ⊢ M : A, then either M is a lambda
    or M → N for some N.

    Reference: Pierce TAPL, Chapter 9 -/
theorem progress {M : Term} {A : Ty}
    (htype : [] ⊢ M : A) :
    IsValue M ∨ ∃ N, Lambda.BetaStep M N := by
  match M with
  | Lambda.Term.var n =>
    -- Impossible: [] has no variables
    cases htype with
    | var h => cases h
  | Lambda.Term.lam _ =>
    -- Lambda is a value
    left
    exact trivial
  | Lambda.Term.app M' N' =>
    -- Application: either M' steps, or M' is a value (hence lambda) and we can beta
    cases htype with
    | @app _ _ _ B _ hM' hN' =>
      have ih : IsValue M' ∨ ∃ N, Lambda.BetaStep M' N := progress hM'
      cases ih with
      | inl hval =>
        -- M' is a value, by canonical forms it's a lambda
        obtain ⟨M'', hM'_eq⟩ := canonical_forms_arr hM' hval
        right
        rw [hM'_eq]
        exact ⟨Lambda.Term.subst0 N' M'', Lambda.BetaStep.beta M'' N'⟩
      | inr hstep =>
        -- M' steps
        obtain ⟨M'', hstep'⟩ := hstep
        right
        exact ⟨Lambda.Term.app M'' N', Lambda.BetaStep.appL hstep'⟩

end Metatheory.STLC
