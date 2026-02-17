/-
# Simply Typed Lambda Calculus with Products and Sums - Typing

This module defines typing contexts and the typing relation for the extended STLC
with products and sums, along with subject reduction.

## Overview

- Contexts are lists of types (de Bruijn style)
- The typing judgment Γ ⊢ M : A assigns types to terms
- Well-typed terms enjoy subject reduction (types preserved under reduction)

## Typing Rules

### Lambda Calculus
- Γ(x) = A ⟹ Γ ⊢ x : A
- (A :: Γ) ⊢ M : B ⟹ Γ ⊢ λM : A → B
- Γ ⊢ M : A → B, Γ ⊢ N : A ⟹ Γ ⊢ M N : B

### Products
- Γ ⊢ M : A, Γ ⊢ N : B ⟹ Γ ⊢ (M, N) : A × B
- Γ ⊢ M : A × B ⟹ Γ ⊢ fst M : A
- Γ ⊢ M : A × B ⟹ Γ ⊢ snd M : B

### Sums
- Γ ⊢ M : A ⟹ Γ ⊢ inl M : A + B
- Γ ⊢ M : B ⟹ Γ ⊢ inr M : A + B
- Γ ⊢ M : A + B, (A :: Γ) ⊢ N₁ : C, (B :: Γ) ⊢ N₂ : C ⟹ Γ ⊢ case M N₁ N₂ : C

## References

- Pierce, "Types and Programming Languages" (2002), Chapters 11 and 12
-/

import Metatheory.STLCext.Reduction

namespace Metatheory.STLCext

/-! ## Typing Contexts -/

/-- A typing context is a list of types (de Bruijn indexed) -/
abbrev Context := List Ty

/-! ## Typing Relation -/

/-- Typing judgment: Γ ⊢ M : A -/
inductive HasType : Context → Term → Ty → Prop where
  /-- Variable rule -/
  | var : ∀ {Γ : Context} {n : Nat} {A : Ty},
      Γ[n]? = some A →
      HasType Γ (Term.var n) A
  /-- Lambda abstraction -/
  | lam : ∀ {Γ : Context} {M : Term} {A B : Ty},
      HasType (A :: Γ) M B →
      HasType Γ (Term.lam M) (A ⇒ B)
  /-- Application -/
  | app : ∀ {Γ : Context} {M N : Term} {A B : Ty},
      HasType Γ M (A ⇒ B) →
      HasType Γ N A →
      HasType Γ (Term.app M N) B
  /-- Pair introduction -/
  | pair : ∀ {Γ : Context} {M N : Term} {A B : Ty},
      HasType Γ M A →
      HasType Γ N B →
      HasType Γ (Term.pair M N) (A ⊗ B)
  /-- First projection -/
  | fst : ∀ {Γ : Context} {M : Term} {A B : Ty},
      HasType Γ M (A ⊗ B) →
      HasType Γ (Term.fst M) A
  /-- Second projection -/
  | snd : ∀ {Γ : Context} {M : Term} {A B : Ty},
      HasType Γ M (A ⊗ B) →
      HasType Γ (Term.snd M) B
  /-- Left injection -/
  | inl : ∀ {Γ : Context} {M : Term} {A B : Ty},
      HasType Γ M A →
      HasType Γ (Term.inl M) (A ⊕ B)
  /-- Right injection -/
  | inr : ∀ {Γ : Context} {M : Term} {A B : Ty},
      HasType Γ M B →
      HasType Γ (Term.inr M) (A ⊕ B)
  /-- Case analysis -/
  | case : ∀ {Γ : Context} {M N₁ N₂ : Term} {A B C : Ty},
      HasType Γ M (A ⊕ B) →
      HasType (A :: Γ) N₁ C →
      HasType (B :: Γ) N₂ C →
      HasType Γ (Term.case M N₁ N₂) C
  /-- Unit introduction -/
  | unit : ∀ {Γ : Context},
      HasType Γ Term.unit Ty.unit

/-- Notation for typing judgment -/
scoped notation:50 Γ " ⊢ " M " : " A => HasType Γ M A

/-! ## Basic Typing Examples -/

/-- The identity function λx.x has type A ⇒ A -/
theorem identity_typed (A : Ty) : [] ⊢ Term.lam (Term.var 0) : A ⇒ A := by
  apply HasType.lam
  apply HasType.var
  rfl

/-- The pairing function λx.λy.(x,y) has type A ⇒ B ⇒ A × B -/
theorem pair_typed (A B : Ty) :
    [] ⊢ Term.lam (Term.lam (Term.pair (Term.var 1) (Term.var 0))) : A ⇒ B ⇒ A ⊗ B := by
  apply HasType.lam
  apply HasType.lam
  apply HasType.pair
  · apply HasType.var; rfl
  · apply HasType.var; rfl

/-! ## Context Operations -/

/-- Lookup in context -/
def Context.lookup (Γ : Context) (n : Nat) : Option Ty := Γ[n]?

/-- Context extension -/
def Context.extend (Γ : Context) (A : Ty) : Context := A :: Γ

/-! ## Helper Lemmas for Context Manipulation -/

/-- Helper lemma for get? on appended lists -/
theorem get?_append_of_lt {α : Type} (l₁ l₂ : List α) (n : Nat) (h : n < l₁.length) :
    (l₁ ++ l₂)[n]? = l₁[n]? := by
  simp only [List.getElem?_append_left h]

theorem get?_append_of_ge {α : Type} (l₁ l₂ : List α) (n : Nat) (h : n ≥ l₁.length) :
    (l₁ ++ l₂)[n]? = l₂[n - l₁.length]? := by
  simp only [List.getElem?_append_right h]

/-! ## Weakening -/

/-- Weakening: if Γ ⊢ M : A and we preserve context lookups, then Γ' ⊢ M : A -/
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
  | pair h_fst h_snd ih_fst ih_snd =>
    apply HasType.pair
    · exact ih_fst h_pres
    · exact ih_snd h_pres
  | fst h_pair ih =>
    apply HasType.fst
    exact ih h_pres
  | snd h_pair ih =>
    apply HasType.snd
    exact ih h_pres
  | inl h_val ih =>
    apply HasType.inl
    exact ih h_pres
  | inr h_val ih =>
    apply HasType.inr
    exact ih h_pres
  | @case Γ M N₁ N₂ A B C h_scrut h_left h_right ih_scrut ih_left ih_right =>
    apply HasType.case
    · exact ih_scrut h_pres
    · apply ih_left
      intro n D h_get
      cases n with
      | zero => exact h_get
      | succ n' => exact h_pres n' D h_get
    · apply ih_right
      intro n D h_get
      cases n with
      | zero => exact h_get
      | succ n' => exact h_pres n' D h_get
  | unit => exact HasType.unit

/-! ## Shift Typing -/

/-- Helper: shift typing with explicit context equality -/
theorem typing_shift_at_aux {Γ Γ₁ Γ₂ : Context} {M : Term} {A B : Ty}
    (hΓ : Γ = Γ₁ ++ Γ₂)
    (h : HasType Γ M A) :
    HasType (Γ₁ ++ [B] ++ Γ₂) (Term.shift 1 Γ₁.length M) A := by
  induction h generalizing Γ₁ Γ₂ with
  | @var Γ' n A' hget =>
    simp only [Term.shift]
    by_cases hn : n < Γ₁.length
    · simp only [hn, ↓reduceIte]
      apply HasType.var
      have h1 : n < (Γ₁ ++ [B]).length := by simp; omega
      rw [get?_append_of_lt (Γ₁ ++ [B]) Γ₂ n h1]
      rw [get?_append_of_lt Γ₁ [B] n hn]
      rw [hΓ, get?_append_of_lt Γ₁ Γ₂ n hn] at hget
      exact hget
    · simp only [hn, ↓reduceIte]
      have htonat : Int.toNat (↑n + 1) = n + 1 := by simp only [Int.toNat_natCast_add_one]
      simp only [htonat]
      apply HasType.var
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
    simp only [Term.shift]
    apply HasType.lam
    have hΓ' : A' :: Γ' = (A' :: Γ₁) ++ Γ₂ := by rw [hΓ]; rfl
    have ih' := ih hΓ'
    simp only [List.cons_append, List.length_cons] at ih'
    exact ih'
  | @app Γ' M' N' A' B' hM hN ihM ihN =>
    simp only [Term.shift]
    exact HasType.app (ihM hΓ) (ihN hΓ)
  | @pair Γ' M' N' A' B' hM hN ihM ihN =>
    simp only [Term.shift]
    exact HasType.pair (ihM hΓ) (ihN hΓ)
  | @fst Γ' M' A' B' hM ihM =>
    simp only [Term.shift]
    exact HasType.fst (ihM hΓ)
  | @snd Γ' M' A' B' hM ihM =>
    simp only [Term.shift]
    exact HasType.snd (ihM hΓ)
  | @inl Γ' M' A' B' hM ihM =>
    simp only [Term.shift]
    exact HasType.inl (ihM hΓ)
  | @inr Γ' M' A' B' hM ihM =>
    simp only [Term.shift]
    exact HasType.inr (ihM hΓ)
  | @case Γ' M' N₁ N₂ A' B' C hM hN₁ hN₂ ihM ihN₁ ihN₂ =>
    simp only [Term.shift]
    apply HasType.case
    · exact ihM hΓ
    · have hΓ₁ : A' :: Γ' = (A' :: Γ₁) ++ Γ₂ := by rw [hΓ]; rfl
      have ih₁ := ihN₁ hΓ₁
      simp only [List.cons_append, List.length_cons] at ih₁
      exact ih₁
    · have hΓ₂ : B' :: Γ' = (B' :: Γ₁) ++ Γ₂ := by rw [hΓ]; rfl
      have ih₂ := ihN₂ hΓ₂
      simp only [List.cons_append, List.length_cons] at ih₂
      exact ih₂
  | unit => simp only [Term.shift]; exact HasType.unit

/-- Shifting preserves typing -/
theorem typing_shift {Γ : Context} {N : Term} {A B : Ty}
    (h : HasType Γ N A) :
    HasType (B :: Γ) (Term.shift 1 0 N) A := by
  have h' := @typing_shift_at_aux Γ [] Γ N A B (by simp) h
  simp at h'
  exact h'

/-- Prepending types to context -/
theorem typing_shift_prepend {Γ Δ : Context} {N : Term} {A : Ty}
    (hN : HasType Γ N A) :
    HasType (Δ ++ Γ) (Term.shift Δ.length 0 N) A := by
  induction Δ with
  | nil =>
    simp only [List.nil_append, List.length_nil]
    have : Term.shift (0 : Nat) 0 N = N := Term.shift_zero 0 N
    rw [this]
    exact hN
  | cons B Δ' ih =>
    have h1 : HasType (Δ' ++ Γ) (Term.shift (↑Δ'.length) 0 N) A := ih
    have h2 : HasType (B :: (Δ' ++ Γ)) (Term.shift 1 0 (Term.shift (↑Δ'.length) 0 N)) A :=
      typing_shift h1
    simp at h2
    have heq : Term.shift (↑(B :: Δ').length) 0 N =
               Term.shift 1 0 (Term.shift (↑Δ'.length) 0 N) := by
      simp only [List.length_cons]
      rw [Nat.add_comm]
      exact (Term.shift_shift 1 Δ'.length 0 N).symm
    rw [heq]
    exact h2

/-! ## Substitution Typing -/

/-- Helper for substitution typing -/
theorem substitution_typing_gen_aux {Γ : Context} {M : Term} {B : Ty}
    (hM : HasType Γ M B) :
    ∀ {Γ₁ Γ₂ : Context} {N : Term} {A : Ty} (j : Nat),
    Γ = Γ₁ ++ [A] ++ Γ₂ →
    j = Γ₁.length →
    HasType (Γ₁ ++ Γ₂) N A →
    HasType (Γ₁ ++ Γ₂) (Term.subst j N M) B := by
  induction hM with
  | @var Γ' n C hget =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp only [Term.subst]
    by_cases hn_eq : n = j
    · simp only [hn_eq, ↓reduceIte]
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
      · simp only [hn_eq, hn_gt, ↓reduceIte]
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
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp only [Term.subst]
    apply HasType.lam
    have h1 : (C :: Γ₁) ++ [A] ++ Γ₂ = C :: (Γ₁ ++ [A] ++ Γ₂) := by simp
    have h2 : (C :: Γ₁) ++ Γ₂ = C :: (Γ₁ ++ Γ₂) := by simp
    have hΓ' : C :: Γ' = (C :: Γ₁) ++ [A] ++ Γ₂ := by rw [hΓ]; exact h1
    have hN' : HasType ((C :: Γ₁) ++ Γ₂) (Term.shift1 N) A := by
      rw [h2]
      exact typing_shift hN
    have hj' : j + 1 = (C :: Γ₁).length := by simp [hj]
    have ih' := @ih (C :: Γ₁) Γ₂ (Term.shift1 N) A (j + 1) hΓ' hj' hN'
    rw [h2] at ih'
    exact ih'
  | @app Γ' M₁ M₂ C D hM₁ hM₂ ihM₁ ihM₂ =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp only [Term.subst]
    apply HasType.app
    · exact @ihM₁ Γ₁ Γ₂ N A j hΓ hj hN
    · exact @ihM₂ Γ₁ Γ₂ N A j hΓ hj hN
  | @pair Γ' M₁ M₂ C D hM₁ hM₂ ihM₁ ihM₂ =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp only [Term.subst]
    apply HasType.pair
    · exact @ihM₁ Γ₁ Γ₂ N A j hΓ hj hN
    · exact @ihM₂ Γ₁ Γ₂ N A j hΓ hj hN
  | @fst Γ' M' C D hM ihM =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp only [Term.subst]
    apply HasType.fst
    exact @ihM Γ₁ Γ₂ N A j hΓ hj hN
  | @snd Γ' M' C D hM ihM =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp only [Term.subst]
    apply HasType.snd
    exact @ihM Γ₁ Γ₂ N A j hΓ hj hN
  | @inl Γ' M' C D hM ihM =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp only [Term.subst]
    apply HasType.inl
    exact @ihM Γ₁ Γ₂ N A j hΓ hj hN
  | @inr Γ' M' C D hM ihM =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp only [Term.subst]
    apply HasType.inr
    exact @ihM Γ₁ Γ₂ N A j hΓ hj hN
  | @case Γ' M' N₁ N₂ C D E hM hN₁ hN₂ ihM ihN₁ ihN₂ =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp only [Term.subst]
    apply HasType.case
    · exact @ihM Γ₁ Γ₂ N A j hΓ hj hN
    · have h1 : (C :: Γ₁) ++ [A] ++ Γ₂ = C :: (Γ₁ ++ [A] ++ Γ₂) := by simp
      have h2 : (C :: Γ₁) ++ Γ₂ = C :: (Γ₁ ++ Γ₂) := by simp
      have hΓ' : C :: Γ' = (C :: Γ₁) ++ [A] ++ Γ₂ := by rw [hΓ]; exact h1
      have hN' : HasType ((C :: Γ₁) ++ Γ₂) (Term.shift1 N) A := by
        rw [h2]
        exact typing_shift hN
      have hj' : j + 1 = (C :: Γ₁).length := by simp [hj]
      have ih' := @ihN₁ (C :: Γ₁) Γ₂ (Term.shift1 N) A (j + 1) hΓ' hj' hN'
      rw [h2] at ih'
      exact ih'
    · have h1 : (D :: Γ₁) ++ [A] ++ Γ₂ = D :: (Γ₁ ++ [A] ++ Γ₂) := by simp
      have h2 : (D :: Γ₁) ++ Γ₂ = D :: (Γ₁ ++ Γ₂) := by simp
      have hΓ' : D :: Γ' = (D :: Γ₁) ++ [A] ++ Γ₂ := by rw [hΓ]; exact h1
      have hN' : HasType ((D :: Γ₁) ++ Γ₂) (Term.shift1 N) A := by
        rw [h2]
        exact typing_shift hN
      have hj' : j + 1 = (D :: Γ₁).length := by simp [hj]
      have ih' := @ihN₂ (D :: Γ₁) Γ₂ (Term.shift1 N) A (j + 1) hΓ' hj' hN'
      rw [h2] at ih'
      exact ih'
  | unit =>
    intro Γ₁ Γ₂ N A j hΓ hj hN
    simp only [Term.subst]
    exact HasType.unit

/-- Substitution typing (main lemma) -/
theorem substitution_typing {Γ : Context} {M N : Term} {A B : Ty}
    (hM : HasType (A :: Γ) M B)
    (hN : HasType Γ N A) :
    HasType Γ (Term.subst0 N M) B := by
  unfold Term.subst0
  have hM' : HasType ([] ++ [A] ++ Γ) M B := by simp; exact hM
  have hN' : HasType ([] ++ Γ) N A := by simp; exact hN
  have h := @substitution_typing_gen_aux ([] ++ [A] ++ Γ) M B hM' [] Γ N A 0 (by simp) (by simp) hN'
  simp at h
  exact h

/-! ## Subject Reduction -/

/-- Subject Reduction: if Γ ⊢ M : A and M → N, then Γ ⊢ N : A -/
theorem subject_reduction {Γ : Context} {M N : Term} {A : Ty}
    (htype : Γ ⊢ M : A) (hstep : Step M N) : Γ ⊢ N : A := by
  induction hstep generalizing Γ A with
  | beta M' N' =>
    cases htype with
    | @app _ _ _ B _ hM hN =>
      cases hM with
      | @lam _ _ _ _ hBody =>
        exact substitution_typing hBody hN
  | fstPair M' N' =>
    cases htype with
    | @fst _ _ A' B' hP =>
      cases hP with
      | pair hM hN => exact hM
  | sndPair M' N' =>
    cases htype with
    | @snd _ _ A' B' hP =>
      cases hP with
      | pair hM hN => exact hN
  | caseInl V N₁ N₂ =>
    cases htype with
    | @case _ _ _ _ A' B' C hS hL hR =>
      cases hS with
      | @inl _ _ _ _ hV =>
        exact substitution_typing hL hV
  | caseInr V N₁ N₂ =>
    cases htype with
    | @case _ _ _ _ A' B' C hS hL hR =>
      cases hS with
      | @inr _ _ _ _ hV =>
        exact substitution_typing hR hV
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
  | pairL _ ih =>
    cases htype with
    | pair hM hN =>
      exact HasType.pair (ih hM) hN
  | pairR _ ih =>
    cases htype with
    | pair hM hN =>
      exact HasType.pair hM (ih hN)
  | fst _ ih =>
    cases htype with
    | fst hM =>
      exact HasType.fst (ih hM)
  | snd _ ih =>
    cases htype with
    | snd hM =>
      exact HasType.snd (ih hM)
  | inl _ ih =>
    cases htype with
    | inl hM =>
      exact HasType.inl (ih hM)
  | inr _ ih =>
    cases htype with
    | inr hM =>
      exact HasType.inr (ih hM)
  | caseS _ ih =>
    cases htype with
    | case hM hL hR =>
      exact HasType.case (ih hM) hL hR
  | caseL _ ih =>
    cases htype with
    | case hM hL hR =>
      exact HasType.case hM (ih hL) hR
  | caseR _ ih =>
    cases htype with
    | case hM hL hR =>
      exact HasType.case hM hL (ih hR)

/-- Subject reduction for multi-step reduction -/
theorem subject_reduction_multi {Γ : Context} {M N : Term} {A : Ty}
    (htype : Γ ⊢ M : A) (hsteps : MultiStep M N) : Γ ⊢ N : A := by
  induction hsteps with
  | refl => exact htype
  | step hstep _ ih =>
    exact ih (subject_reduction htype hstep)

/-! ## Progress -/

/-- A term is a value -/
def IsValue : Term → Prop
  | Term.lam _ => True
  | Term.pair M N => IsValue M ∧ IsValue N
  | Term.inl M => IsValue M
  | Term.inr M => IsValue M
  | Term.unit => True
  | _ => False

/-- Canonical forms for function types -/
theorem canonical_forms_arr {M : Term} {A B : Ty}
    (htype : [] ⊢ M : A ⇒ B) (hval : IsValue M) :
    ∃ M', M = Term.lam M' := by
  cases M with
  | var n => cases htype with | var h => cases h
  | lam M' => exact ⟨M', rfl⟩
  | app _ _ => cases hval
  | pair _ _ => cases htype
  | fst _ => cases hval
  | snd _ => cases hval
  | inl _ => cases htype
  | inr _ => cases htype
  | case _ _ _ => cases hval
  | unit => cases htype

/-- Canonical forms for product types -/
theorem canonical_forms_prod {M : Term} {A B : Ty}
    (htype : [] ⊢ M : A ⊗ B) (hval : IsValue M) :
    ∃ M₁ M₂, M = Term.pair M₁ M₂ := by
  cases M with
  | var n => cases htype with | var h => cases h
  | lam _ => cases htype
  | app _ _ => cases hval
  | pair M₁ M₂ => exact ⟨M₁, M₂, rfl⟩
  | fst _ => cases hval
  | snd _ => cases hval
  | inl _ => cases htype
  | inr _ => cases htype
  | case _ _ _ => cases hval
  | unit => cases htype

/-- Canonical forms for sum types -/
theorem canonical_forms_sum {M : Term} {A B : Ty}
    (htype : [] ⊢ M : A ⊕ B) (hval : IsValue M) :
    (∃ M', M = Term.inl M') ∨ (∃ M', M = Term.inr M') := by
  cases M with
  | var n => cases htype with | var h => cases h
  | lam _ => cases htype
  | app _ _ => cases hval
  | pair _ _ => cases htype
  | fst _ => cases hval
  | snd _ => cases hval
  | inl M' => exact Or.inl ⟨M', rfl⟩
  | inr M' => exact Or.inr ⟨M', rfl⟩
  | case _ _ _ => cases hval
  | unit => cases htype

/-- Progress: A closed well-typed term is either a value or can step -/
theorem progress {M : Term} {A : Ty}
    (htype : [] ⊢ M : A) :
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
    | @app _ _ _ B _ hM' hN' =>
      have ih : IsValue M' ∨ ∃ N, Step M' N := progress hM'
      cases ih with
      | inl hval =>
        obtain ⟨M'', hM'_eq⟩ := canonical_forms_arr hM' hval
        right
        rw [hM'_eq]
        exact ⟨Term.subst0 N' M'', Step.beta M'' N'⟩
      | inr hstep =>
        obtain ⟨M'', hstep'⟩ := hstep
        right
        exact ⟨Term.app M'' N', Step.appL hstep'⟩
  | Term.pair M' N' =>
    cases htype with
    | pair hM' hN' =>
      have ihM : IsValue M' ∨ ∃ N, Step M' N := progress hM'
      have ihN : IsValue N' ∨ ∃ N, Step N' N := progress hN'
      cases ihM with
      | inl hvalM =>
        cases ihN with
        | inl hvalN =>
          left
          exact ⟨hvalM, hvalN⟩
        | inr hstepN =>
          obtain ⟨N'', hstep'⟩ := hstepN
          right
          exact ⟨Term.pair M' N'', Step.pairR hstep'⟩
      | inr hstepM =>
        obtain ⟨M'', hstep'⟩ := hstepM
        right
        exact ⟨Term.pair M'' N', Step.pairL hstep'⟩
  | Term.fst M' =>
    cases htype with
    | @fst _ _ A' B' hM' =>
      have ih : IsValue M' ∨ ∃ N, Step M' N := progress hM'
      cases ih with
      | inl hval =>
        obtain ⟨M₁, M₂, hM'_eq⟩ := canonical_forms_prod hM' hval
        right
        rw [hM'_eq]
        exact ⟨M₁, Step.fstPair M₁ M₂⟩
      | inr hstep =>
        obtain ⟨M'', hstep'⟩ := hstep
        right
        exact ⟨Term.fst M'', Step.fst hstep'⟩
  | Term.snd M' =>
    cases htype with
    | @snd _ _ A' B' hM' =>
      have ih : IsValue M' ∨ ∃ N, Step M' N := progress hM'
      cases ih with
      | inl hval =>
        obtain ⟨M₁, M₂, hM'_eq⟩ := canonical_forms_prod hM' hval
        right
        rw [hM'_eq]
        exact ⟨M₂, Step.sndPair M₁ M₂⟩
      | inr hstep =>
        obtain ⟨M'', hstep'⟩ := hstep
        right
        exact ⟨Term.snd M'', Step.snd hstep'⟩
  | Term.inl M' =>
    cases htype with
    | inl hM' =>
      have ih : IsValue M' ∨ ∃ N, Step M' N := progress hM'
      cases ih with
      | inl hval =>
        left
        exact hval
      | inr hstep =>
        obtain ⟨M'', hstep'⟩ := hstep
        right
        exact ⟨Term.inl M'', Step.inl hstep'⟩
  | Term.inr M' =>
    cases htype with
    | inr hM' =>
      have ih : IsValue M' ∨ ∃ N, Step M' N := progress hM'
      cases ih with
      | inl hval =>
        left
        exact hval
      | inr hstep =>
        obtain ⟨M'', hstep'⟩ := hstep
        right
        exact ⟨Term.inr M'', Step.inr hstep'⟩
  | Term.case M' N₁ N₂ =>
    cases htype with
    | @case _ _ _ _ A' B' C hM' hN₁ hN₂ =>
      have ih : IsValue M' ∨ ∃ N, Step M' N := progress hM'
      cases ih with
      | inl hval =>
        have hcf := canonical_forms_sum hM' hval
        cases hcf with
        | inl hl =>
          obtain ⟨V, hM'_eq⟩ := hl
          right
          rw [hM'_eq]
          exact ⟨Term.subst0 V N₁, Step.caseInl V N₁ N₂⟩
        | inr hr =>
          obtain ⟨V, hM'_eq⟩ := hr
          right
          rw [hM'_eq]
          exact ⟨Term.subst0 V N₂, Step.caseInr V N₁ N₂⟩
      | inr hstep =>
        obtain ⟨M'', hstep'⟩ := hstep
        right
        exact ⟨Term.case M'' N₁ N₂, Step.caseS hstep'⟩
  | Term.unit =>
    left
    exact trivial

end Metatheory.STLCext
