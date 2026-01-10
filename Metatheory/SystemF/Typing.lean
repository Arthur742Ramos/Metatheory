/-
# System F Typing

This module defines the typing relation for System F (polymorphic lambda calculus).

## Overview

System F typing extends STLC typing with:
- Type abstraction: Γ ⊢ Λα. M : ∀α. τ when Γ, α ⊢ M : τ
- Type application: Γ ⊢ M [σ] : τ[σ/α] when Γ ⊢ M : ∀α. τ

## Contexts

A context contains term variable bindings with their types.
When we go under a type binder (Λ):
- Term variable types get shifted (type indices increase by 1)
- The type variable count k increases by 1

## What's Proved

- Type well-formedness preservation (hasType_wf)
- Progress theorem for closed terms

## Future Work

Subject reduction requires substitution lemmas that are substantial to prove.
See the STLC module for the approach used for simpler lambda calculus.

## References

- Pierce, "Types and Programming Languages" (2002), Chapter 23
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
-/

import Metatheory.SystemF.Terms

namespace Metatheory.SystemF

open Ty Term

/-! ## Typing Contexts

We use a simplified representation where the context is a list of types.
Type variables are tracked implicitly by a separate count k. -/

/-- A typing context is a list of types for term variables.
    The nth entry gives the type of term variable n.
    Type well-formedness is tracked by a separate type variable count. -/
abbrev Context := List Ty

/-- Number of type variables in scope -/
abbrev TyVarCount := Nat

/-! ## Context Operations -/

/-- Shift all types in context when going under a type binder -/
def shiftContext (Γ : Context) : Context :=
  Γ.map (shiftTyUp 1 0)

/-- Lookup a term variable in context -/
def lookup (Γ : Context) (n : Nat) : Option Ty :=
  Γ[n]?

/-! ## Typing Relation -/

/-- Typing judgment: Γ ⊢ M : τ at type variable depth k
    k tracks how many type variables are in scope -/
inductive HasType : TyVarCount → Context → Term → Ty → Prop where
  /-- Variable rule -/
  | var : ∀ {k Γ n τ},
      lookup Γ n = some τ →
      HasType k Γ (var n) τ

  /-- Lambda abstraction -/
  | lam : ∀ {k Γ τ₁ τ₂ M},
      Ty.WF k τ₁ →
      HasType k (τ₁ :: Γ) M τ₂ →
      HasType k Γ (lam τ₁ M) (τ₁ ⇒ τ₂)

  /-- Application -/
  | app : ∀ {k Γ M N τ₁ τ₂},
      HasType k Γ M (τ₁ ⇒ τ₂) →
      HasType k Γ N τ₁ →
      HasType k Γ (app M N) τ₂

  /-- Type abstraction -/
  | tlam : ∀ {k Γ M τ},
      HasType (k + 1) (shiftContext Γ) M τ →
      HasType k Γ (tlam M) (all τ)

  /-- Type application -/
  | tapp : ∀ {k Γ M τ σ},
      HasType k Γ M (all τ) →
      Ty.WF k σ →
      HasType k Γ (tapp M σ) (substTy0 σ τ)

/-- Notation for typing -/
scoped notation:40 k " ; " Γ " ⊢ " M " : " τ => HasType k Γ M τ

/-- Typing in empty context at depth 0 -/
scoped notation:40 "⊢ " M " : " τ => HasType 0 [] M τ

/-! ## Basic Properties -/

/-- Types in typing derivations are well-formed -/
theorem hasType_wf {k : TyVarCount} {Γ : Context} {M : Term} {τ : Ty}
    (h : k ; Γ ⊢ M : τ) (hΓ : ∀ n σ, lookup Γ n = some σ → Ty.WF k σ) : Ty.WF k τ := by
  induction h with
  | var hlook =>
    exact hΓ _ _ hlook
  | lam hτ₁ _ ih =>
    constructor
    · exact hτ₁
    · apply ih
      intro n σ hlook'
      cases n with
      | zero =>
        simp only [lookup] at hlook'
        injection hlook' with heq
        rw [← heq]
        exact hτ₁
      | succ n' =>
        simp only [lookup] at hlook'
        exact hΓ n' σ hlook'
  | app _ _ ih₁ _ =>
    have hwf := ih₁ hΓ
    exact hwf.2
  | @tlam k' Γ' M' τ' _ ih =>
    apply ih
    intro n σ hlook'
    simp only [shiftContext, lookup] at hlook'
    have hget : (List.map (shiftTyUp 1 0) Γ')[n]? = Option.map (shiftTyUp 1 0) Γ'[n]? := by
      simp only [List.getElem?_map]
    rw [hget] at hlook'
    cases hΓn : Γ'[n]? with
    | none =>
      simp only [hΓn, Option.map_none] at hlook'
      exact absurd hlook' (by simp)
    | some σ' =>
      simp only [hΓn, Option.map_some] at hlook'
      injection hlook' with heq
      rw [← heq]
      have h := hΓ n σ' hΓn
      exact WF_shiftTyUp 1 0 h
  | tapp _ hσ ih =>
    have hall := ih hΓ
    exact WF_substTy0 hall hσ

/-! ## Progress

Well-typed closed terms are either values or can step. -/

/-- Progress theorem: well-typed closed terms are values or can reduce -/
theorem progress {M : Term} {τ : Ty} (h : ⊢ M : τ) :
    IsValue M ∨ ∃ N, M ⟶ N := by
  generalize hΓ : ([] : Context) = Γ at h
  generalize hk : (0 : TyVarCount) = k at h
  induction h with
  | var hlook =>
    -- Variable in empty context is impossible
    rw [← hΓ] at hlook
    simp only [lookup] at hlook
    exact absurd hlook (Option.noConfusion)
  | lam _ _ _ =>
    left
    exact IsValue.lam _ _
  | app hfun harg ihfun iharg =>
    right
    have ihf := ihfun hΓ hk
    cases ihf with
    | inl hval =>
      cases hval with
      | lam τ' M' =>
        exact ⟨substTerm0 _ _, Step.beta _ _ _⟩
      | tlam M' =>
        -- Type error: tlam can't have arrow type
        cases hfun
    | inr hstep =>
      obtain ⟨M', hM'⟩ := hstep
      exact ⟨app M' _, Step.appL hM'⟩
  | tlam _ _ =>
    left
    exact IsValue.tlam _
  | tapp hfun hσ ihfun =>
    right
    have ihf := ihfun hΓ hk
    cases ihf with
    | inl hval =>
      cases hval with
      | lam _ _ =>
        -- Type error: lam can't have ∀ type
        cases hfun
      | tlam M' =>
        exact ⟨substTypeInTerm0 _ _, Step.tbeta _ _⟩
    | inr hstep =>
      obtain ⟨M', hM'⟩ := hstep
      exact ⟨tapp M' _, Step.tappL hM'⟩

/-! ## Examples -/

/-- The polymorphic identity has type ∀α. α → α -/
example : ⊢ polyId : idTy := by
  unfold polyId idTy
  apply HasType.tlam
  simp only [shiftContext, List.map_nil]
  apply HasType.lam
  · simp only [Ty.WF]; omega
  · apply HasType.var
    native_decide

/-- Church true has type ∀α. α → α → α -/
example : ⊢ cTrue : boolTy := by
  unfold cTrue boolTy
  apply HasType.tlam
  simp only [shiftContext, List.map_nil]
  apply HasType.lam
  · simp only [Ty.WF]; omega
  · apply HasType.lam
    · simp only [Ty.WF]; omega
    · apply HasType.var
      native_decide

/-- Church false has type ∀α. α → α → α -/
example : ⊢ cFalse : boolTy := by
  unfold cFalse boolTy
  apply HasType.tlam
  simp only [shiftContext, List.map_nil]
  apply HasType.lam
  · simp only [Ty.WF]; omega
  · apply HasType.lam
    · simp only [Ty.WF]; omega
    · apply HasType.var
      native_decide

end Metatheory.SystemF
