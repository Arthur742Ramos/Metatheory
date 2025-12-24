/-
# System F Terms

This module defines terms for System F (polymorphic lambda calculus).

## Overview

System F terms extend the simply typed lambda calculus with:
- Type abstraction: Λα. M (abstracts over a type variable)
- Type application: M [τ] (applies a term to a type)

## De Bruijn Representation

Both term variables and type variables use de Bruijn indices.
This requires careful tracking of two separate binding depths.

## References

- Girard, "Interprétation fonctionnelle et élimination des coupures" (1972)
- Reynolds, "Towards a theory of type structure" (1974)
- Pierce, "Types and Programming Languages" (2002), Chapter 23
-/

import Metatheory.SystemF.Types

namespace Metatheory.SystemF

open Ty

/-! ## Term Syntax -/

/-- System F terms with de Bruijn indices for both term and type variables. -/
inductive Term : Type where
  /-- Term variable (de Bruijn index) -/
  | var : Nat → Term
  /-- Lambda abstraction with type annotation -/
  | lam : Ty → Term → Term
  /-- Application -/
  | app : Term → Term → Term
  /-- Type abstraction (Λα. M) -/
  | tlam : Term → Term
  /-- Type application (M [τ]) -/
  | tapp : Term → Ty → Term
  deriving Repr, DecidableEq

namespace Term

/-! ## Notation -/

/-- Notation for application -/
infixl:70 " ⬝ " => app

/-! ## Term Shifting (for term variables)

`shiftTermUp d c M` shifts term variable indices ≥ c by d. -/

/-- Shift term variables up by d at cutoff c -/
def shiftTermUp (d : Nat) (c : Nat) : Term → Term
  | var n => if n < c then var n else var (n + d)
  | lam τ M => lam τ (shiftTermUp d (c + 1) M)
  | app M N => app (shiftTermUp d c M) (shiftTermUp d c N)
  | tlam M => tlam (shiftTermUp d c M)
  | tapp M τ => tapp (shiftTermUp d c M) τ

/-- Shift term variables down by 1 at cutoff c -/
def shiftTermDown (c : Nat) : Term → Term
  | var n => if n < c then var n else var (n - 1)
  | lam τ M => lam τ (shiftTermDown (c + 1) M)
  | app M N => app (shiftTermDown c M) (shiftTermDown c N)
  | tlam M => tlam (shiftTermDown c M)
  | tapp M τ => tapp (shiftTermDown c M) τ

/-! ## Type Shifting in Terms

When we go under a type binder (tlam), we need to shift type indices in the term. -/

/-- Shift type variables in a term up by d at cutoff c -/
def shiftTypeInTerm (d : Nat) (c : Nat) : Term → Term
  | var n => var n
  | lam τ M => lam (shiftTyUp d c τ) (shiftTypeInTerm d c M)
  | app M N => app (shiftTypeInTerm d c M) (shiftTypeInTerm d c N)
  | tlam M => tlam (shiftTypeInTerm d (c + 1) M)
  | tapp M τ => tapp (shiftTypeInTerm d c M) (shiftTyUp d c τ)

/-! ## Term Substitution

`substTerm k N M` substitutes N for term variable k in M. -/

/-- Substitute term N for term variable k in term M -/
def substTerm (k : Nat) (N : Term) : Term → Term
  | var n =>
    if n < k then var n
    else if n = k then N
    else var (n - 1)
  | lam τ M => lam τ (substTerm (k + 1) (shiftTermUp 1 0 N) M)
  | app M₁ M₂ => app (substTerm k N M₁) (substTerm k N M₂)
  | tlam M => tlam (substTerm k (shiftTypeInTerm 1 0 N) M)
  | tapp M τ => tapp (substTerm k N M) τ

/-- Substitute for term variable 0 -/
abbrev substTerm0 (N M : Term) : Term := substTerm 0 N M

/-! ## Type Substitution in Terms

`substTypeInTerm k σ M` substitutes type σ for type variable k in term M. -/

/-- Substitute type σ for type variable k in term M -/
def substTypeInTerm (k : Nat) (σ : Ty) : Term → Term
  | var n => var n
  | lam τ M => lam (substTy k σ τ) (substTypeInTerm k σ M)
  | app M N => app (substTypeInTerm k σ M) (substTypeInTerm k σ N)
  | tlam M => tlam (substTypeInTerm (k + 1) (shiftTyUp 1 0 σ) M)
  | tapp M τ => tapp (substTypeInTerm k σ M) (substTy k σ τ)

/-- Substitute for type variable 0 in term -/
abbrev substTypeInTerm0 (σ : Ty) (M : Term) : Term := substTypeInTerm 0 σ M

/-! ## Values

In System F, values are lambda abstractions and type abstractions. -/

/-- Predicate for values -/
inductive IsValue : Term → Prop where
  | lam : ∀ τ M, IsValue (lam τ M)
  | tlam : ∀ M, IsValue (tlam M)

/-! ## Small-Step Reduction -/

/-- Single-step β-reduction for System F -/
inductive Step : Term → Term → Prop where
  /-- Term β-reduction: (λx:τ. M) N → M[N/x] -/
  | beta : ∀ τ M N, Step (app (lam τ M) N) (substTerm0 N M)
  /-- Type β-reduction: (Λα. M) [τ] → M[τ/α] -/
  | tbeta : ∀ M τ, Step (tapp (tlam M) τ) (substTypeInTerm0 τ M)
  /-- Congruence: application left -/
  | appL : ∀ {M M' N}, Step M M' → Step (app M N) (app M' N)
  /-- Congruence: application right -/
  | appR : ∀ {M N N'}, Step N N' → Step (app M N) (app M N')
  /-- Congruence: type application -/
  | tappL : ∀ {M M' τ}, Step M M' → Step (tapp M τ) (tapp M' τ)

/-- Notation for reduction -/
scoped infix:50 " ⟶ " => Step

/-! ## Multi-Step Reduction -/

/-- Reflexive-transitive closure of reduction -/
inductive MultiStep : Term → Term → Prop where
  | refl : ∀ M, MultiStep M M
  | step : ∀ {M N P}, Step M N → MultiStep N P → MultiStep M P

/-- Notation for multi-step reduction -/
scoped infix:50 " ⟶* " => MultiStep

namespace MultiStep

/-- Single step implies multi-step -/
theorem single {M N : Term} (h : M ⟶ N) : M ⟶* N :=
  MultiStep.step h (MultiStep.refl N)

/-- Transitivity -/
theorem trans {M N P : Term} (h1 : M ⟶* N) (h2 : N ⟶* P) : M ⟶* P := by
  induction h1 with
  | refl => exact h2
  | step hstep _ ih => exact MultiStep.step hstep (ih h2)

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

/-- Congruence: type application -/
theorem tappL {M M' : Term} {τ : Ty} (h : M ⟶* M') : tapp M τ ⟶* tapp M' τ := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (Step.tappL hstep) ih

end MultiStep

/-! ## Examples -/

/-- The polymorphic identity: Λα. λx:α. x -/
def polyId : Term := tlam (lam (tvar 0) (var 0))

/-- Church true: Λα. λx:α. λy:α. x -/
def cTrue : Term := tlam (lam (tvar 0) (lam (tvar 0) (var 1)))

/-- Church false: Λα. λx:α. λy:α. y -/
def cFalse : Term := tlam (lam (tvar 0) (lam (tvar 0) (var 0)))

/-- Church zero: Λα. λf:α→α. λx:α. x -/
def cZero : Term := tlam (lam (tvar 0 ⇒ tvar 0) (lam (tvar 0) (var 0)))

/-- Church successor -/
def cSucc : Term :=
  lam natTy (tlam (lam (tvar 0 ⇒ tvar 0) (lam (tvar 0)
    (app (var 1) (app (app (tapp (var 3) (tvar 0)) (var 1)) (var 0))))))

/-- polyId is a value -/
theorem polyId_isValue : IsValue polyId := IsValue.tlam _

/-- Applying polyId to a type gives a lambda -/
example (τ : Ty) : tapp polyId τ ⟶ lam τ (var 0) := by
  apply Step.tbeta

end Term

end Metatheory.SystemF
