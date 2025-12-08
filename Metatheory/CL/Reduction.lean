/-
# Combinatory Logic - Reduction

This module defines one-step and multi-step weak reduction for CL.

## Reduction Rules

- **K-reduction**: Kxy → x
- **S-reduction**: Sxyz → xz(yz)

Plus congruence rules for reducing inside applications.

## References

- Hindley & Seldin, "Lambda-Calculus and Combinators" (2008)
- Barendregt, "The Lambda Calculus" (1984), Chapter 7
-/

import Metatheory.CL.Syntax
import Metatheory.Rewriting.Basic

namespace Metatheory.CL

open Term

/-! ## One-Step Weak Reduction -/

/-- One-step weak reduction for Combinatory Logic.

    The two basic contractions are:
    - K M N → M
    - S M N P → (M P) (N P)

    Plus congruence rules for reducing inside applications. -/
inductive WeakStep : Term → Term → Prop where
  | k_red : ∀ (M N : Term), WeakStep (K ⬝ M ⬝ N) M
  | s_red : ∀ (M N P : Term), WeakStep (S ⬝ M ⬝ N ⬝ P) ((M ⬝ P) ⬝ (N ⬝ P))
  | appL : ∀ {M M' N : Term}, WeakStep M M' → WeakStep (M ⬝ N) (M' ⬝ N)
  | appR : ∀ {M N N' : Term}, WeakStep N N' → WeakStep (M ⬝ N) (M ⬝ N')

/-- Notation for one-step reduction -/
scoped infix:50 " ⟶ " => WeakStep

/-! ## Multi-Step Reduction -/

/-- Multi-step weak reduction (reflexive-transitive closure) -/
abbrev MultiStep : Term → Term → Prop := Rewriting.Star WeakStep

/-- Notation for multi-step reduction -/
scoped infix:50 " ⟶* " => MultiStep

namespace MultiStep

/-- Reflexivity -/
theorem refl (M : Term) : M ⟶* M := Rewriting.Star.refl M

/-- Single step implies multi-step -/
theorem single {M N : Term} (h : M ⟶ N) : M ⟶* N := Rewriting.Star.single h

/-- Transitivity -/
theorem trans {M N P : Term} (h1 : M ⟶* N) (h2 : N ⟶* P) : M ⟶* P :=
  Rewriting.Star.trans h1 h2

/-- Head step -/
theorem head {M N P : Term} (h1 : M ⟶ N) (h2 : N ⟶* P) : M ⟶* P :=
  Rewriting.Star.head h1 h2

/-- Tail step -/
theorem tail {M N P : Term} (h1 : M ⟶* N) (h2 : N ⟶ P) : M ⟶* P :=
  Rewriting.Star.tail h1 h2

/-- Left congruence for multi-step -/
theorem appL {M M' N : Term} (h : M ⟶* M') : (M ⬝ N) ⟶* (M' ⬝ N) := by
  induction h with
  | refl => exact refl _
  | tail _ hstep ih => exact tail ih (WeakStep.appL hstep)

/-- Right congruence for multi-step -/
theorem appR {M N N' : Term} (h : N ⟶* N') : (M ⬝ N) ⟶* (M ⬝ N') := by
  induction h with
  | refl => exact refl _
  | tail _ hstep ih => exact tail ih (WeakStep.appR hstep)

/-- Full congruence: if M ⟶* M' and N ⟶* N' then M·N ⟶* M'·N' -/
theorem app {M M' N N' : Term} (hM : M ⟶* M') (hN : N ⟶* N') :
    (M ⬝ N) ⟶* (M' ⬝ N') :=
  trans (appL hM) (appR hN)

end MultiStep

end Metatheory.CL
