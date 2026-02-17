/-
# Combinatory Logic - Syntax

This module defines the syntax of Combinatory Logic (CL), a simple
rewriting system that is Turing-complete and closely related to λ-calculus.

## Overview

Combinatory Logic uses just two primitive combinators:
- **S**: the "substitution" combinator: Sxyz → xz(yz)
- **K**: the "constant" combinator: Kxy → x

From these, all computable functions can be expressed.

## References

- Curry & Feys, "Combinatory Logic" (1958)
- Hindley & Seldin, "Lambda-Calculus and Combinators" (2008)
- Barendregt, "The Lambda Calculus" (1984), Chapter 7
-/

namespace Metatheory.CL

/-! ## Term Definition -/

/-- Combinatory Logic terms.

    Terms are built from the primitive combinators S and K,
    and application. Unlike λ-calculus, there are no binders. -/
inductive Term : Type where
  | S : Term
  | K : Term
  | app : Term → Term → Term
  deriving Repr, DecidableEq

namespace Term

/-! ## Notation -/

/-- Application notation (left-associative) -/
scoped infixl:65 " ⬝ " => Term.app

/-! ## Derived Combinators -/

/-- Identity combinator: I = SKK.
    Reduces: Ix → SKKx → Kx(Kx) → x -/
def I : Term := S ⬝ K ⬝ K

/-- Composition combinator: B = S(KS)K.
    Reduces: Bfgx → f(gx) -/
def B : Term := S ⬝ (K ⬝ S) ⬝ K

/-- Self-application: ω = SII -/
def omega_small : Term := S ⬝ I ⬝ I

/-- Non-terminating term: Ω = ωω -/
def Omega : Term := omega_small ⬝ omega_small

/-- Cardinal combinator (flip): C = S(S(KB)S)(KK) where B = S(KS)K.
    Reduces: Cxyz → xzy (swaps second and third arguments) -/
def C : Term := S ⬝ (S ⬝ (K ⬝ B) ⬝ S) ⬝ (K ⬝ K)

/-- Warbler combinator (duplicate): W = SS(SK).
    Reduces: Wxy → xyy (duplicates second argument) -/
def W : Term := S ⬝ S ⬝ (S ⬝ K)

/-! ## Size Function -/

/-- Size of a term (number of nodes in syntax tree).
    Used for termination proofs. -/
def size : Term → Nat
  | S => 1
  | K => 1
  | app M N => 1 + size M + size N

/-- Size is always positive -/
theorem size_pos (M : Term) : 0 < size M := by
  cases M <;> simp [size] <;> omega

/-- Left subterm is smaller -/
theorem size_app_left (M N : Term) : size M < size (app M N) := by
  simp [size]; omega

/-- Right subterm is smaller -/
theorem size_app_right (M N : Term) : size N < size (app M N) := by
  simp [size]; omega

end Term

end Metatheory.CL
