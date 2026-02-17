/-
# Simply Typed Lambda Calculus with Products and Sums - Types

This module defines simple types extended with products and sums.

## Overview

Simple types now include:
- Base types (e.g., Bool, Nat)
- Function types (A → B)
- Product types (A × B)
- Sum types (A + B)

## References

- Pierce, "Types and Programming Languages" (2002), Chapters 11 and 12
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
-/

namespace Metatheory.STLCext

/-! ## Simple Types with Products and Sums -/

/-- Simple types: base types, function types, products, sums, and unit -/
inductive Ty where
  | base : Nat → Ty        -- Base type indexed by natural number
  | arr  : Ty → Ty → Ty    -- Function type A → B
  | prod : Ty → Ty → Ty    -- Product type A × B
  | sum  : Ty → Ty → Ty    -- Sum type A + B
  | unit : Ty              -- Unit type (terminal object)
deriving DecidableEq, Repr

/-- Notation for function types -/
scoped infixr:70 " ⇒ " => Ty.arr

/-- Notation for product types -/
scoped infixl:75 " ⊗ " => Ty.prod

/-- Notation for sum types -/
scoped infixl:65 " ⊕ " => Ty.sum

namespace Ty

/-! ## Common Base Types -/

/-- Base type 0 (often represents Bool) -/
abbrev TBool : Ty := base 0

/-- Base type 1 (often represents Nat) -/
abbrev TNat : Ty := base 1

/-- Unit type -/
abbrev TUnit : Ty := unit

/-! ## Type Properties -/

/-- A type is ground (has no type constructors) -/
def isGround : Ty → Bool
  | base _ => true
  | arr _ _ => false
  | prod _ _ => false
  | sum _ _ => false
  | unit => true

/-- Size of a type (number of type constructors) -/
def size : Ty → Nat
  | base _ => 1
  | arr a b => 1 + size a + size b
  | prod a b => 1 + size a + size b
  | sum a b => 1 + size a + size b
  | unit => 1

/-- Depth of a type (maximum nesting) -/
def depth : Ty → Nat
  | base _ => 0
  | arr a b => 1 + max (depth a) (depth b)
  | prod a b => 1 + max (depth a) (depth b)
  | sum a b => 1 + max (depth a) (depth b)
  | unit => 0

/-! ## Type Examples -/

/-- Identity type: A → A -/
def idTy (A : Ty) : Ty := A ⇒ A

/-- Pair type: A × B -/
def pairTy (A B : Ty) : Ty := A ⊗ B

/-- Either type: A + B -/
def eitherTy (A B : Ty) : Ty := A ⊕ B

/-- Church boolean type: A → A → A -/
def churchBool (A : Ty) : Ty := A ⇒ A ⇒ A

/-- Church natural type: (A → A) → A → A -/
def churchNat (A : Ty) : Ty := (A ⇒ A) ⇒ A ⇒ A

end Ty

end Metatheory.STLCext
