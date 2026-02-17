/-
# Simply Typed Lambda Calculus - Types

This module defines simple types for the simply typed lambda calculus (STLC).

## Overview

Simple types consist of:
- Base types (e.g., Bool, Nat)
- Function types (A → B)

## References

- Pierce, "Types and Programming Languages" (2002)
- Barendregt, "Lambda Calculi with Types" (1992)
-/

namespace Metatheory.STLC

/-! ## Simple Types -/

/-- Simple types: base types and function types -/
inductive Ty where
  | base : Nat → Ty        -- Base type indexed by natural number
  | arr  : Ty → Ty → Ty    -- Function type A → B
deriving DecidableEq, Repr

/-- Notation for function types -/
scoped infixr:70 " ⇒ " => Ty.arr

namespace Ty

/-! ## Common Base Types -/

/-- Base type 0 (often represents Bool) -/
abbrev TBool : Ty := base 0

/-- Base type 1 (often represents Nat) -/
abbrev TNat : Ty := base 1

/-! ## Type Properties -/

/-- A type is ground (has no arrows) -/
def isGround : Ty → _root_.Bool
  | base _ => true
  | arr _ _ => false

/-- Size of a type (number of type constructors) -/
def size : Ty → _root_.Nat
  | base _ => 1
  | arr a b => 1 + size a + size b

/-- Depth of a type (maximum nesting of arrows) -/
def depth : Ty → _root_.Nat
  | base _ => 0
  | arr a b => 1 + max (depth a) (depth b)

/-! ## Type Examples -/

/-- Identity type: A → A -/
def idTy (A : Ty) : Ty := A ⇒ A

/-- Church boolean type: A → A → A -/
def churchBool (A : Ty) : Ty := A ⇒ A ⇒ A

/-- Church natural type: (A → A) → A → A -/
def churchNat (A : Ty) : Ty := (A ⇒ A) ⇒ A ⇒ A

end Ty

end Metatheory.STLC
