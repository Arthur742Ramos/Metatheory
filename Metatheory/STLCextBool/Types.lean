/-
# Simply Typed Lambda Calculus with Booleans - Types

This module defines simple types extended with a dedicated boolean type.

## Overview

Simple types include:
- Base types (e.g., Bool, Nat)
- Function types (A → B)
- Boolean type

## References

- Pierce, "Types and Programming Languages" (2002)
-/

namespace Metatheory.STLCextBool

/-! ## Simple Types with Booleans -/

/-- Simple types: base types, function types, and booleans. -/
inductive Ty where
  | base : Nat → Ty        -- Base type indexed by natural number
  | arr  : Ty → Ty → Ty    -- Function type A → B
  | bool : Ty              -- Boolean type
  deriving DecidableEq, Repr

/-- Notation for function types. -/
scoped infixr:70 " ⇒ " => Ty.arr

namespace Ty

/-! ## Common Base Types -/

/-- Base type 0 (often represents Nat). -/
abbrev TNat : Ty := base 0

/-- Boolean type alias. -/
abbrev TBool : Ty := bool

end Ty

end Metatheory.STLCextBool
