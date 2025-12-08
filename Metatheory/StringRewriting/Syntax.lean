/-
# String Rewriting - Syntax

This module defines the syntax for a simple string rewriting system.
We use a finite alphabet and represent strings as lists.

## Overview

String rewriting (also called semi-Thue systems) is one of the simplest
forms of term rewriting, yet captures many interesting computational phenomena.

## References

- Thue, "Probleme über Veränderungen von Zeichenreihen" (1914)
- Book & Otto, "String-Rewriting Systems" (1993)
-/

namespace Metatheory.StringRewriting

/-! ## Alphabet -/

/-- A simple alphabet with two symbols -/
inductive Symbol where
  | a : Symbol
  | b : Symbol
deriving DecidableEq, Repr

open Symbol

/-- A string is a list of symbols -/
abbrev Str := List Symbol

/-! ## String Operations -/

/-- Length of a string -/
abbrev length : Str → Nat := List.length

/-! ## Pattern Matching Helpers -/

/-- Check if one string is a prefix of another -/
def isPrefix : Str → Str → Bool
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys => x == y && isPrefix xs ys

/-- Remove prefix from string if present -/
def removePrefix : Str → Str → Option Str
  | [], s => some s
  | _, [] => none
  | x :: xs, y :: ys => if x == y then removePrefix xs ys else none

/-! ## Example Strings -/

/-- Empty string -/
def ε : Str := []

/-- Single 'a' -/
def sa : Str := [a]

/-- Single 'b' -/
def sb : Str := [b]

/-- String "aa" -/
def aa : Str := [a, a]

/-- String "bb" -/
def bb : Str := [b, b]

/-- String "ab" -/
def ab : Str := [a, b]

/-- String "ba" -/
def ba : Str := [b, a]

end Metatheory.StringRewriting
