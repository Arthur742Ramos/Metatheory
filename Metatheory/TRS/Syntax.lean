/-
# Simple Expression Syntax

This module defines a simple expression language for demonstrating
term rewriting system confluence.

## The Language

We use a simple language with:
- Constants: 0, 1
- Binary operations: + (add), * (mul)

This allows us to define rewriting rules like:
- x + 0 → x (additive identity)
- x * 1 → x (multiplicative identity)
- x * 0 → 0 (zero annihilation)
- 0 + x → x, 1 * x → x (symmetric identities)

## Purpose

This serves as a second case study to demonstrate the generic
rewriting framework, complementing the lambda calculus example.
-/

namespace Metatheory.TRS

/-! ## Expression Syntax -/

/-- Simple arithmetic expressions -/
inductive Expr : Type where
  | zero : Expr                    -- 0
  | one : Expr                     -- 1
  | var : Nat → Expr               -- Variables x₀, x₁, ...
  | add : Expr → Expr → Expr       -- e₁ + e₂
  | mul : Expr → Expr → Expr       -- e₁ * e₂
  deriving Repr, DecidableEq

namespace Expr

/-! ## Notation -/

scoped notation "𝟬" => Expr.zero
scoped notation "𝟭" => Expr.one
scoped infixl:65 " ⊕ " => Expr.add
scoped infixl:70 " ⊛ " => Expr.mul

/-! ## Size Measure

We define a size measure to prove termination of our rewriting rules.
The key insight is that our rules reduce expression size.
-/

/-- Size of an expression (number of constructors) -/
def size : Expr → Nat
  | zero => 1
  | one => 1
  | var _ => 1
  | add e₁ e₂ => 1 + size e₁ + size e₂
  | mul e₁ e₂ => 1 + size e₁ + size e₂

/-- Size is always positive -/
theorem size_pos (e : Expr) : size e > 0 := by
  induction e <;> simp [size] <;> omega

/-! ## Example Expressions -/

/-- Variable 0 -/
def x : Expr := var 0

/-- Variable 1 -/
def y : Expr := var 1

/-- Example: x + 0 -/
def ex1 : Expr := x ⊕ 𝟬

/-- Example: (x * 1) + 0 -/
def ex2 : Expr := (x ⊛ 𝟭) ⊕ 𝟬

/-- Example: 0 * (x + y) -/
def ex3 : Expr := 𝟬 ⊛ (x ⊕ y)

end Expr

end Metatheory.TRS
