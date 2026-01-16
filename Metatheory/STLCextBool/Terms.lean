/-
# Simply Typed Lambda Calculus with Booleans - Terms

This module defines lambda calculus terms extended with boolean literals
and conditional expressions, using de Bruijn indices.

## References

- Pierce, "Types and Programming Languages" (2002), Chapter 11
-/

import Metatheory.STLCextBool.Types

namespace Metatheory.STLCextBool

/-! ## Term Definition -/

/-- Lambda calculus terms with booleans. -/
inductive Term : Type where
  | var   : Nat → Term               -- Variable (de Bruijn index)
  | lam   : Term → Term              -- Lambda abstraction λ.M
  | app   : Term → Term → Term       -- Application M N
  | ttrue : Term                     -- Boolean true
  | tfalse : Term                    -- Boolean false
  | ite   : Term → Term → Term → Term -- if M then N₁ else N₂
  deriving Repr, DecidableEq

namespace Term

/-! ## Notation -/

scoped infixl:70 " @ " => Term.app
scoped prefix:max "ƛ " => Term.lam

/-! ## Shifting -/

/-- Shift free variables by d, starting from cutoff c. -/
def shift (d : Int) (c : Nat) : Term → Term
  | var n => if n < c then var n else var (Int.toNat (n + d))
  | lam M => lam (shift d (c + 1) M)
  | app M N => app (shift d c M) (shift d c N)
  | ttrue => ttrue
  | tfalse => tfalse
  | ite M N₁ N₂ => ite (shift d c M) (shift d c N₁) (shift d c N₂)

/-- Shorthand for shifting by 1 from cutoff 0. -/
abbrev shift1 (M : Term) : Term := shift 1 0 M

/-! ## Substitution -/

/-- Substitute N for variable j in M. -/
def subst (j : Nat) (N : Term) : Term → Term
  | var n =>
    if n = j then N
    else if n > j then var (n - 1)
    else var n
  | lam M => lam (subst (j + 1) (shift1 N) M)
  | app M₁ M₂ => app (subst j N M₁) (subst j N M₂)
  | ttrue => ttrue
  | tfalse => tfalse
  | ite M N₁ N₂ => ite (subst j N M) (subst j N N₁) (subst j N N₂)

/-- Substitute for variable 0. -/
abbrev subst0 (N : Term) (M : Term) : Term := subst 0 N M

/-- Substitution notation: M[N] means substitute N for var 0 in M. -/
scoped notation:max M "[" N "]" => subst0 N M

/-! ## Shift/Substitution Lemmas -/

/-- Shifting by 0 is identity. -/
theorem shift_zero (c : Nat) (M : Term) : shift 0 c M = M := by
  induction M generalizing c with
  | var n =>
    simp [shift]
  | lam M ih =>
    simp [shift, ih]
  | app M N ihM ihN =>
    simp [shift, ihM, ihN]
  | ttrue => rfl
  | tfalse => rfl
  | ite M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp [shift, ihM, ihN₁, ihN₂]

/-- Substituting at c after shifting by 1 at c cancels out. -/
theorem subst_shift_cancel (M : Term) (N : Term) (c : Nat) :
    subst c N (shift 1 c M) = M := by
  induction M generalizing c N with
  | var n =>
    by_cases hnc : n < c
    · have hne : n ≠ c := Nat.ne_of_lt hnc
      have hngt : ¬n > c := by omega
      simp [shift, subst, hnc, hne, hngt]
    · have hne : n + 1 ≠ c := by omega
      have hgt : n + 1 > c := by omega
      simp [shift, subst, hnc, hne, hgt]
  | lam M ih =>
    simp [shift, subst, ih]
  | app M N ihM ihN =>
    simp [shift, subst, ihM, ihN]
  | ttrue => rfl
  | tfalse => rfl
  | ite M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp [shift, subst, ihM, ihN₁, ihN₂]

/-- Substituting for a shifted variable cancels out. -/
theorem subst_shift1 (M N : Term) : (shift 1 0 M)[N] = M :=
  subst_shift_cancel M N 0

end Term

end Metatheory.STLCextBool
