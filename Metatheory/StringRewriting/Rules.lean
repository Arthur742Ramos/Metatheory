/-
# String Rewriting - Rules

This module defines the rewriting rules for our simple string rewriting system.

## Rule Set

We use a simple idempotent reduction system:
- aa → a (double 'a' reduces to single 'a')
- bb → b (double 'b' reduces to single 'b')

This system is:
1. **Terminating**: Each step strictly reduces string length
2. **Locally confluent**: Critical pairs are joinable

Therefore by Newman's lemma, the system is confluent.

## References

- Book & Otto, "String-Rewriting Systems" (1993)
-/

import Metatheory.StringRewriting.Syntax
import Metatheory.Rewriting.Basic

namespace Metatheory.StringRewriting

open Symbol

/-! ## Rewriting Rules -/

/-- Single-step rewriting relation.

    A step rewrites a substring by one of the rules:
    - [a, a] → [a]
    - [b, b] → [b]

    The step can occur at any position in the string. -/
inductive Step : Str → Str → Prop where
  | aa_rule : ∀ (l r : Str), Step (l ++ [a, a] ++ r) (l ++ [a] ++ r)
  | bb_rule : ∀ (l r : Str), Step (l ++ [b, b] ++ r) (l ++ [b] ++ r)

/-- Notation for single-step reduction -/
scoped infix:50 " ⟶ " => Step

/-! ## Multi-step Reduction -/

/-- Multi-step reduction (reflexive-transitive closure) -/
abbrev MultiStep : Str → Str → Prop := Rewriting.Star Step

/-- Notation for multi-step reduction -/
scoped infix:50 " ⟶* " => MultiStep

/-! ## Basic Properties -/

/-- Rewriting reduces string length by 1 -/
theorem step_length {s t : Str} (h : s ⟶ t) : t.length + 1 = s.length := by
  cases h with
  | aa_rule l r =>
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  | bb_rule l r =>
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- Steps are proper: source ≠ target -/
theorem step_ne {s t : Str} (h : s ⟶ t) : s ≠ t := by
  intro heq
  have hlen := step_length h
  rw [heq] at hlen
  omega

/-! ## Context Rules -/

/-- Left context: if s ⟶ t then l ++ s ⟶ l ++ t -/
theorem step_context_left {s t : Str} (l : Str) (h : s ⟶ t) : l ++ s ⟶ l ++ t := by
  cases h with
  | aa_rule l' r =>
    simp only [← List.append_assoc]
    exact Step.aa_rule (l ++ l') r
  | bb_rule l' r =>
    simp only [← List.append_assoc]
    exact Step.bb_rule (l ++ l') r

/-- Right context: if s ⟶ t then s ++ r ⟶ t ++ r -/
theorem step_context_right {s t : Str} (r : Str) (h : s ⟶ t) : s ++ r ⟶ t ++ r := by
  cases h with
  | aa_rule l r' =>
    have h1 : (l ++ [a, a] ++ r') ++ r = l ++ [a, a] ++ (r' ++ r) := by
      simp [List.append_assoc]
    have h2 : (l ++ [a] ++ r') ++ r = l ++ [a] ++ (r' ++ r) := by
      simp [List.append_assoc]
    rw [h1, h2]
    exact Step.aa_rule l (r' ++ r)
  | bb_rule l r' =>
    have h1 : (l ++ [b, b] ++ r') ++ r = l ++ [b, b] ++ (r' ++ r) := by
      simp [List.append_assoc]
    have h2 : (l ++ [b] ++ r') ++ r = l ++ [b] ++ (r' ++ r) := by
      simp [List.append_assoc]
    rw [h1, h2]
    exact Step.bb_rule l (r' ++ r)

/-! ## Multi-step Context Rules -/

/-- Multi-step left context -/
theorem multi_context_left {s t : Str} (l : Str) (h : s ⟶* t) : l ++ s ⟶* l ++ t := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hst ih => exact Rewriting.Star.tail ih (step_context_left l hst)

/-- Multi-step right context -/
theorem multi_context_right {s t : Str} (r : Str) (h : s ⟶* t) : s ++ r ⟶* t ++ r := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hst ih => exact Rewriting.Star.tail ih (step_context_right r hst)

end Metatheory.StringRewriting
