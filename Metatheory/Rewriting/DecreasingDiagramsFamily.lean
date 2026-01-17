/-
# Decreasing Diagrams Family (Non-Terminating)

This module defines a parameterized family of non-terminating ARSs whose
confluence is proved via decreasing diagrams. The parameter controls the
labels on the local peak while the underlying rewrite graph is fixed.
-/

import Metatheory.Rewriting.DecreasingDiagrams
import Mathlib.Order.WellFounded

namespace Metatheory.RewritingFamily

open Rewriting

/-! ## Family Definition -/

/-- States for the example rewriting system. -/
inductive Node where
  | a : Node
  | b : Node
  | c : Node
  | d : Node
  deriving DecidableEq, Repr

open Node

/-- Labeled steps for the family indexed by `n`. -/
inductive LStep (n : Nat) : Nat → Node → Node → Prop where
  | a_to_b : LStep n (n + 1) a b
  | a_to_c : LStep n (n + 1) a c
  | b_to_d : LStep n n b d
  | c_to_d : LStep n n c d
  | d_to_a : LStep n 0 d a

/-- Unlabeled step relation for the family. -/
abbrev Step (n : Nat) : Node → Node → Prop := LabeledUnion (LStep n)

/-! ## Non-Termination -/

/-- A reduction loop witnessing non-termination for any `n`. -/
theorem step_loop (n : Nat) : Plus (Step n) a a := by
  have hab : Step n a b := ⟨n + 1, LStep.a_to_b⟩
  have hbd : Step n b d := ⟨n, LStep.b_to_d⟩
  have hda : Step n d a := ⟨0, LStep.d_to_a⟩
  exact Plus.tail (Plus.tail (Plus.single hab) hbd) hda

/-- The family is not terminating (for any `n`). -/
theorem step_not_terminating (n : Nat) : ¬ Terminating (Step n) := by
  intro hterm
  exact (hterm.isIrrefl.irrefl a) (step_loop n)

/-! ## Local Decreasing -/

/-- The family is locally decreasing with respect to `<`. -/
theorem step_locallyDecreasing (n : Nat) : LocallyDecreasing (LStep n) (· < ·) := by
  intro x y z l1 l2 hxy hxz
  cases hxy <;> cases hxz
  · exact ⟨b, StarPred.refl _, StarPred.refl _⟩
  ·
    have hpred : n < n + 1 ∧ n < n + 1 := by
      exact ⟨Nat.lt_succ_self n, Nat.lt_succ_self n⟩
    exact ⟨d, StarPred.single n hpred LStep.b_to_d,
      StarPred.single n hpred LStep.c_to_d⟩
  ·
    have hpred : n < n + 1 ∧ n < n + 1 := by
      exact ⟨Nat.lt_succ_self n, Nat.lt_succ_self n⟩
    exact ⟨d, StarPred.single n hpred LStep.c_to_d,
      StarPred.single n hpred LStep.b_to_d⟩
  · exact ⟨c, StarPred.refl _, StarPred.refl _⟩
  · exact ⟨d, StarPred.refl _, StarPred.refl _⟩
  · exact ⟨d, StarPred.refl _, StarPred.refl _⟩
  · exact ⟨a, StarPred.refl _, StarPred.refl _⟩

/-! ## Confluence -/

/-- Confluence via decreasing diagrams for the whole family. -/
theorem step_confluent (n : Nat) : Confluent (Step n) := by
  apply confluent_of_locallyDecreasing (r := LStep n) (lt := (· < ·))
  · exact Nat.lt_wfRel.wf
  · exact step_locallyDecreasing n

end Metatheory.RewritingFamily
