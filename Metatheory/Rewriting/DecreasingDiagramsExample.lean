/-
# Decreasing Diagrams Example (Non-Terminating)

This module gives a small non-terminating ARS whose confluence is proved
using decreasing diagrams. The system has a single local peak that is
closed by strictly smaller labels.
-/

import Metatheory.Rewriting.DecreasingDiagrams
import Mathlib.Order.WellFounded

namespace Metatheory.RewritingExample

open Rewriting

/-! ## Example System -/

/-- States for the example rewriting system. -/
inductive Node where
  | a : Node
  | b : Node
  | c : Node
  | d : Node
  deriving DecidableEq, Repr

open Node

/-- Labeled steps for a non-terminating but confluent system. -/
inductive LStep : Nat → Node → Node → Prop where
  | a_to_b : LStep 2 a b
  | a_to_c : LStep 2 a c
  | b_to_d : LStep 1 b d
  | c_to_d : LStep 1 c d
  | d_to_a : LStep 0 d a

/-- Unlabeled step relation. -/
abbrev Step : Node → Node → Prop := LabeledUnion LStep

/-! ## Non-Termination -/

/-- A reduction loop witnessing non-termination. -/
theorem step_loop : Plus Step a a := by
  have hab : Step a b := ⟨2, LStep.a_to_b⟩
  have hbd : Step b d := ⟨1, LStep.b_to_d⟩
  have hda : Step d a := ⟨0, LStep.d_to_a⟩
  exact Plus.tail (Plus.tail (Plus.single hab) hbd) hda

/-- The system is not terminating. -/
theorem step_not_terminating : ¬ Terminating Step := by
  intro hterm
  have hloop : Plus Step a a := step_loop
  exact (hterm.isIrrefl.irrefl a) hloop

/-! ## Local Decreasing -/

/-- The labeled system is locally decreasing with respect to `<`. -/
theorem step_locallyDecreasing : LocallyDecreasing LStep (· < ·) := by
  intro x y z l1 l2 hxy hxz
  cases hxy <;> cases hxz
  · exact ⟨b, StarPred.refl _, StarPred.refl _⟩
  ·
    have hpred : (1 : Nat) < 2 ∧ (1 : Nat) < 2 := by decide
    exact ⟨d, StarPred.single 1 hpred LStep.b_to_d,
      StarPred.single 1 hpred LStep.c_to_d⟩
  ·
    have hpred : (1 : Nat) < 2 ∧ (1 : Nat) < 2 := by decide
    exact ⟨d, StarPred.single 1 hpred LStep.c_to_d,
      StarPred.single 1 hpred LStep.b_to_d⟩
  · exact ⟨c, StarPred.refl _, StarPred.refl _⟩
  · exact ⟨d, StarPred.refl _, StarPred.refl _⟩
  · exact ⟨d, StarPred.refl _, StarPred.refl _⟩
  · exact ⟨a, StarPred.refl _, StarPred.refl _⟩

/-! ## Confluence -/

/-- Confluence via decreasing diagrams (non-terminating example). -/
theorem step_confluent : Confluent Step := by
  apply confluent_of_locallyDecreasing (r := LStep) (lt := (· < ·))
  · exact Nat.lt_wfRel.wf
  · exact step_locallyDecreasing

/-! ## Normal Forms -/

/-- No node is a normal form in this system. -/
theorem no_normalForm (x : Node) : ¬ Rewriting.IsNormalForm Step x := by
  intro hnf
  cases x with
  | a => exact hnf b ⟨2, LStep.a_to_b⟩
  | b => exact hnf d ⟨1, LStep.b_to_d⟩
  | c => exact hnf d ⟨1, LStep.c_to_d⟩
  | d => exact hnf a ⟨0, LStep.d_to_a⟩

/-- `a` is not a normal form. -/
theorem no_normalForm_a : ¬ Rewriting.IsNormalForm Step a :=
  no_normalForm a

/-- No term has a normal form in this system. -/
theorem no_hasNormalForm (x : Node) : ¬ Rewriting.HasNormalForm Step x := by
  intro hnf
  rcases hnf with ⟨n, _, hnnf⟩
  exact no_normalForm n hnnf

/-- `a` has no normal form. -/
theorem no_hasNormalForm_a : ¬ Rewriting.HasNormalForm Step a :=
  no_hasNormalForm a

end Metatheory.RewritingExample
