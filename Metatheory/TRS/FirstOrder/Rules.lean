/-
# First-Order TRS Rules and Rewriting

Defines rewrite rules, rule sets, and the induced one-step and multi-step
rewrite relations using positional replacement.
-/

import Metatheory.Rewriting.Basic
import Metatheory.TRS.FirstOrder.Positions
import Metatheory.TRS.FirstOrder.Syntax

namespace Metatheory.TRS.FirstOrder

open Term

/-! ## Rules -/

/-- A rewrite rule over a signature. -/
structure Rule (sig : Signature) where
  lhs : Term sig
  rhs : Term sig

noncomputable instance instDecidableEqRule {sig : Signature} : DecidableEq (Rule sig) :=
  fun _ _ => Classical.propDecidable _

/-- A set of rewrite rules. -/
abbrev RuleSet (sig : Signature) := Rule sig -> Prop

/-! ## Root Rewriting -/

/-- Root rewrite step by instantiating a rule. -/
def RootStep {sig : Signature} (rules : RuleSet sig) (s t : Term sig) : Prop :=
  ∃ r, rules r ∧ ∃ sub, s = Term.subst sub r.lhs ∧ t = Term.subst sub r.rhs

/-! ## One-step Rewriting -/

/-- One-step rewrite using a rule instance at some position. -/
def Step {sig : Signature} (rules : RuleSet sig) (s t : Term sig) : Prop :=
  ∃ r, rules r ∧ ∃ (p : Pos) (sub : Subst sig),
    Term.subterm s p = some (Term.subst sub r.lhs) ∧
    Term.replace s p (Term.subst sub r.rhs) = some t

scoped notation:50 s " ⟶[" rules "] " t => Step rules s t

/-! ## Multi-step Rewriting -/

/-- Multi-step rewrite (reflexive-transitive closure). -/
abbrev MultiStep {sig : Signature} (rules : RuleSet sig) : Term sig -> Term sig -> Prop :=
  Rewriting.Star (Step rules)

scoped notation:50 s " ⟶*[" rules "] " t => MultiStep rules s t

/-! ## Basic Lemmas -/

theorem rootStep_to_step {sig : Signature} {rules : RuleSet sig} {s t : Term sig}
    (h : RootStep rules s t) : Step rules s t := by
  rcases h with ⟨r, hr, sub, rfl, rfl⟩
  refine ⟨r, hr, [], sub, ?_, ?_⟩ <;> simp

theorem step_of_rule {sig : Signature} {rules : RuleSet sig} (r : Rule sig)
    (hr : rules r) (sub : Subst sig) :
    Step rules (Term.subst sub r.lhs) (Term.subst sub r.rhs) := by
  refine rootStep_to_step ?_
  exact ⟨r, hr, sub, rfl, rfl⟩

end Metatheory.TRS.FirstOrder
