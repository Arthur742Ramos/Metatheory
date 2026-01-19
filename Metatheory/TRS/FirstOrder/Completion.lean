/-
# Knuth-Bendix Completion (Abstract)

This module provides a lightweight, abstract completion relation that
adds oriented critical pairs as rewrite rules. Soundness is delegated
to the Knuth-Bendix confluence criterion proved in `Confluence.lean`.
-/

import Metatheory.Rewriting.Basic
import Metatheory.TRS.FirstOrder.Confluence
import Metatheory.TRS.FirstOrder.CriticalPairs

namespace Metatheory.TRS.FirstOrder

open Term

/-! ## Completion Steps -/

/-- Add a rule to a rule set. -/
def addRule {sig : Signature} (rules : RuleSet sig) (r0 : Rule sig) : RuleSet sig :=
  fun r => rules r ∨ r = r0

/-- A critical pair is oriented by an ordering into a rule. -/
def Oriented {sig : Signature} (ord : ReductionOrdering sig)
    (cp : CriticalPair sig) (r : Rule sig) : Prop :=
  (r.lhs = cp.left ∧ r.rhs = cp.right ∧ ord.lt cp.right cp.left) ∨
  (r.lhs = cp.right ∧ r.rhs = cp.left ∧ ord.lt cp.left cp.right)

/-- Oriented rules satisfy the ordering direction. -/
theorem oriented_lt {sig : Signature} {ord : ReductionOrdering sig}
    {cp : CriticalPair sig} {r : Rule sig} (h : Oriented ord cp r) :
    ord.lt r.rhs r.lhs := by
  rcases h with ⟨hl, hr, hlt⟩ | ⟨hl, hr, hlt⟩
  · simpa [hl, hr] using hlt
  · simpa [hl, hr] using hlt

/-- One completion step: orient a critical pair into a new rule. -/
inductive CompletionStep {sig : Signature} (ord : ReductionOrdering sig) :
    RuleSet sig → RuleSet sig → Prop where
  | orient {rules : RuleSet sig} {cp : CriticalPair sig} {r : Rule sig} :
      CriticalPairs rules cp → Oriented ord cp r →
      CompletionStep ord rules (addRule rules r)

/-- Reflexive-transitive closure of completion steps. -/
abbrev Completion {sig : Signature} (ord : ReductionOrdering sig) :
    RuleSet sig → RuleSet sig → Prop :=
  Rewriting.Star (CompletionStep ord)

/-! ## Soundness -/

/-- If completion yields a Knuth-Bendix complete system, it is confluent. -/
theorem completion_sound {sig : Signature} {ord : ReductionOrdering sig}
    {rules rules' : RuleSet sig}
    (hcomp : Completion ord rules rules')
    (hkb : KnuthBendixComplete (rules := rules') ord) :
    Confluent rules' := by
  exact confluent_of_knuthBendixComplete hkb

/-! ## List-based Completion -/

/-- Orient a critical pair using a reduction ordering. -/
noncomputable def orientCriticalPair {sig : Signature} (ord : ReductionOrdering sig)
    (cp : CriticalPair sig) : Option (Rule sig) := by
  classical
  by_cases h : ord.lt cp.right cp.left
  · exact some { lhs := cp.left, rhs := cp.right }
  by_cases h' : ord.lt cp.left cp.right
  · exact some { lhs := cp.right, rhs := cp.left }
  exact none

theorem orientCriticalPair_oriented {sig : Signature} {ord : ReductionOrdering sig}
    {cp : CriticalPair sig} {r : Rule sig} :
    orientCriticalPair ord cp = some r → Oriented ord cp r := by
  classical
  unfold orientCriticalPair
  by_cases h : ord.lt cp.right cp.left
  · intro hr
    simp [h] at hr
    cases hr
    exact Or.inl ⟨rfl, rfl, h⟩
  ·
    by_cases h' : ord.lt cp.left cp.right
    · intro hr
      simp [h, h'] at hr
      cases hr
      exact Or.inr ⟨rfl, rfl, h'⟩
    ·
      intro hr
      simp [h, h'] at hr

/-- Orient all critical pairs from a list. -/
noncomputable def orientCriticalPairs {sig : Signature} (ord : ReductionOrdering sig)
    (cps : List (CriticalPair sig)) : List (Rule sig) :=
  cps.filterMap (orientCriticalPair ord)

/-- One batch completion step on a finite rule list. -/
noncomputable def completionStepList {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) (rules : RuleList sig) : RuleList sig :=
  rules ++ orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules)

end Metatheory.TRS.FirstOrder
