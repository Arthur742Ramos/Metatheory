/-
# Knuth-Bendix Completion (Core)

This module provides a small, self-contained completion layer over the
first-order critical-pair infrastructure. It keeps the executable core used by
the case-study modules:

- orienting critical pairs into rules
- performing one list-based completion step
- iterating completion and bounded completion-by-fuel
- extracting confluence once a fixpoint is reached

The previous version of this file contained a much larger experimental
development with dependencies on unavailable tactics. The current version keeps
the stable API that the repo actually uses and restricts itself to elementary,
fully checked proofs.
-/

import Metatheory.Rewriting.Basic
import Metatheory.TRS.FirstOrder.Confluence
import Metatheory.TRS.FirstOrder.CriticalPairs

namespace Metatheory.TRS.FirstOrder

open Term

/-! ## Abstract Completion Steps -/

/-- Add a rule to a rule set. -/
def addRule {sig : Signature} (rules : RuleSet sig) (r₀ : Rule sig) : RuleSet sig :=
  fun r => rules r ∨ r = r₀

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

/-- If completion yields a Knuth-Bendix complete system, it is confluent. -/
theorem completion_sound {sig : Signature} {ord : ReductionOrdering sig}
    {rules rules' : RuleSet sig}
    (_hcomp : Completion ord rules rules')
    (hkb : KnuthBendixComplete (rules := rules') ord) :
    Confluent rules' := by
  exact confluent_of_knuthBendixComplete hkb

/-! ## List-Based Completion -/

/-- Orient a critical pair using a reduction ordering. -/
noncomputable def orientCriticalPair {sig : Signature} (ord : ReductionOrdering sig)
    (cp : CriticalPair sig) : Option (Rule sig) := by
  classical
  by_cases h₁ : ord.lt cp.right cp.left
  · exact some { lhs := cp.left, rhs := cp.right }
  · by_cases h₂ : ord.lt cp.left cp.right
    · exact some { lhs := cp.right, rhs := cp.left }
    · exact none

/-- A successful orientation produces an oriented rule. -/
theorem orientCriticalPair_oriented {sig : Signature} {ord : ReductionOrdering sig}
    {cp : CriticalPair sig} {r : Rule sig} :
    orientCriticalPair ord cp = some r → Oriented ord cp r := by
  classical
  unfold orientCriticalPair
  by_cases h₁ : ord.lt cp.right cp.left
  · intro hr
    simp [h₁] at hr
    cases hr
    exact Or.inl ⟨rfl, rfl, h₁⟩
  · by_cases h₂ : ord.lt cp.left cp.right
    · intro hr
      simp [h₁, h₂] at hr
      cases hr
      exact Or.inr ⟨rfl, rfl, h₂⟩
    · intro hr
      simp [h₁, h₂] at hr

/-- Orient all critical pairs from a list. -/
noncomputable def orientCriticalPairs {sig : Signature} (ord : ReductionOrdering sig)
    (cps : List (CriticalPair sig)) : List (Rule sig) :=
  cps.filterMap (orientCriticalPair ord)

/-- One batch completion step on a finite rule list. -/
noncomputable def completionStepList {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) (rules : RuleList sig) : RuleList sig :=
  rules ++ orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules)

/-- Iterate the list-based completion step `n` times. -/
noncomputable def completionIter {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) : Nat → RuleList sig → RuleList sig
  | 0, rules => rules
  | n + 1, rules => completionIter ord n (completionStepList ord rules)

/-- A rule in one completion step is either old or comes from an oriented critical pair. -/
theorem mem_completionStepList {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {r : Rule sig} :
    r ∈ completionStepList ord rules →
    r ∈ rules ∨ ∃ cp, cp ∈ criticalPairsOfRules (sig := sig) rules ∧
      orientCriticalPair ord cp = some r := by
  intro hmem
  rcases List.mem_append.1 hmem with hmem | hmem
  · exact Or.inl hmem
  · rcases List.mem_filterMap.1 hmem with ⟨cp, hcp, horient⟩
    exact Or.inr ⟨cp, hcp, horient⟩

/-- Every newly added rule in one completion step is oriented from a critical pair. -/
theorem completionStepList_oriented {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {r : Rule sig} :
    r ∈ completionStepList ord rules →
    r ∈ rules ∨ ∃ cp, cp ∈ criticalPairsOfRules (sig := sig) rules ∧ Oriented ord cp r := by
  intro hmem
  rcases mem_completionStepList (ord := ord) (rules := rules) hmem with hmem | hmem
  · exact Or.inl hmem
  · rcases hmem with ⟨cp, hcp, horient⟩
    exact Or.inr ⟨cp, hcp, orientCriticalPair_oriented horient⟩

/-- One completion step preserves membership of old rules. -/
theorem completionStepList_subset {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} :
    ∀ r, r ∈ rules → r ∈ completionStepList ord rules := by
  intro r hmem
  exact List.mem_append.2 (Or.inl hmem)

/-- A fixpoint adds no genuinely new oriented rules. -/
def isFixpoint {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) (rules : RuleList sig) : Prop :=
  ∀ r, r ∈ orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules) → r ∈ rules

noncomputable instance instDecidableIsFixpoint {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) (rules : RuleList sig) : Decidable (isFixpoint ord rules) := by
  classical
  infer_instance

/-- At a fixpoint, one completion step has the same membership relation. -/
theorem completionStepList_fixpoint {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hfix : isFixpoint ord rules) :
    ∀ r, r ∈ completionStepList ord rules ↔ r ∈ rules := by
  intro r
  constructor
  · intro hmem
    rcases List.mem_append.1 hmem with hmem | hmem
    · exact hmem
    · exact hfix r hmem
  · intro hmem
    exact List.mem_append.2 (Or.inl hmem)

/-- One completion step unfolds one iteration. -/
theorem completionIter_succ_eq_step {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} (n : Nat) (rules : RuleList sig) :
    completionIter ord (n + 1) rules =
      completionStepList ord (completionIter ord n rules) := by
  induction n generalizing rules with
  | zero =>
      simp [completionIter, completionStepList]
  | succ n ih =>
      calc
        completionIter ord (Nat.succ (Nat.succ n)) rules
            = completionIter ord (Nat.succ n) (completionStepList ord rules) := by
                simp [completionIter]
        _ = completionStepList ord (completionIter ord n (completionStepList ord rules)) := by
                simpa using ih (rules := completionStepList ord rules)
        _ = completionStepList ord (completionIter ord (Nat.succ n) rules) := by
                simp [completionIter]

/-- Initial rules remain present in every completion iteration. -/
theorem completionIter_subset {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {n : Nat} :
    ∀ r, r ∈ rules → r ∈ completionIter ord n rules := by
  induction n generalizing rules with
  | zero =>
      intro r hmem
      simpa [completionIter] using hmem
  | succ n ih =>
      intro r hmem
      simp only [completionIter]
      exact ih (rules := completionStepList ord rules) r (completionStepList_subset (ord := ord) r hmem)

/-- Orientation of the initial rules is preserved by completion iteration. -/
theorem completionIter_oriented {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} :
    (∀ r, r ∈ rules → ord.lt r.rhs r.lhs) →
    ∀ n r, r ∈ completionIter ord n rules → ord.lt r.rhs r.lhs := by
  intro hinit n
  induction n generalizing rules with
  | zero =>
      intro r hmem
      simpa [completionIter] using hinit r hmem
  | succ n ih =>
      intro r hmem
      simp only [completionIter] at hmem
      have hstep : ∀ r, r ∈ completionStepList ord rules → ord.lt r.rhs r.lhs := by
        intro r hr
        rcases completionStepList_oriented (ord := ord) (rules := rules) hr with hr | ⟨cp, _, horient⟩
        · exact hinit r hr
        · exact oriented_lt horient
      exact ih (rules := completionStepList ord rules) hstep r hmem

/-! ## Completion with Fuel -/

/-- Completion result: either a fixpoint was reached or fuel ran out. -/
inductive CompletionResult (sig : Signature) where
  | complete : RuleList sig → CompletionResult sig
  | incomplete : RuleList sig → CompletionResult sig

/-- Completion with bounded iterations. -/
noncomputable def completionWithFuel {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) : Nat → RuleList sig → CompletionResult sig
  | 0, rules => CompletionResult.incomplete rules
  | n + 1, rules => by
      classical
      exact if h : isFixpoint ord rules then
        CompletionResult.complete rules
      else
        completionWithFuel ord n (completionStepList ord rules)

/-- Unfold one positive-fuel completion step. -/
theorem completionWithFuel_succ {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) (n : Nat) (rules : RuleList sig) :
    completionWithFuel ord (n + 1) rules =
      if isFixpoint ord rules then
        CompletionResult.complete rules
      else
        completionWithFuel ord n (completionStepList ord rules) := by
  rfl

/-- A completed result is a fixpoint. -/
theorem completionWithFuel_complete_isFixpoint {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {fuel : Nat} {rules result : RuleList sig}
    (h : completionWithFuel ord fuel rules = CompletionResult.complete result) :
    isFixpoint ord result := by
  induction fuel generalizing rules with
  | zero =>
      simp [completionWithFuel] at h
  | succ n ih =>
      classical
      by_cases hfix : isFixpoint ord rules
      · simp [completionWithFuel, hfix] at h
        cases h
        exact hfix
      · simp [completionWithFuel, hfix] at h
        exact ih h

/-- If completion runs out of fuel, the result is the corresponding iteration. -/
theorem completionWithFuel_incomplete_eq_iter {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {fuel : Nat} {rules result : RuleList sig}
    (h : completionWithFuel ord fuel rules = CompletionResult.incomplete result) :
    result = completionIter ord fuel rules := by
  induction fuel generalizing rules with
  | zero =>
      simpa [completionWithFuel, completionIter] using h.symm
  | succ n ih =>
      classical
      by_cases hfix : isFixpoint ord rules
      · simp [completionWithFuel, hfix] at h
      · simp [completionWithFuel, hfix] at h
        simpa [completionIter] using ih h

/-- A successful completion result is some completion iterate. -/
theorem completionWithFuel_complete_exists_iter {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {fuel : Nat} {rules result : RuleList sig}
    (h : completionWithFuel ord fuel rules = CompletionResult.complete result) :
    ∃ k ≤ fuel, result = completionIter ord k rules := by
  induction fuel generalizing rules result with
  | zero =>
      simp [completionWithFuel] at h
  | succ n ih =>
      classical
      by_cases hfix : isFixpoint ord rules
      · simp [completionWithFuel, hfix] at h
        cases h
        refine ⟨0, Nat.zero_le _, ?_⟩
        simp [completionIter]
      · simp [completionWithFuel, hfix] at h
        rcases ih h with ⟨k, hk, hres⟩
        refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
        simpa [completionIter] using hres

/-- If completion terminates, the result appears at some completion iterate. -/
theorem completion_terminates_of_iter {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules result : RuleList sig} {fuel : Nat}
    (h : completionWithFuel ord fuel rules = CompletionResult.complete result) :
    ∃ n, result = completionIter ord n rules := by
  rcases completionWithFuel_complete_exists_iter (ord := ord) (rules := rules) (result := result) h with
    ⟨n, _, hres⟩
  exact ⟨n, hres⟩

/-- Every rule in a successful completion result satisfies the orientation ordering. -/
theorem completionWithFuel_oriented {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {fuel : Nat} {rules result : RuleList sig}
    (hinit : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (h : completionWithFuel ord fuel rules = CompletionResult.complete result) :
    ∀ r, r ∈ result → ord.lt r.rhs r.lhs := by
  induction fuel generalizing rules with
  | zero =>
      simp [completionWithFuel] at h
  | succ n ih =>
      classical
      by_cases hfix : isFixpoint ord rules
      · simp [completionWithFuel, hfix] at h
        cases h
        exact hinit
      · simp [completionWithFuel, hfix] at h
        apply ih
        · intro r hr
          rcases completionStepList_oriented (ord := ord) (rules := rules) hr with hr | ⟨cp, _, horient⟩
          · exact hinit r hr
          · exact oriented_lt horient
        · exact h

/-! ## Fixpoint Soundness -/

/-- If a critical pair is oriented at a fixpoint, the resulting rule is already present. -/
theorem fixpoint_oriented_mem {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hfix : isFixpoint ord rules)
    {cp : CriticalPair sig} {r : Rule sig}
    (hcp : cp ∈ criticalPairsOfRules (sig := sig) rules)
    (horient : orientCriticalPair ord cp = some r) :
    r ∈ rules := by
  have hmem : r ∈ orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules) := by
    exact List.mem_filterMap.2 ⟨cp, hcp, horient⟩
  exact hfix r hmem

/-- At a fixpoint, an orientable critical pair is joinable in one step on one branch. -/
theorem joinable_of_fixpoint_orientable {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {cp : CriticalPair sig}
    (hfix : isFixpoint ord rules)
    (hcp : cp ∈ criticalPairsOfRules (sig := sig) rules)
    (horient : ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    Joinable (ruleSetOfList (sig := sig) rules) cp.left cp.right := by
  classical
  by_cases hgt : ord.lt cp.right cp.left
  ·
    let r : Rule sig := { lhs := cp.left, rhs := cp.right }
    have horient' : orientCriticalPair ord cp = some r := by
      simp [orientCriticalPair, hgt, r]
    have hrule : r ∈ rules := fixpoint_oriented_mem (ord := ord) (rules := rules) hfix hcp horient'
    have hstep : Step (ruleSetOfList (sig := sig) rules) cp.left cp.right := by
      have hstep' := step_of_rule (rules := ruleSetOfList (sig := sig) rules) r hrule Term.idSubst
      simpa [r, Term.subst_id] using hstep'
    exact ⟨cp.right, Rewriting.Star.single hstep, Rewriting.Star.refl _⟩
  ·
    have hlt : ord.lt cp.left cp.right := by
      rcases horient with hgt' | hlt
      · exact (hgt hgt').elim
      · exact hlt
    let r : Rule sig := { lhs := cp.right, rhs := cp.left }
    have horient' : orientCriticalPair ord cp = some r := by
      simp [orientCriticalPair, hgt, hlt, r]
    have hrule : r ∈ rules := fixpoint_oriented_mem (ord := ord) (rules := rules) hfix hcp horient'
    have hstep : Step (ruleSetOfList (sig := sig) rules) cp.right cp.left := by
      have hstep' := step_of_rule (rules := ruleSetOfList (sig := sig) rules) r hrule Term.idSubst
      simpa [r, Term.subst_id] using hstep'
    exact ⟨cp.left, Rewriting.Star.refl _, Rewriting.Star.single hstep⟩

/-- If every critical pair is orientable and listed, a fixpoint gives joinability. -/
theorem criticalPairsJoinable_of_fixpoint_orientable {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hfix : isFixpoint ord rules)
    (hcomplete : ∀ cp, CriticalPairs (ruleSetOfList (sig := sig) rules) cp →
      cp ∈ criticalPairsOfRules (sig := sig) rules)
    (horient : ∀ cp, cp ∈ criticalPairsOfRules (sig := sig) rules →
      ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    CriticalPairsJoinable (ruleSetOfList (sig := sig) rules) := by
  intro cp hcp
  have hmem := hcomplete cp hcp
  exact joinable_of_fixpoint_orientable (ord := ord) (rules := rules) hfix hmem (horient cp hmem)

/-- Fixpoint certificates yield Knuth-Bendix completeness. -/
theorem knuthBendixComplete_of_fixpoint_orientable {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hfix : isFixpoint ord rules)
    (hnvl : NonVarLHS (ruleSetOfList (sig := sig) rules))
    (hord : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (hcomplete : ∀ cp, CriticalPairs (ruleSetOfList (sig := sig) rules) cp →
      cp ∈ criticalPairsOfRules (sig := sig) rules)
    (horient : ∀ cp, cp ∈ criticalPairsOfRules (sig := sig) rules →
      ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    KnuthBendixComplete (ruleSetOfList (sig := sig) rules) ord := by
  refine ⟨hnvl, ?_, ?_⟩
  · intro r hr
    exact hord r hr
  · exact criticalPairsJoinable_of_fixpoint_orientable (ord := ord) (rules := rules) hfix hcomplete horient

/-- Successful completion yields confluence once the resulting rule list is certified. -/
theorem completionWithFuel_confluent_of_orientable {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {fuel : Nat} {rules result : RuleList sig}
    (hinit : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (h : completionWithFuel ord fuel rules = CompletionResult.complete result)
    (hnvl : NonVarLHS (ruleSetOfList (sig := sig) result))
    (hcomplete : ∀ cp, CriticalPairs (ruleSetOfList (sig := sig) result) cp →
      cp ∈ criticalPairsOfRules (sig := sig) result)
    (horient : ∀ cp, cp ∈ criticalPairsOfRules (sig := sig) result →
      ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    Confluent (ruleSetOfList (sig := sig) result) := by
  have hfix : isFixpoint ord result :=
    completionWithFuel_complete_isFixpoint (ord := ord) (rules := rules) (result := result) h
  have hord : ∀ r, r ∈ result → ord.lt r.rhs r.lhs :=
    completionWithFuel_oriented (ord := ord) (rules := rules) (result := result) hinit h
  have hkb :=
    knuthBendixComplete_of_fixpoint_orientable
      (ord := ord) (rules := result) hfix hnvl hord hcomplete horient
  exact confluent_of_knuthBendixComplete hkb

end Metatheory.TRS.FirstOrder
