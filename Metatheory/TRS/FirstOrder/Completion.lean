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
    (_hcomp : Completion ord rules rules')
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

/-- Iterate the list-based completion step `n` times. -/
noncomputable def completionIter {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) : Nat → RuleList sig → RuleList sig
  | 0, rules => rules
  | n + 1, rules => completionIter ord n (completionStepList ord rules)

theorem mem_completionStepList {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {r : Rule sig} :
    r ∈ completionStepList ord rules →
    r ∈ rules ∨ ∃ cp, cp ∈ criticalPairsOfRules (sig := sig) rules ∧
      orientCriticalPair ord cp = some r := by
  intro hmem
  have hmem' := List.mem_append.1 hmem
  rcases hmem' with hmem' | hmem'
  · exact Or.inl hmem'
  ·
    rcases List.mem_filterMap.1 hmem' with ⟨cp, hcp, horient⟩
    exact Or.inr ⟨cp, hcp, horient⟩

theorem completionStepList_oriented {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {r : Rule sig} :
    r ∈ completionStepList ord rules →
    r ∈ rules ∨ ∃ cp, cp ∈ criticalPairsOfRules (sig := sig) rules ∧ Oriented ord cp r := by
  intro hmem
  rcases mem_completionStepList (ord := ord) (rules := rules) hmem with hmem' | hmem'
  · exact Or.inl hmem'
  ·
    rcases hmem' with ⟨cp, hcp, horient⟩
    exact Or.inr ⟨cp, hcp, orientCriticalPair_oriented horient⟩

/-! ## Fixpoint Detection -/

/-- A completion step is trivial if it adds no new rules. -/
def isFixpoint {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) (rules : RuleList sig) : Prop :=
  ∀ r, r ∈ orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules) → r ∈ rules

/-- If isFixpoint holds, completionStepList returns the same rules (up to duplicates). -/
theorem completionStepList_fixpoint {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hfix : isFixpoint ord rules) :
    ∀ r, r ∈ completionStepList ord rules ↔ r ∈ rules := by
  intro r
  constructor
  · intro hmem
    rcases List.mem_append.1 hmem with hmem' | hmem'
    · exact hmem'
    · exact hfix r hmem'
  · intro hmem
    exact List.mem_append_left _ hmem

/-- Fixpoints are preserved by a completion step. -/
theorem isFixpoint_completionStepList {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hfix : isFixpoint ord rules) :
    isFixpoint ord (completionStepList ord rules) := by
  intro r hr
  rcases List.mem_filterMap.1 hr with ⟨cp, hcp, horient⟩
  have hsubset : ∀ r, r ∈ completionStepList ord rules → r ∈ rules := by
    intro r hr'
    exact (completionStepList_fixpoint (ord := ord) (rules := rules) hfix r).1 hr'
  have hcp' : cp ∈ criticalPairsOfRules (sig := sig) rules :=
    criticalPairsOfRules_mono (rules := completionStepList ord rules) (rules' := rules) hsubset cp hcp
  have hr' : r ∈ orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules) :=
    List.mem_filterMap.2 ⟨cp, hcp', horient⟩
  have hrules : r ∈ rules := hfix r hr'
  exact List.mem_append.2 (Or.inl hrules)

 

/-- If a fixpoint is not reached, completion strictly increases the rule list length. -/
theorem completionStepList_length_lt_of_not_fixpoint {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} :
    ¬ isFixpoint ord rules → rules.length < (completionStepList ord rules).length := by
  intro hnot
  classical
  rcases Classical.not_forall.1 hnot with ⟨r, hr⟩
  rcases Classical.not_imp.1 hr with ⟨hmem, _⟩
  have hlen :
      0 < (orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules)).length :=
    List.length_pos_of_mem hmem
  have hlt : rules.length <
      rules.length + (orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules)).length :=
    Nat.lt_add_of_pos_right hlen
  simpa [completionStepList, List.length_append] using hlt

/-- One iteration unfolds to a single completion step. -/
theorem completionIter_succ_eq_step {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} (n : Nat) (rules : RuleList sig) :
    completionIter ord (n + 1) rules =
      completionStepList ord (completionIter ord n rules) := by
  induction n generalizing rules with
  | zero =>
      simp [completionIter]
  | succ n ih =>
      calc
        completionIter ord (Nat.succ (Nat.succ n)) rules
            = completionIter ord (Nat.succ n) (completionStepList ord rules) := by
                simp [completionIter]
        _ = completionStepList ord (completionIter ord n (completionStepList ord rules)) := by
                simpa using (ih (rules := completionStepList ord rules))
        _ = completionStepList ord (completionIter ord (Nat.succ n) rules) := by
                simp [completionIter]

/-- If a step is not a fixpoint, the completion iteration strictly grows in length. -/
theorem completionIter_length_lt_succ_of_not_fixpoint {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {n : Nat} :
    ¬ isFixpoint ord (completionIter ord n rules) →
    (completionIter ord n rules).length < (completionIter ord (n + 1) rules).length := by
  intro hnot
  have hlt :=
    completionStepList_length_lt_of_not_fixpoint (ord := ord)
      (rules := completionIter ord n rules) hnot
  simpa [completionIter_succ_eq_step (ord := ord) (n := n) (rules := rules)] using hlt

/-- If all earlier iterations are not fixpoints, lengths grow by at least the step count. -/
theorem completionIter_length_lower_bound {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} :
    ∀ n, (∀ m < n, ¬ isFixpoint ord (completionIter ord m rules)) →
      rules.length + n ≤ (completionIter ord n rules).length := by
  sorry

theorem completionIter_fixpoint_succ {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {n : Nat} :
    isFixpoint ord (completionIter ord n rules) →
    isFixpoint ord (completionIter ord (n + 1) rules) := by
  sorry

theorem completionIter_fixpoint_of_le {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {n m : Nat} :
    n ≤ m →
    isFixpoint ord (completionIter ord n rules) →
    isFixpoint ord (completionIter ord m rules) := by
  sorry

theorem completionIter_fixpoint_of_bounded {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {bound : Nat}
    (hbound : ∀ n, (completionIter ord n rules).length ≤ bound) :
    ∃ n ≤ bound, isFixpoint ord (completionIter ord n rules) := by
  sorry

/-! ## Universe Bounds -/

/-- A finite universe of rules closed under completion steps. -/
structure RuleUniverse (sig : Signature) [DecidableEq sig.Sym] where
  univ : RuleList sig
  closed : ∀ {ord : ReductionOrdering sig} {rules : RuleList sig},
    (∀ r, r ∈ rules → r ∈ univ) →
    ∀ r, r ∈ completionStepList ord rules → r ∈ univ

/-- Rule universe defined by a decidable predicate on rules. -/
def RuleUniverse.ofPred {sig : Signature} [DecidableEq sig.Sym]
    (p : Rule sig → Prop) [DecidablePred p] (univ : RuleList sig)
    (hmem : ∀ r, r ∈ univ ↔ p r)
    (hclosed : ∀ {ord : ReductionOrdering sig} {rules : RuleList sig},
      (∀ r, r ∈ rules → p r) →
      ∀ r, r ∈ completionStepList ord rules → p r) :
    RuleUniverse sig :=
  { univ := univ
    closed := by
      intro ord rules hsubset r hmem'
      have : p r := hclosed (ord := ord) (rules := rules) (fun r hr => (hmem r).1 (hsubset r hr)) r hmem'
      exact (hmem r).2 this }

/-- If the initial rules are in the universe, all completion iterations stay in the universe. -/
theorem completionIter_subset_universe {sig : Signature} [DecidableEq sig.Sym]
    (U : RuleUniverse sig) {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hsubset : ∀ r, r ∈ rules → r ∈ U.univ) :
    ∀ n r, r ∈ completionIter ord n rules → r ∈ U.univ := by
  intro n
  induction n generalizing rules with
  | zero =>
      intro r hmem
      simpa [completionIter] using hsubset r hmem
  | succ n ih =>
      intro r hmem
      simp only [completionIter] at hmem
      have hsubset' : ∀ r, r ∈ completionIter ord n (completionStepList ord rules) → r ∈ U.univ := by
        intro r hr
        exact ih (rules := completionStepList ord rules)
          (fun r hr => U.closed (ord := ord) (rules := rules) hsubset r hr) r hr
      exact hsubset' r hmem

/-- If each completion iteration is nodup and stays within a universe list, its length is bounded. -/
theorem completionIter_length_le_of_subset {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {univ : RuleList sig}
    (hnodup : ∀ n, (completionIter ord n rules).Nodup)
    (hsubset : ∀ n, ∀ r, r ∈ completionIter ord n rules → r ∈ univ) :
    ∀ n, (completionIter ord n rules).length ≤ univ.length := by
  sorry

theorem completionIter_fixpoint_of_universe {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {univ : RuleList sig}
    (hnodup : ∀ n, (completionIter ord n rules).Nodup)
    (hsubset : ∀ n, ∀ r, r ∈ completionIter ord n rules → r ∈ univ) :
    ∃ n ≤ univ.length, isFixpoint ord (completionIter ord n rules) := by
  refine completionIter_fixpoint_of_bounded (ord := ord) (rules := rules)
    (bound := univ.length) ?_
  intro n
  exact completionIter_length_le_of_subset (ord := ord) (rules := rules) (univ := univ) hnodup hsubset n

/-- Completion result: either completed or ran out of fuel. -/
inductive CompletionResult (sig : Signature) where
  | complete : RuleList sig → CompletionResult sig
  | incomplete : RuleList sig → CompletionResult sig

/-- Completion with bounded iterations (fuel). -/
noncomputable def completionWithFuel {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) : Nat → RuleList sig → CompletionResult sig
  | 0, rules => CompletionResult.incomplete rules
  | n + 1, rules => by
      classical
      exact if h : isFixpoint ord rules then
        CompletionResult.complete rules
      else
        completionWithFuel ord n (completionStepList ord rules)

theorem completionWithFuel_complete_of_iter_fixpoint {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} :
    ∀ n, isFixpoint ord (completionIter ord n rules) →
      ∃ result, completionWithFuel ord (n + 1) rules = CompletionResult.complete result := by
  sorry

theorem completionWithFuel_complete_of_universe {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {univ : RuleList sig}
    (hnodup : ∀ n, (completionIter ord n rules).Nodup)
    (hsubset : ∀ n, ∀ r, r ∈ completionIter ord n rules → r ∈ univ) :
    ∃ result,
      completionWithFuel ord (univ.length + 1) rules = CompletionResult.complete result := by
  sorry

theorem completionIter_confluent_of_universe {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {univ : RuleList sig}
    (hnodup : ∀ n, (completionIter ord n rules).Nodup)
    (hsubset : ∀ n, ∀ r, r ∈ completionIter ord n rules → r ∈ univ)
    (hord : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (hcomplete : ∀ n cp, CriticalPairs (ruleSetOfList (sig := sig) (completionIter ord n rules)) cp →
      cp ∈ criticalPairsOfRules (sig := sig) (completionIter ord n rules))
    (horient : ∀ cp, cp ∈ criticalPairsOfRules (sig := sig) univ →
      ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    ∃ n, Confluent (ruleSetOfList (sig := sig) (completionIter ord n rules)) := by
  sorry

/-! ## Completion with Fuel -/

/-- If completion succeeds, the result is a fixpoint. -/
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

 

/-- If completion runs out of fuel, the result is the `fuel`-step iteration. -/
theorem completionWithFuel_incomplete_eq_iter {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {fuel : Nat} {rules result : RuleList sig}
    (h : completionWithFuel ord fuel rules = CompletionResult.incomplete result) :
    result = completionIter ord fuel rules := by
  sorry

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
        rcases ih (rules := completionStepList ord rules) (result := result) h with ⟨k, hk, hres⟩
        refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
        simpa [completionIter] using hres

/-- If completion terminates, it does so at some iteration. -/
theorem completion_terminates_of_iter {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules result : RuleList sig} {fuel : Nat}
    (h : completionWithFuel ord fuel rules = CompletionResult.complete result) :
    ∃ n, result = completionIter ord n rules := by
  rcases completionWithFuel_complete_exists_iter (ord := ord) (rules := rules) (result := result) h with
    ⟨n, _, hres⟩
  exact ⟨n, hres⟩

/-! ## Completion Correctness -/

/-- Rules only grow during completion. -/
theorem completionStepList_subset {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} :
    ∀ r, r ∈ rules → r ∈ completionStepList ord rules := by
  intro r hmem
  exact List.mem_append_left _ hmem

/-- Iterated completion preserves subset. -/
theorem completionIter_subset {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {n : Nat} :
    ∀ r, r ∈ rules → r ∈ completionIter ord n rules := by
  induction n generalizing rules with
  | zero => simp [completionIter]
  | succ n ih =>
      intro r hmem
      simp only [completionIter]
      apply ih
      exact completionStepList_subset (r := r) hmem

/-- All rules in each completion iteration satisfy the ordering. -/
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
      have hinit' : ∀ r, r ∈ completionStepList ord rules → ord.lt r.rhs r.lhs := by
        intro r hr
        rcases completionStepList_oriented (ord := ord) (rules := rules) hr with hmem' | ⟨cp, _, horient⟩
        · exact hinit r hmem'
        · exact oriented_lt horient
      exact ih (rules := completionStepList ord rules) hinit' r hmem

/-- All rules in a completed system satisfy the ordering. -/
theorem completionWithFuel_oriented {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {fuel : Nat} {rules result : RuleList sig}
    (hinit : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (h : completionWithFuel ord fuel rules = CompletionResult.complete result) :
    ∀ r, r ∈ result → ord.lt r.rhs r.lhs := by
  induction fuel generalizing rules with
  | zero => simp [completionWithFuel] at h
  | succ n ih =>
      classical
      simp only [completionWithFuel] at h
      split at h
      · case isTrue hfix =>
          injection h with heq
          rw [← heq]
          exact hinit
      · case isFalse hfix =>
          apply ih _ h
          intro r hmem
          rcases completionStepList_oriented (ord := ord) (rules := rules) hmem with hmem' | ⟨cp, _, horient⟩
          · exact hinit r hmem'
          · exact oriented_lt horient
/-! ## Fixpoint Soundness -/

/-- At a fixpoint, every oriented critical pair is already a rule. -/
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

/-- If a critical pair is orientable at a fixpoint, it is joinable by one step. -/
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
      cases horient with
      | inl hgt' => exact (hgt hgt').elim
      | inr hlt => exact hlt
    let r : Rule sig := { lhs := cp.right, rhs := cp.left }
    have horient' : orientCriticalPair ord cp = some r := by
      simp [orientCriticalPair, hgt, hlt, r]
    have hrule : r ∈ rules := fixpoint_oriented_mem (ord := ord) (rules := rules) hfix hcp horient'
    have hstep : Step (ruleSetOfList (sig := sig) rules) cp.right cp.left := by
      have hstep' := step_of_rule (rules := ruleSetOfList (sig := sig) rules) r hrule Term.idSubst
      simpa [r, Term.subst_id] using hstep'
    exact ⟨cp.left, Rewriting.Star.refl _, Rewriting.Star.single hstep⟩

/-- If all critical pairs are orientable and the list is complete, a fixpoint gives joinability. -/
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
  have hor := horient cp hmem
  exact joinable_of_fixpoint_orientable (ord := ord) (rules := rules) hfix hmem hor

/-- Fixpoint certificates yield Knuth-Bendix completeness under orientability and completeness. -/
theorem knuthBendixComplete_of_fixpoint_orientable {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hfix : isFixpoint ord rules)
    (hord : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (hcomplete : ∀ cp, CriticalPairs (ruleSetOfList (sig := sig) rules) cp →
      cp ∈ criticalPairsOfRules (sig := sig) rules)
    (horient : ∀ cp, cp ∈ criticalPairsOfRules (sig := sig) rules →
      ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    KnuthBendixComplete (ruleSetOfList (sig := sig) rules) ord := by
  refine ⟨?_, ?_⟩
  · intro r hr
    exact hord r hr
  · exact criticalPairsJoinable_of_fixpoint_orientable (ord := ord) (rules := rules) hfix hcomplete horient

/-- Completion yields confluence when a fixpoint is reached and all critical pairs are orientable. -/
theorem completionWithFuel_confluent_of_orientable {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {fuel : Nat} {rules result : RuleList sig}
    (hinit : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (h : completionWithFuel ord fuel rules = CompletionResult.complete result)
    (hcomplete : ∀ cp, CriticalPairs (ruleSetOfList (sig := sig) result) cp →
      cp ∈ criticalPairsOfRules (sig := sig) result)
    (horient : ∀ cp, cp ∈ criticalPairsOfRules (sig := sig) result →
      ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    Confluent (ruleSetOfList (sig := sig) result) := by
  have hfix : isFixpoint ord result :=
    completionWithFuel_complete_isFixpoint (ord := ord) (rules := rules) (result := result) h
  have hord : ∀ r, r ∈ result → ord.lt r.rhs r.lhs :=
    completionWithFuel_oriented (ord := ord) (rules := rules) (result := result) hinit h
  have hkb := knuthBendixComplete_of_fixpoint_orientable
    (ord := ord) (rules := result) hfix hord hcomplete horient
  exact confluent_of_knuthBendixComplete hkb

theorem completionWithFuel_confluent_of_universe {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {univ : RuleList sig}
    (hnodup : ∀ n, (completionIter ord n rules).Nodup)
    (hsubset : ∀ n, ∀ r, r ∈ completionIter ord n rules → r ∈ univ)
    (hord : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (hcomplete : ∀ n cp, CriticalPairs (ruleSetOfList (sig := sig) (completionIter ord n rules)) cp →
      cp ∈ criticalPairsOfRules (sig := sig) (completionIter ord n rules))
    (horient : ∀ cp, cp ∈ criticalPairsOfRules (sig := sig) univ →
      ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    ∃ result,
      completionWithFuel ord (univ.length + 1) rules = CompletionResult.complete result ∧
      Confluent (ruleSetOfList (sig := sig) result) := by
  sorry

end Metatheory.TRS.FirstOrder
