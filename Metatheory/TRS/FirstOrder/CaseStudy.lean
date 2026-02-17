/-
# First-Order TRS Case Study: Unit Laws

This module provides a small Knuth-Bendix certificate for the TRS
with unit laws `e * x -> x` and `x * e -> x`.
-/

import Metatheory.TRS.FirstOrder.Completion

namespace Metatheory.TRS.FirstOrder

open Term

/-! ## Signature and Terms -/

/-- Symbols for a unit-law signature. -/
inductive UnitSym : Type
  | e
  | mul

/-- Arity of unit-law symbols. -/
def unitArity : UnitSym -> Nat
  | .e => 0
  | .mul => 2

/-- Unit-law signature with constant `e` and binary `mul`. -/
def unitSig : Signature :=
  { Sym := UnitSym, arity := unitArity }

/-- Constant term `e`. -/
def eTerm : Term unitSig :=
  Term.app UnitSym.e (fun i => i.elim0)

/-- Binary constructor `mul`. -/
def mulTerm (s t : Term unitSig) : Term unitSig :=
  Term.app UnitSym.mul (fun i => Fin.cases s (fun _ => t) i)

/-- Variable `x`. -/
def xTerm : Term unitSig :=
  Term.var 0

/-! ## Basic Simplifications -/

@[simp] lemma subterm_mul_left (s t : Term unitSig) :
    Term.subterm (mulTerm s t) [0] = some s := by
  simp [mulTerm, Term.subterm, unitArity]

@[simp] lemma subterm_mul_right (s t : Term unitSig) :
    Term.subterm (mulTerm s t) [1] = some t := by
  simp [mulTerm, Term.subterm, unitArity]

@[simp] lemma replace_mul_left (s t u : Term unitSig) :
    Term.replace (mulTerm s t) [0] u = some (mulTerm u t) := by
  simp [mulTerm, Term.replace, unitArity]

@[simp] lemma replace_mul_right (s t u : Term unitSig) :
    Term.replace (mulTerm s t) [1] u = some (mulTerm s u) := by
  simp [mulTerm, Term.replace, unitArity]

@[simp] lemma subst_eTerm (sub : Subst unitSig) : Term.subst sub eTerm = eTerm := by
  simp [eTerm, Term.subst]

@[simp] lemma size_eTerm : Term.size eTerm = 1 := by
  simp [eTerm, Term.size, Term.finSum, unitArity]

@[simp] lemma size_mulTerm (s t : Term unitSig) :
    Term.size (mulTerm s t) = 1 + Term.size s + Term.size t := by
  simp [mulTerm, Term.size, Term.finSum, unitArity, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-! ## Rules -/

/-- Rule `mul(e, x) → x`. -/
def rule_left : Rule unitSig :=
  { lhs := mulTerm eTerm (Term.var 0), rhs := Term.var 0 }

/-- Rule `mul(x, e) → x`. -/
def rule_right : Rule unitSig :=
  { lhs := mulTerm (Term.var 0) eTerm, rhs := Term.var 0 }

/-- Rule set containing the unit laws. -/
def rules : RuleSet unitSig :=
  fun r => r = rule_left ∨ r = rule_right

@[simp] lemma rules_left : rules rule_left := by
  simp [rules]

@[simp] lemma rules_right : rules rule_right := by
  simp [rules]

/-! ## Ordering Proofs -/

lemma lt_add_two (n : Nat) : n < n + 2 :=
  Nat.lt_add_of_pos_right n (by decide)

/-- Orientation for `mul(e, x) → x`. -/
theorem rule_left_oriented :
    stableSizeLt (sig := unitSig) rule_left.rhs rule_left.lhs := by
  intro sub
  have h : Term.size (sub 0) < Term.size (sub 0) + 2 := lt_add_two _
  simpa [rule_left, Term.subst, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Orientation for `mul(x, e) → x`. -/
theorem rule_right_oriented :
    stableSizeLt (sig := unitSig) rule_right.rhs rule_right.lhs := by
  intro sub
  have h : Term.size (sub 0) < Term.size (sub 0) + 2 := lt_add_two _
  simpa [rule_right, Term.subst, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Orientation for all unit rules. -/
theorem rules_oriented :
    ∀ r, rules r → stableSizeLt (sig := unitSig) r.rhs r.lhs := by
  intro r hr
  rcases hr with rfl | rfl
  · exact rule_left_oriented
  · exact rule_right_oriented

/-! ## Critical Pairs -/

lemma joinable_of_eq {s t : Term unitSig} (h : s = t) :
    Rewriting.Joinable (Step rules) s t := by
  subst h
  exact Rewriting.Joinable.refl (Step rules) _

lemma joinable_unit_overlap (sub : Subst unitSig) :
    Rewriting.Joinable (Step rules)
      (mulTerm (sub 0) eTerm) (mulTerm eTerm (sub 0)) := by
  refine ⟨sub 0, ?_, ?_⟩
  ·
    have hstep := step_of_rule rule_right rules_right sub
    have hstep' : Step rules (mulTerm (sub 0) eTerm) (sub 0) := by
      simpa [rule_right, Term.subst] using hstep
    exact Rewriting.Star.single hstep'
  ·
    have hstep := step_of_rule rule_left rules_left sub
    have hstep' : Step rules (mulTerm eTerm (sub 0)) (sub 0) := by
      simpa [rule_left, Term.subst] using hstep
    exact Rewriting.Star.single hstep'

/-- Unit rules have joinable critical pairs. -/
theorem rules_criticalPairsJoinable : CriticalPairsJoinable rules := by
  intro cp hcp
  rcases hcp with ⟨r1, r2, p, sub1, sub2, hr1, hr2, hover, hmk⟩
  rcases hr1 with rfl | rfl <;> rcases hr2 with rfl | rfl
  all_goals
    have hsub : Term.subterm (Term.subst sub1 r1.lhs) p = some (Term.subst sub2 r2.lhs) := hover
    have hoverEq : Term.subst sub1 r1.lhs = Term.subst sub2 r2.lhs := by
      simpa using hsub
    cases p with
    | nil =>
        -- root overlaps yield equal contracta
        simp at hmk
        cases hmk
        have hEq : Term.subst sub1 rule_left.lhs = Term.subst sub2 rule_left.lhs ∨
            Term.subst sub1 rule_left.lhs = Term.subst sub2 rule_right.lhs ∨
            Term.subst sub1 rule_right.lhs = Term.subst sub2 rule_left.lhs ∨
            Term.subst sub1 rule_right.lhs = Term.subst sub2 rule_right.lhs := by
          exact Or.inl (by
            simpa [rule_left, rule_right, Term.subterm] using hoverEq)
        cases hEq with
        | inl h =>
            have hsub' := congrArg (fun t => Term.subterm t [1]) h
            have hvars : sub1 0 = sub2 0 := by
              simpa [rule_left, Term.subst] using hsub'
            exact joinable_of_eq hvars
        | inr h =>
            cases h with
            | inl h =>
                have hleft := congrArg (fun t => Term.subterm t [1]) h
                have hright := congrArg (fun t => Term.subterm t [0]) h
                have hsub1 : sub1 0 = eTerm := by
                  simpa [rule_left, rule_right, Term.subst] using hleft
                have hsub2 : sub2 0 = eTerm := by
                  simpa [rule_left, rule_right, Term.subst] using hright
                exact joinable_of_eq (by simpa [hsub1, hsub2])
            | inr h =>
                cases h with
                | inl h =>
                    have hleft := congrArg (fun t => Term.subterm t [0]) h
                    have hright := congrArg (fun t => Term.subterm t [1]) h
                    have hsub1 : sub1 0 = eTerm := by
                      simpa [rule_left, rule_right, Term.subst] using hleft
                    have hsub2 : sub2 0 = eTerm := by
                      simpa [rule_left, rule_right, Term.subst] using hright
                    exact joinable_of_eq (by simpa [hsub1, hsub2])
                | inr h =>
                    have hsub' := congrArg (fun t => Term.subterm t [0]) h
                    have hvars : sub1 0 = sub2 0 := by
                      simpa [rule_right, Term.subst] using hsub'
                    exact joinable_of_eq hvars
    | cons i ps =>
        cases ps with
        | nil =>
            cases i with
            | zero =>
                -- p = [0]
                simp [rule_left, rule_right, Term.subterm, Term.subst] at hsub
                cases hsub
                cases hoverEq
            | succ i =>
                cases i with
                | zero =>
                    -- p = [1]
                    have ht : t = Term.var 0 := by
                      simpa [rule_left, rule_right, Term.subterm] using hsub
                    subst ht
                    have hsub1 : sub1 0 = mulTerm (sub2 0) eTerm := by
                      simpa [rule_left, rule_right, Term.subst] using hoverEq
                    simp [rule_left, rule_right, Term.subst] at hmk
                    cases hmk
                    simpa [hsub1] using (joinable_unit_overlap (sub := sub2))
                | succ i =>
                    simp [rule_left, rule_right, Term.subterm] at hsub
        | cons j qs =>
            simp [rule_left, rule_right, Term.subterm] at hsub

/-! ## Knuth-Bendix Certificate -/

/-- Knuth-Bendix completion certificate for the unit-law TRS. -/
theorem unit_knuthBendixComplete :
    KnuthBendixComplete (rules := rules) (stableSizeOrdering unitSig) := by
  refine ⟨?_, ?_⟩
  · exact rules_oriented
  · exact rules_criticalPairsJoinable

/-- The unit-law TRS is confluent. -/
theorem caseStudy_confluent : Confluent rules :=
  confluent_of_knuthBendixComplete unit_knuthBendixComplete

/-! ## Finite Completion View -/

noncomputable def unitRuleList : RuleList unitSig :=
  [rule_left, rule_right]

theorem unitRuleList_rules : ∀ r, r ∈ unitRuleList → rules r := by
  intro r hr
  simp [unitRuleList, rules] at hr
  rcases hr with rfl | rfl
  · exact rules_left
  · exact rules_right

theorem unitRuleList_oriented :
    ∀ r, r ∈ unitRuleList → stableSizeLt (sig := unitSig) r.rhs r.lhs := by
  intro r hr
  exact rules_oriented r (unitRuleList_rules r hr)

theorem unit_completionStep_oriented :
    ∀ r, r ∈ completionStepList (stableSizeOrdering unitSig) unitRuleList →
      stableSizeLt (sig := unitSig) r.rhs r.lhs := by
  intro r hr
  rcases completionStepList_oriented (ord := stableSizeOrdering unitSig)
    (rules := unitRuleList) (r := r) hr with hr' | hr'
  · exact unitRuleList_oriented r hr'
  ·
    rcases hr' with ⟨cp, hcp, horiented⟩
    exact oriented_lt (ord := stableSizeOrdering unitSig) horiented

end Metatheory.TRS.FirstOrder
