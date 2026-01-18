/-
# First-Order TRS Examples

A tiny ground TRS example with a Knuth-Bendix completion certificate.
-/

import Metatheory.TRS.FirstOrder.Confluence

namespace Metatheory.TRS.FirstOrder

/-! ## Signature and Terms -/

/-- Symbols for a tiny ground signature. -/
inductive ExampleSym : Type
  | a
  | b
  | f

/-- Arity of the example symbols. -/
def exampleArity : ExampleSym -> Nat
  | .a => 0
  | .b => 0
  | .f => 1

/-- Example signature with constants `a`, `b` and unary `f`. -/
def exampleSig : Signature :=
  { Sym := ExampleSym, arity := exampleArity }

/-- Constant term `a`. -/
def aTerm : Term exampleSig :=
  Term.app ExampleSym.a (fun i => i.elim0)

/-- Constant term `b`. -/
def bTerm : Term exampleSig :=
  Term.app ExampleSym.b (fun i => i.elim0)

/-- Unary constructor `f`. -/
def fTerm (t : Term exampleSig) : Term exampleSig :=
  Term.app ExampleSym.f (fun _ => t)

/-! ## Rules -/

/-- Rule `f(a) → b`. -/
def rule1 : Rule exampleSig :=
  { lhs := fTerm aTerm, rhs := bTerm }

/-- Rule `f(b) → a`. -/
def rule2 : Rule exampleSig :=
  { lhs := fTerm bTerm, rhs := aTerm }

/-- Rule set containing the two example rules. -/
def rules : RuleSet exampleSig :=
  fun r => r = rule1 ∨ r = rule2

/-! ## Ordering Lemmas -/

/-- `b` is strictly smaller than `f(a)` in the stable size ordering. -/
theorem rule1_oriented :
    stableSizeLt (sig := exampleSig) rule1.rhs rule1.lhs := by
  intro sub
  simp [rule1, fTerm, aTerm, bTerm, Term.size, Term.subst, Term.finSum, exampleArity]

/-- `a` is strictly smaller than `f(b)` in the stable size ordering. -/
theorem rule2_oriented :
    stableSizeLt (sig := exampleSig) rule2.rhs rule2.lhs := by
  intro sub
  simp [rule2, fTerm, aTerm, bTerm, Term.size, Term.subst, Term.finSum, exampleArity]

/-- Orientation proof for all rules using the stable size ordering. -/
theorem rules_oriented :
    ∀ r, rules r → stableSizeLt (sig := exampleSig) r.rhs r.lhs := by
  intro r hr
  rcases hr with rfl | rfl
  · exact rule1_oriented
  · exact rule2_oriented

/-! ## Critical Pairs -/

/-- The example rules have trivially joinable critical pairs. -/
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
        simp [rule1, rule2, mkCriticalPair] at hmk
        cases hmk
        exact Rewriting.Joinable.refl (Step rules) _
    | cons i ps =>
        simp [rule1, rule2, fTerm, aTerm, bTerm, Term.subterm, exampleArity] at hsub

/-! ## Knuth-Bendix Certificate -/

/-- Knuth-Bendix completion certificate for the example system. -/
theorem example_knuthBendixComplete :
    KnuthBendixComplete (rules := rules) (stableSizeOrdering exampleSig) := by
  refine ⟨?_, ?_⟩
  · exact rules_oriented
  · exact rules_criticalPairsJoinable

/-- The example TRS is confluent. -/
theorem example_confluent : Confluent rules :=
  confluent_of_knuthBendixComplete example_knuthBendixComplete

end Metatheory.TRS.FirstOrder
