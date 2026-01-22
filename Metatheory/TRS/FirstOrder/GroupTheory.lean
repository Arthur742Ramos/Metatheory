/-
# Group Theory Case Study

A larger TRS example: group theory axioms.
This demonstrates the framework on a non-trivial algebraic example.

Rules:
- e * x -> x (left identity)
- x * e -> x (right identity)
- inv(inv(x)) -> x (double inverse)
- inv(e) -> e (inverse of identity)
-/

import Metatheory.TRS.FirstOrder.Confluence
import Mathlib.Data.Fin.Tuple.Basic

namespace Metatheory.TRS.FirstOrder

open Term

/-! ## Signature -/

/-- Symbols for group signature. -/
inductive GroupSym : Type
  | e    -- identity element
  | mul  -- binary multiplication
  | inv  -- unary inverse

/-- Arity of group symbols. -/
def groupArity : GroupSym -> Nat
  | .e => 0
  | .mul => 2
  | .inv => 1

/-- Group signature. -/
def groupSig : Signature :=
  { Sym := GroupSym, arity := groupArity }

/-! ## Term Constructors -/

/-- Identity element e. -/
def eTerm : Term groupSig :=
  Term.app GroupSym.e (Fin.elim0)

/-- Binary multiplication. -/
def mulTerm (s t : Term groupSig) : Term groupSig :=
  Term.app GroupSym.mul (Fin.cons s (fun _ => t))

/-- Unary inverse. -/
def invTerm (t : Term groupSig) : Term groupSig :=
  Term.app GroupSym.inv (fun _ => t)

/-- Variable x. -/
def xVar : Term groupSig := Term.var 0

/-! ## Simplification Lemmas -/

@[simp] lemma subst_eTerm (sub : Subst groupSig) :
    Term.subst sub eTerm = eTerm := by
  simp only [eTerm, Term.subst]
  congr
  funext i
  exact Fin.elim0 i

@[simp] lemma subst_mulTerm (sub : Subst groupSig) (s t : Term groupSig) :
    Term.subst sub (mulTerm s t) = mulTerm (Term.subst sub s) (Term.subst sub t) := by
  simp only [mulTerm, Term.subst]
  congr
  funext i
  cases i using Fin.cases <;> rfl

@[simp] lemma subst_invTerm (sub : Subst groupSig) (t : Term groupSig) :
    Term.subst sub (invTerm t) = invTerm (Term.subst sub t) := rfl

@[simp] lemma size_eTerm : Term.size eTerm = 1 := rfl

lemma finSum_two (f : Fin 2 → Nat) : Term.finSum f = f 0 + f 1 := by
  simp only [Term.finSum, Fin.succ_zero_eq_one, Nat.add_zero]

lemma size_mulTerm (s t : Term groupSig) :
    Term.size (mulTerm s t) = 1 + Term.size s + Term.size t := by
  simp only [mulTerm, Term.size, groupSig, groupArity, finSum_two, Fin.cons_zero, Fin.cons_succ]
  ac_rfl

@[simp] lemma size_invTerm (t : Term groupSig) :
    Term.size (invTerm t) = 1 + Term.size t := rfl

@[simp] lemma subterm_mul_left (s t : Term groupSig) :
    Term.subterm (mulTerm s t) [0] = some s := by
  simp [mulTerm, Term.subterm, groupArity]

@[simp] lemma subterm_mul_right (s t : Term groupSig) :
    Term.subterm (mulTerm s t) [1] = some t := by
  simp [mulTerm, Term.subterm, groupArity]

@[simp] lemma replace_mul_left (s t u : Term groupSig) :
    Term.replace (mulTerm s t) [0] u = some (mulTerm u t) := by
  simp [mulTerm, Term.replace, groupArity]
  ext j
  cases j using Fin.cases <;> simp

@[simp] lemma replace_mul_right (s t u : Term groupSig) :
    Term.replace (mulTerm s t) [1] u = some (mulTerm s u) := by
  simp [mulTerm, Term.replace, groupArity]
  ext j
  cases j using Fin.cases with
  | zero => simp
  | succ j =>
      cases j using Fin.cases <;> simp

@[simp] lemma subterm_inv (t : Term groupSig) :
    Term.subterm (invTerm t) [0] = some t := by
  simp [invTerm, Term.subterm, groupArity]

@[simp] lemma replace_inv (t u : Term groupSig) :
    Term.replace (invTerm t) [0] u = some (invTerm u) := by
  simp [invTerm, Term.replace, groupArity]
  ext j
  cases j using Fin.cases <;> simp

@[simp] lemma subst_xVar (sub : Subst groupSig) : Term.subst sub xVar = sub 0 := by
  rfl

/-! ## Rewrite Rules -/

/-- Rule: e * x -> x -/
def rule_left_id : Rule groupSig :=
  { lhs := mulTerm eTerm xVar, rhs := xVar }

/-- Rule: x * e -> x -/
def rule_right_id : Rule groupSig :=
  { lhs := mulTerm xVar eTerm, rhs := xVar }

/-- Rule: inv(inv(x)) -> x -/
def rule_double_inv : Rule groupSig :=
  { lhs := invTerm (invTerm xVar), rhs := xVar }

/-- Rule: inv(e) -> e -/
def rule_inv_e : Rule groupSig :=
  { lhs := invTerm eTerm, rhs := eTerm }

/-- Group theory rule set (simplified). -/
def groupRules : RuleSet groupSig :=
  fun r => r = rule_left_id ∨ r = rule_right_id ∨
          r = rule_double_inv ∨ r = rule_inv_e

@[simp] lemma groupRules_left : groupRules rule_left_id := by
  simp [groupRules]

@[simp] lemma groupRules_right : groupRules rule_right_id := by
  simp [groupRules]

@[simp] lemma groupRules_double_inv : groupRules rule_double_inv := by
  simp [groupRules]

@[simp] lemma groupRules_inv_e : groupRules rule_inv_e := by
  simp [groupRules]

/-! ## Ordering Proofs -/

/-- All group rules decrease term size. -/
theorem groupRules_size_decreasing :
    ∀ r, groupRules r → stableSizeLt (sig := groupSig) r.rhs r.lhs := by
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl
  · -- e * x -> x
    intro sub
    simp only [rule_left_id, subst_mulTerm, subst_eTerm, size_mulTerm, size_eTerm]
    omega
  · -- x * e -> x
    intro sub
    simp only [rule_right_id, subst_mulTerm, subst_eTerm, size_mulTerm, size_eTerm]
    omega
  · -- inv(inv(x)) -> x
    intro sub
    simp only [rule_double_inv, subst_invTerm, size_invTerm]
    omega
  · -- inv(e) -> e
    intro sub
    simp only [rule_inv_e, subst_invTerm, subst_eTerm, size_invTerm, size_eTerm]
    omega

/-- Group rewriting terminates. -/
theorem groupRules_terminating : Terminating groupRules :=
  terminating_of_ordering (ord := stableSizeOrdering groupSig) groupRules_size_decreasing

/-! ## One-step Reductions -/

lemma step_left_id (t : Term groupSig) :
    Step groupRules (mulTerm eTerm t) t := by
  have hstep := step_of_rule (rules := groupRules) rule_left_id groupRules_left (fun _ => t)
  simpa [rule_left_id] using hstep

lemma step_right_id (t : Term groupSig) :
    Step groupRules (mulTerm t eTerm) t := by
  have hstep := step_of_rule (rules := groupRules) rule_right_id groupRules_right (fun _ => t)
  simpa [rule_right_id] using hstep

lemma step_double_inv (t : Term groupSig) :
    Step groupRules (invTerm (invTerm t)) t := by
  have hstep := step_of_rule (rules := groupRules) rule_double_inv groupRules_double_inv (fun _ => t)
  simpa [rule_double_inv] using hstep

lemma step_inv_e : Step groupRules (invTerm eTerm) eTerm := by
  have hstep := step_of_rule (rules := groupRules) rule_inv_e groupRules_inv_e Term.idSubst
  simpa [rule_inv_e] using hstep

/-! ## Critical Pairs -/

lemma joinable_of_eq {s t : Term groupSig} (h : s = t) :
    Rewriting.Joinable (Step groupRules) s t := by
  subst h
  exact Rewriting.Joinable.refl (Step groupRules) _

lemma joinable_inv_e :
    Rewriting.Joinable (Step groupRules) (invTerm eTerm) eTerm := by
  refine ⟨eTerm, Rewriting.Star.single step_inv_e, Rewriting.Star.refl _⟩

lemma joinable_inv_e_mul_e_e :
    Rewriting.Joinable (Step groupRules) (invTerm eTerm) (mulTerm eTerm eTerm) := by
  refine ⟨eTerm, Rewriting.Star.single step_inv_e, Rewriting.Star.single (step_left_id eTerm)⟩

theorem groupRules_criticalPairsJoinable : CriticalPairsJoinable groupRules := by
  intro cp hcp
  rcases hcp with ⟨r1, r2, p, sub1, sub2, hr1, hr2, hover, hmk⟩
  rcases hr1 with rfl | rfl | rfl | rfl <;> rcases hr2 with rfl | rfl | rfl | rfl
  all_goals
    cases p with
    | nil =>
        -- root overlaps
        simp [mkCriticalPair] at hmk
        cases hmk
        ·
          -- both sides reduce to the same instantiation
          have hoverEq : Term.subst sub1 r1.lhs = Term.subst sub2 r2.lhs := by
            simpa [Overlap] using hover
          -- extract variable equality when needed
          have hsub := congrArg (fun t => Term.subterm t [1]) hoverEq
          simp [rule_left_id, rule_right_id, rule_double_inv, rule_inv_e, mulTerm, invTerm,
            Term.subterm, groupArity, subst_xVar] at hsub
        ·
          -- fallback (no additional information)
          simp [rule_left_id, rule_right_id, rule_double_inv, rule_inv_e] at hmk
    | cons i ps =>
        cases ps with
        | nil =>
            cases i with
            | zero =>
                -- position [0]
                -- handle possible overlaps with inv(e) or inv(inv(x))
                -- use hmk to recover the critical pair and show joinability
                all_goals
                  simp [rule_left_id, rule_right_id, rule_double_inv, rule_inv_e, mkCriticalPair, Overlap,
                    mulTerm, invTerm, groupArity, Term.subterm, Term.replace, subst_xVar] at hover hmk
            | succ i =>
                -- position [1]
                cases i with
                | zero =>
                    -- [1]
                    all_goals
                      simp [rule_left_id, rule_right_id, rule_double_inv, rule_inv_e, mkCriticalPair, Overlap,
                        mulTerm, invTerm, groupArity, Term.subterm, Term.replace, subst_xVar] at hover hmk
                | succ i =>
                    simp [rule_left_id, rule_right_id, rule_double_inv, rule_inv_e, Overlap, mulTerm, invTerm,
                      Term.subterm, groupArity] at hover
        | cons j qs =>
            -- deeper positions are impossible
            simp [rule_left_id, rule_right_id, rule_double_inv, rule_inv_e, Overlap, mulTerm, invTerm,
              Term.subterm, groupArity] at hover

theorem group_knuthBendixComplete :
    KnuthBendixComplete (rules := groupRules) (stableSizeOrdering groupSig) := by
  refine ⟨?_, ?_⟩
  · exact groupRules_size_decreasing
  · exact groupRules_criticalPairsJoinable

theorem group_confluent : Confluent groupRules :=
  confluent_of_knuthBendixComplete group_knuthBendixComplete

end Metatheory.TRS.FirstOrder
