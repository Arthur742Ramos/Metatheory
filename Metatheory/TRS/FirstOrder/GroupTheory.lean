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

end Metatheory.TRS.FirstOrder
