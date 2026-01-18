/-
# Critical Pairs for First-Order TRSs

Defines overlaps and critical pairs using unifiers and term positions.
-/

import Metatheory.TRS.FirstOrder.Rules
import Metatheory.TRS.FirstOrder.Positions

namespace Metatheory.TRS.FirstOrder

open Term

/-! ## Variable and Unification Predicates -/

/-- Predicate: term is a variable. -/
def IsVar {sig : Signature} : Term sig -> Prop
  | Term.var _ => True
  | Term.app _ _ => False

/-- Predicate: term is not a variable. -/
abbrev NonVar {sig : Signature} (t : Term sig) : Prop := ¬ IsVar t

@[simp] theorem isVar_var {sig : Signature} (x : Nat) : IsVar (Term.var (sig := sig) x) := by
  simp [IsVar]

@[simp] theorem nonVar_app {sig : Signature} (f : sig.Sym) (args : Fin (sig.arity f) -> Term sig) :
    NonVar (Term.app f args) := by
  simp [NonVar, IsVar]

/-- A substitution unifies two terms if it makes them equal. -/
def Unifies {sig : Signature} (sub : Subst sig) (s t : Term sig) : Prop :=
  Term.subst sub s = Term.subst sub t

theorem unifies_refl {sig : Signature} (sub : Subst sig) (t : Term sig) :
    Unifies sub t t := by
  rfl

theorem unifies_symm {sig : Signature} {sub : Subst sig} {s t : Term sig} :
    Unifies sub s t -> Unifies sub t s := by
  intro h
  simpa [Unifies] using h.symm

theorem unifies_trans {sig : Signature} {sub : Subst sig} {s t u : Term sig} :
    Unifies sub s t -> Unifies sub t u -> Unifies sub s u := by
  intro hst htu
  dsimp [Unifies] at hst htu ⊢
  exact hst.trans htu

theorem unifies_comp {sig : Signature} {sub tau : Subst sig} {s t : Term sig}
    (h : Unifies sub s t) : Unifies (Term.compSubst tau sub) s t := by
  dsimp [Unifies] at h ⊢
  have h' := congrArg (Term.subst tau) h
  simpa [Term.subst_comp] using h'

/-! ## Critical Pairs -/

/-- Overlap witness: an LHS instance contains another LHS instance at a position. -/
def Overlap {sig : Signature} (r1 r2 : Rule sig) (p : Pos)
    (sub1 sub2 : Subst sig) : Prop :=
  Term.subterm (Term.subst sub1 r1.lhs) p = some (Term.subst sub2 r2.lhs)

/-- A critical pair is a pair of terms derived from overlapping rules. -/
structure CriticalPair (sig : Signature) where
  left : Term sig
  right : Term sig

/-- Build a critical pair from an overlap, if the replacement is defined. -/
def mkCriticalPair {sig : Signature} (r1 r2 : Rule sig) (p : Pos)
    (sub1 sub2 : Subst sig) : Option (CriticalPair sig) :=
  match Term.replace (Term.subst sub1 r1.lhs) p (Term.subst sub2 r2.rhs) with
  | none => none
  | some t => some ⟨Term.subst sub1 r1.rhs, t⟩

@[simp] theorem mkCriticalPair_root {sig : Signature} (r1 r2 : Rule sig)
    (sub1 sub2 : Subst sig) :
    mkCriticalPair r1 r2 [] sub1 sub2 =
      some ⟨Term.subst sub1 r1.rhs, Term.subst sub2 r2.rhs⟩ := by
  simp [mkCriticalPair]

/-- A critical pair of a rule set. -/
def IsCriticalPair {sig : Signature} (rules : RuleSet sig) (cp : CriticalPair sig) : Prop :=
  ∃ r1 r2 p sub1 sub2,
    rules r1 ∧ rules r2 ∧ Overlap r1 r2 p sub1 sub2 ∧
      mkCriticalPair r1 r2 p sub1 sub2 = some cp

/-- The set of critical pairs of a rule set. -/
abbrev CriticalPairs {sig : Signature} (rules : RuleSet sig) : CriticalPair sig -> Prop :=
  IsCriticalPair rules

end Metatheory.TRS.FirstOrder
