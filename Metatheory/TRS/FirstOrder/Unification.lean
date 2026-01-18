/-
# Unification Basics for First-Order Terms

Defines unifiers, most general unifiers, and basic occurs/check utilities.
-/

import Metatheory.TRS.FirstOrder.Syntax

namespace Metatheory.TRS.FirstOrder

open Term

/-- An equation between terms. -/
abbrev Equation (sig : Signature) := Term sig × Term sig

/-- A list of equations. -/
abbrev Equations (sig : Signature) := List (Equation sig)

/-- A substitution unifies a list of equations. -/
def UnifiesList {sig : Signature} (sub : Subst sig) (eqs : Equations sig) : Prop :=
  ∀ e ∈ eqs, Term.subst sub e.1 = Term.subst sub e.2

/-- A list of equations is unifiable if it has a unifier. -/
def Unifiable {sig : Signature} (eqs : Equations sig) : Prop :=
  ∃ sub, UnifiesList sub eqs

/-- Most general unifier: any unifier factors through it by composition. -/
def IsMGU {sig : Signature} (sub : Subst sig) (eqs : Equations sig) : Prop :=
  UnifiesList sub eqs ∧
  ∀ tau, UnifiesList tau eqs -> ∃ theta, tau = Term.compSubst theta sub

/-- Occurs check: variable occurs in term. -/
def Occurs {sig : Signature} (x : Nat) : Term sig -> Prop
  | Term.var y => x = y
  | Term.app _ args => ∃ i, Occurs x (args i)

theorem occurs_var {sig : Signature} (x y : Nat) :
    Occurs (sig := sig) x (Term.var y) ↔ x = y := by
  rfl

theorem occurs_app {sig : Signature} (x : Nat) (f : sig.Sym)
    (args : Fin (sig.arity f) -> Term sig) :
    Occurs (sig := sig) x (Term.app f args) ↔ ∃ i, Occurs x (args i) := by
  rfl

/-- Update a substitution at a single variable. -/
def updateSubst {sig : Signature} (sub : Subst sig) (x : Nat) (t : Term sig) : Subst sig :=
  fun y => if y = x then t else sub y

@[simp] theorem updateSubst_same {sig : Signature} (sub : Subst sig) (x : Nat) (t : Term sig) :
    updateSubst sub x t x = t := by
  simp [updateSubst]

@[simp] theorem updateSubst_ne {sig : Signature} (sub : Subst sig) {x y : Nat} (t : Term sig)
    (h : y ≠ x) : updateSubst sub x t y = sub y := by
  simp [updateSubst, h]

end Metatheory.TRS.FirstOrder
