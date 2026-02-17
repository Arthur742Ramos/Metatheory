/-
# First-Order Term Syntax and Substitutions

This module defines first-order terms over a signature and
basic substitution operations used by term rewriting systems.
-/

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Basic

namespace Metatheory.TRS.FirstOrder

/-- A first-order signature: function symbols with arities. -/
structure Signature where
  Sym : Type
  arity : Sym -> Nat

/-- First-order terms over a signature. -/
inductive Term (sig : Signature) : Type where
  | var : Nat -> Term sig
  | app : (f : sig.Sym) -> (Fin (sig.arity f) -> Term sig) -> Term sig

noncomputable instance instDecidableEqTerm {sig : Signature} : DecidableEq (Term sig) := by
  classical
  exact Classical.decEq _

/-- Substitutions map variables to terms. -/
abbrev Subst (sig : Signature) := Nat -> Term sig

namespace Term

variable {sig : Signature}

/-- Sum over finite arguments (recursive on arity). -/
def finSum : ∀ {n : Nat}, (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 + finSum (fun i => f (Fin.succ i))

/-- Size of a term (number of nodes). -/
def size : Term sig → Nat
  | var _ => 1
  | app f args =>
    1 + finSum (fun i => size (args i))

/-- Size is always positive. -/
theorem size_pos (t : Term sig) : 0 < size t := by
  induction t with
  | var _ => simp [size]
  | app f args ih =>
    have : 0 < finSum (fun i => size (args i)) + 1 := Nat.succ_pos _
    simpa [size, Nat.add_comm] using this

/-- Any component is bounded by the sum. -/
theorem finSum_ge {n : Nat} (f : Fin n → Nat) (i : Fin n) : f i ≤ finSum f := by
  induction n with
  | zero =>
      exact finZeroElim (α := fun i => f i ≤ finSum f) i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          simp [finSum]
      | succ i =>
          have h := ih (f := fun j => f (Fin.succ j)) (i := i)
          have h' : f (Fin.succ i) ≤ f 0 + finSum (fun j => f (Fin.succ j)) :=
            Nat.le_trans h (Nat.le_add_left _ _)
          simpa [finSum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'

/-- If two functions differ only at one index and increase there, their sums increase. -/
theorem finSum_lt_of_lt {n : Nat} {f g : Fin n → Nat} (i : Fin n)
    (h : f i < g i) (hrest : ∀ j, j ≠ i → f j = g j) :
    finSum f < finSum g := by
  induction n with
  | zero =>
      exact finZeroElim (α := fun _ => finSum f < finSum g) i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          have hrest' : ∀ j, f (Fin.succ j) = g (Fin.succ j) := by
            intro j
            exact hrest (Fin.succ j) (by simp)
          have hfun : (fun j => f (Fin.succ j)) = (fun j => g (Fin.succ j)) := funext hrest'
          have htail : finSum (fun j => f (Fin.succ j)) = finSum (fun j => g (Fin.succ j)) := by
            simp [hfun]
          have hsum : f 0 + finSum (fun j => f (Fin.succ j)) <
              g 0 + finSum (fun j => f (Fin.succ j)) :=
            Nat.add_lt_add_right h (finSum (fun j => f (Fin.succ j)))
          have : f 0 + finSum (fun j => f (Fin.succ j)) <
              g 0 + finSum (fun j => g (Fin.succ j)) := by
            simpa [htail] using hsum
          simpa [finSum] using this
      | succ i =>
          have hne : (0 : Fin (n + 1)) ≠ i.succ := by
            simpa using (Fin.succ_ne_zero i).symm
          have hrest0 : f 0 = g 0 := by
            apply hrest 0
            simpa using hne
          have hrest' : ∀ j, j ≠ i → f (Fin.succ j) = g (Fin.succ j) := by
            intro j hj
            apply hrest (Fin.succ j)
            intro hEq
            exact hj (Fin.succ_injective _ hEq)
          have h' : finSum (fun j => f (Fin.succ j)) < finSum (fun j => g (Fin.succ j)) := by
            have h'' : (fun j => f (Fin.succ j)) i < (fun j => g (Fin.succ j)) i := by
              simpa using h
            exact ih (i := i) h'' hrest'
          have : f 0 + finSum (fun j => f (Fin.succ j)) <
              g 0 + finSum (fun j => g (Fin.succ j)) := by
            have hsum : f 0 + finSum (fun j => f (Fin.succ j)) <
                f 0 + finSum (fun j => g (Fin.succ j)) :=
              Nat.add_lt_add_left h' (f 0)
            simpa [hrest0] using hsum
          simpa [finSum] using this

/-- Apply a substitution to a term. -/
def subst (sub : Subst sig) : Term sig -> Term sig
  | var x => sub x
  | app f args => app f (fun i => subst sub (args i))

/-- Identity substitution. -/
def idSubst : Subst sig := var

/-- Composition of substitutions. -/
def compSubst (sub tau : Subst sig) : Subst sig := fun x => subst sub (tau x)

theorem subst_id (t : Term sig) : subst idSubst t = t := by
  induction t with
  | var _ => rfl
  | app f args ih =>
    apply congrArg (fun args' => app f args')
    funext i
    exact ih i

theorem subst_comp (sub tau : Subst sig) (t : Term sig) :
    subst (compSubst sub tau) t = subst sub (subst tau t) := by
  induction t with
  | var _ => rfl
  | app f args ih =>
    apply congrArg (fun args' => app f args')
    funext i
    exact ih i

end Term

end Metatheory.TRS.FirstOrder
