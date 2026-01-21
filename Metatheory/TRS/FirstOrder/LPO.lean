/-
# Lexicographic Path Ordering (LPO)

A proper implementation of the Lexicographic Path Ordering with precedence.
LPO is a simplification ordering used for proving termination of TRSs.
-/

import Metatheory.TRS.FirstOrder.Confluence

namespace Metatheory.TRS.FirstOrder

open Term

/-! ## Precedence -/

/-- A precedence is a strict partial order on symbols. -/
structure Precedence (sig : Signature) where
  /-- The strict ordering relation on symbols. -/
  lt : sig.Sym → sig.Sym → Prop
  /-- The ordering is irreflexive. -/
  irrefl : ∀ f, ¬ lt f f
  /-- The ordering is transitive. -/
  trans : ∀ f g h, lt f g → lt g h → lt f h

/-! ## LPO Definition -/

/-- Lexicographic Path Ordering on terms.
    s >_lpo t if one of the following holds:
    1. s = f(s₁,...,sₙ) and sᵢ = t for some i (subterm equality)
    2. s = f(s₁,...,sₙ) and sᵢ >_lpo t for some i (subterm strict)
    3. s = f(s₁,...,sₘ) and t = g(t₁,...,tₙ) with f > g and s >_lpo tⱼ for all j
    4. s = f(s₁,...,sₘ) and t = f(t₁,...,tₙ) with lexicographic comparison
       and s >_lpo tⱼ for all j
-/
inductive LPO {sig : Signature} (prec : Precedence sig) : Term sig → Term sig → Prop where
  | subEq : ∀ {f : sig.Sym} {args : Fin (sig.arity f) → Term sig} {i : Fin (sig.arity f)},
      LPO prec (Term.app f args) (args i)
  | subLt : ∀ {f : sig.Sym} {args : Fin (sig.arity f) → Term sig} {t : Term sig} {i : Fin (sig.arity f)},
      LPO prec (args i) t →
      LPO prec (Term.app f args) t
  | precGt : ∀ {f g : sig.Sym} {args : Fin (sig.arity f) → Term sig} {args' : Fin (sig.arity g) → Term sig},
      prec.lt g f →
      (∀ j, LPO prec (Term.app f args) (args' j)) →
      LPO prec (Term.app f args) (Term.app g args')
  | lexEq : ∀ {f : sig.Sym} {args args' : Fin (sig.arity f) → Term sig} {k : Fin (sig.arity f)},
      (∀ i, i < k → args i = args' i) →
      LPO prec (args k) (args' k) →
      (∀ j, LPO prec (Term.app f args) (args' j)) →
      LPO prec (Term.app f args) (Term.app f args')

/-- LPO is greater-than-or-equal. -/
def LPOge {sig : Signature} (prec : Precedence sig) (s t : Term sig) : Prop :=
  s = t ∨ LPO prec s t

/-! ## Basic LPO Properties -/

/-- Variables are not LPO-greater than anything. -/
theorem lpo_var_not_gt {sig : Signature} (prec : Precedence sig) (x : Nat) (t : Term sig) :
    ¬ LPO prec (Term.var x) t := by
  intro h
  cases h

/-- If s > t via subEq, then t is an argument of s. -/
theorem lpo_subEq_arg {sig : Signature} (prec : Precedence sig)
    {f : sig.Sym} {args : Fin (sig.arity f) → Term sig} {i : Fin (sig.arity f)} :
    LPO prec (Term.app f args) (args i) := LPO.subEq

/-! ## Stable LPO -/

/-- Stable LPO: holds under all substitutions. -/
def StableLPO {sig : Signature} (prec : Precedence sig) (s t : Term sig) : Prop :=
  ∀ sub : Subst sig, LPO prec (Term.subst sub s) (Term.subst sub t)

/-- Stable LPO is closed under substitution by definition. -/
theorem stableLPO_subst {sig : Signature} (prec : Precedence sig)
    {sub : Subst sig} {s t : Term sig}
    (h : StableLPO prec s t) :
    StableLPO prec (Term.subst sub s) (Term.subst sub t) := by
  intro sub'
  have := h (Term.compSubst sub' sub)
  simpa [Term.subst_comp] using this

/-! ## LPO Examples -/

/-- Example precedence: total order on symbols by some encoding. -/
def totalPrecedence (sig : Signature) [LinearOrder sig.Sym] : Precedence sig where
  lt := (· < ·)
  irrefl := lt_irrefl
  trans := fun _ _ _ => lt_trans

end Metatheory.TRS.FirstOrder
