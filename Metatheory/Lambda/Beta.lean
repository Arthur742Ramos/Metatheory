/-
# Single-Step Beta Reduction

This module defines single-step beta reduction for the lambda calculus.

## Beta Reduction

The fundamental rule is:
  (λM)N →β M[N/0]

We also include congruence rules so reduction can occur anywhere in a term.
-/

import Metatheory.Lambda.Term

namespace Metatheory.Lambda

open Term

/-! ## Single-Step Beta Reduction -/

/-- Single-step beta reduction.
    M →β N means M reduces to N in exactly one step. -/
inductive BetaStep : Term → Term → Prop where
  /-- The fundamental beta rule: (λM)N →β M[N] -/
  | beta : ∀ M N, BetaStep (app (lam M) N) (M[N])
  /-- Congruence in left of application -/
  | appL : ∀ {M M' N}, BetaStep M M' → BetaStep (app M N) (app M' N)
  /-- Congruence in right of application -/
  | appR : ∀ {M N N'}, BetaStep N N' → BetaStep (app M N) (app M N')
  /-- Congruence under lambda -/
  | lam : ∀ {M M'}, BetaStep M M' → BetaStep (lam M) (lam M')

/-- Notation for beta reduction -/
scoped infix:50 " →β " => BetaStep

namespace BetaStep

/-! ## Basic Properties -/

/-- Beta reduction is deterministic at each redex position -/
theorem beta_root (M N : Term) : (ƛ M) @ N →β M[N] := BetaStep.beta M N

/-- Example: (λx.x)M →β M -/
example (M : Term) : Term.I @ M →β M := by
  -- I @ M = (λ(var 0)) @ M →β (var 0)[M] = M
  have h1 : Term.I @ M = Term.app (Term.lam (Term.var 0)) M := rfl
  have h2 : (Term.var 0 : Term)[M] = M := rfl
  conv => lhs; rw [h1]
  conv => rhs; rw [← h2]
  exact BetaStep.beta (Term.var 0) M

end BetaStep

end Metatheory.Lambda
