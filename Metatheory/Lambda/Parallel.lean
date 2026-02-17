/-
# Parallel Reduction

This module defines parallel reduction, the key tool for proving Church-Rosser.

## Parallel Reduction

Parallel reduction M ⇒ N reduces zero or more redexes in M simultaneously.
The key property is that it has the diamond property, unlike single-step reduction.

## Definition

- Variables reduce to themselves
- Applications reduce component-wise
- Lambdas reduce under the binder
- Beta redexes can also fire: (λM)N ⇒ M'[N'] when M ⇒ M' and N ⇒ N'
-/

import Metatheory.Lambda.MultiStep

namespace Metatheory.Lambda

open Term

/-! ## Parallel Reduction Definition -/

/-- Parallel reduction: reduce zero or more redexes simultaneously.

    Key insight: This relation HAS the diamond property, unlike BetaStep. -/
inductive ParRed : Term → Term → Prop where
  /-- Variables reduce to themselves -/
  | var : ∀ n, ParRed (var n) (var n)
  /-- Application: reduce both parts -/
  | app : ∀ {M M' N N'}, ParRed M M' → ParRed N N' → ParRed (app M N) (app M' N')
  /-- Lambda: reduce under binder -/
  | lam : ∀ {M M'}, ParRed M M' → ParRed (lam M) (lam M')
  /-- Beta: can also fire the redex -/
  | beta : ∀ {M M' N N'}, ParRed M M' → ParRed N N' →
           ParRed (app (lam M) N) (M'[N'])

/-- Notation for parallel reduction -/
scoped infix:50 " ⇒ " => ParRed

namespace ParRed

/-! ## Reflexivity -/

/-- Parallel reduction is reflexive -/
theorem refl (M : Term) : M ⇒ M := by
  induction M with
  | var n => exact ParRed.var n
  | app M N ih_M ih_N => exact ParRed.app ih_M ih_N
  | lam M ih => exact ParRed.lam ih

/-! ## Relationship to Single-Step -/

/-- Single-step beta reduction implies parallel reduction -/
theorem of_beta {M N : Term} (h : M →β N) : M ⇒ N := by
  induction h with
  | beta M N =>
    exact ParRed.beta (refl M) (refl N)
  | appL _ ih =>
    exact ParRed.app ih (refl _)
  | appR _ ih =>
    exact ParRed.app (refl _) ih
  | lam _ ih =>
    exact ParRed.lam ih

/-! ## Relationship to Multi-Step -/

/-- Parallel reduction implies multi-step reduction -/
theorem toMulti {M N : Term} (h : M ⇒ N) : M →* N := by
  induction h with
  | var n => exact MultiStep.refl _
  | app _ _ ih_M ih_N => exact MultiStep.app ih_M ih_N
  | lam _ ih => exact MultiStep.lam ih
  | @beta M M' N N' _ _ ih_M ih_N =>
    -- (λM)N →* (λM')N' →* M'[N']
    have h1 : (Term.lam M) @ N →* (Term.lam M') @ N' := MultiStep.app (MultiStep.lam ih_M) ih_N
    have h2 : (Term.lam M') @ N' →* M'[N'] := MultiStep.single (BetaStep.beta M' N')
    exact MultiStep.trans h1 h2

/-! ## Auxiliary Substitution Lemmas -/

/-- Shifting preserves parallel reduction -/
theorem shift {M M' : Term} (d : Nat) (c : Nat) (h : M ⇒ M') :
    Term.shift d c M ⇒ Term.shift d c M' := by
  induction h generalizing c with
  | var n =>
    simp only [Term.shift]
    split
    · exact ParRed.var _
    · exact ParRed.var _
  | app _ _ ih_M ih_N =>
    simp only [Term.shift]
    exact ParRed.app (ih_M c) (ih_N c)
  | lam _ ih =>
    simp only [Term.shift]
    exact ParRed.lam (ih (c + 1))
  | beta _ _ ih_M ih_N =>
    simp only [Term.shift]
    -- Need to show: shift d c ((λM)N) ⇒ shift d c (M'[N'])
    -- LHS = (λ(shift d (c+1) M))(shift d c N)
    -- RHS = shift d c (M'[N'])
    -- Use beta rule with ih_M (c+1) and ih_N c
    rw [Term.shift_subst]
    -- Now RHS is (shift d (c+1) M')[shift d c N']
    -- Apply beta with the inductive hypotheses
    exact ParRed.beta (ih_M (c + 1)) (ih_N c)

/-- Parallel reduction is preserved under general substitution -/
theorem subst_gen {M M' : Term} (j : Nat) {N N' : Term}
    (hM : M ⇒ M') (hN : N ⇒ N') :
    Term.subst j N M ⇒ Term.subst j N' M' := by
  -- Induction on the parallel reduction hM : M ⇒ M'
  induction hM generalizing j N N' with
  | var n =>
    -- Case: M = var n, M' = var n
    -- Need: subst j N (var n) ⇒ subst j N' (var n)
    simp only [Term.subst]
    split
    · -- n = j: subst j N (var j) = N, subst j N' (var j) = N'
      -- Need: N ⇒ N'
      exact hN
    · split
      · -- n > j: subst j N (var n) = var (n-1), subst j N' (var n) = var (n-1)
        exact ParRed.var _
      · -- n < j: subst j N (var n) = var n, subst j N' (var n) = var n
        exact ParRed.var _
  | app hM1 hM2 ih_M ih_N =>
    -- Case: M = app M₁ M₂, M' = app M₁' M₂'
    -- IH: subst j N M₁ ⇒ subst j N' M₁', subst j N M₂ ⇒ subst j N' M₂'
    simp only [Term.subst]
    exact ParRed.app (ih_M j hN) (ih_N j hN)
  | lam hM ih =>
    -- Case: M = lam M₀, M' = lam M₀'
    -- Need: subst j N (lam M₀) ⇒ subst j N' (lam M₀')
    -- LHS = lam (subst (j+1) (shift1 N) M₀)
    -- RHS = lam (subst (j+1) (shift1 N') M₀')
    simp only [Term.subst]
    apply ParRed.lam
    -- Need: subst (j+1) (shift1 N) M₀ ⇒ subst (j+1) (shift1 N') M₀'
    -- Use IH with j+1 and shifted N, N'
    have h_shift : Term.shift1 N ⇒ Term.shift1 N' := shift 1 0 hN
    exact ih (j + 1) h_shift
  | @beta M1 M1' M2 M2' hM1 hM2 ih_M ih_N =>
    -- Case: M = app (lam M1) M2, M' = M1'[M2']
    -- Need: subst j N (app (lam M1) M2) ⇒ subst j N' M1'[M2']
    -- LHS = subst j N (app (lam M1) M2)
    --     = app (subst j N (lam M1)) (subst j N M2)
    --     = app (lam (subst (j+1) (shift1 N) M1)) (subst j N M2)
    -- RHS = subst j N' (M1'[M2'])
    --     = subst j N' (Term.subst 0 M2' M1')
    simp only [Term.subst]
    -- After simplification, the goal is:
    -- app (lam (subst (j+1) (shift 1 0 N) M1)) (subst j N M2) ⇒ subst j N' (M1'[M2'])
    -- But shift1 is notation for shift 1 0, so this might display as shift1
    --
    -- Apply IHs to get parallel reductions
    have h1 := ih_M (j+1) (shift 1 0 hN)
    have h2 := ih_N j hN
    -- Beta rule gives us: (λ A) B ⇒ A'[B'] when A ⇒ A' and B ⇒ B'
    -- We get: app (lam (subst (j+1) (shift 1 0 N) M1)) (subst j N M2) ⇒
    --        (subst (j+1) (shift 1 0 N') M1')[subst j N' M2']
    --
    -- But we need to show it reduces to: subst j N' (M1'[M2'])
    -- These are equal by substitution composition
    -- This is the key substitution composition lemma (standard de Bruijn infrastructure)
    have h_eq : (Term.subst (j+1) (Term.shift 1 0 N') M1')[Term.subst j N' M2'] =
                Term.subst j N' (M1'[M2']) := Term.subst_subst_gen M1' N' M2' j
    -- Rewrite the RHS of the beta reduction to match our goal
    have h_beta := ParRed.beta h1 h2
    -- h_beta : app (lam (subst (j+1) (shift 1 0 N) M1)) (subst j N M2) ⇒
    --          (subst (j+1) (shift 1 0 N') M1')[subst j N' M2']
    -- Convert using h_eq
    simp only [← h_eq]
    exact h_beta

/-! ## Substitution Lemma (KEY!) -/

/-- Parallel reduction is preserved under substitution.
    This is the KEY lemma for proving the diamond property.

    If M ⇒ M' and N ⇒ N', then M[N] ⇒ M'[N']. -/
theorem subst {M M' N N' : Term} (hM : M ⇒ M') (hN : N ⇒ N') :
    M[N] ⇒ M'[N'] := subst_gen 0 hM hN

end ParRed

end Metatheory.Lambda
