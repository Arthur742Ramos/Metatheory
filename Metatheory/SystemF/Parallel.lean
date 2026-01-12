/-
# Parallel Reduction for System F

This module defines parallel reduction for System F (polymorphic lambda calculus),
the key tool for proving Church-Rosser.

## Parallel Reduction

Parallel reduction M ⇒ N reduces zero or more redexes in M simultaneously.
The key property is that it has the diamond property, unlike single-step reduction.

## Definition

System F has two kinds of redexes:
- Term beta: (λx:τ. M) N → M[N/x]
- Type beta: (Λα. M) [σ] → M[σ/α]

Parallel reduction contracts any subset of these redexes simultaneously.
This uses FULL reduction (under all binders) for proving Church-Rosser.

## References

- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
-/

import Metatheory.SystemF.StrongNormalization

namespace Metatheory.SystemF

open Ty Term

/-! ## Parallel Reduction Definition -/

/-- Parallel reduction for System F: reduce zero or more redexes simultaneously.

    Uses full reduction (under all binders) for proving Church-Rosser.
    Key insight: This relation HAS the diamond property, unlike StrongStep. -/
inductive ParRed : Term → Term → Prop where
  /-- Variables reduce to themselves -/
  | var : ∀ n, ParRed (var n) (var n)
  /-- Lambda: reduce under binder (type annotation unchanged) -/
  | lam : ∀ {τ M M'}, ParRed M M' → ParRed (lam τ M) (lam τ M')
  /-- Application: reduce both parts -/
  | app : ∀ {M M' N N'}, ParRed M M' → ParRed N N' → ParRed (app M N) (app M' N')
  /-- Type abstraction: reduce under binder -/
  | tlam : ∀ {M M'}, ParRed M M' → ParRed (tlam M) (tlam M')
  /-- Type application: reduce the term (type unchanged) -/
  | tapp : ∀ {M M' τ}, ParRed M M' → ParRed (tapp M τ) (tapp M' τ)
  /-- Term beta: can also fire the redex -/
  | beta : ∀ {τ M M' N N'}, ParRed M M' → ParRed N N' →
           ParRed (app (lam τ M) N) (substTerm0 N' M')
  /-- Type beta: can also fire the type application redex -/
  | tbeta : ∀ {M M' τ}, ParRed M M' →
            ParRed (tapp (tlam M) τ) (substTypeInTerm0 τ M')

/-- Notation for parallel reduction -/
scoped infix:50 " ⇒ " => ParRed

namespace ParRed

/-! ## Reflexivity -/

/-- Parallel reduction is reflexive -/
theorem refl (M : Term) : M ⇒ M := by
  induction M with
  | var n => exact ParRed.var n
  | lam τ M ih => exact ParRed.lam ih
  | app M N ihM ihN => exact ParRed.app ihM ihN
  | tlam M ih => exact ParRed.tlam ih
  | tapp M τ ih => exact ParRed.tapp ih

/-! ## Relationship to Single-Step (Strong) -/

/-- Single-step strong reduction implies parallel reduction -/
theorem of_strongStep {M N : Term} (h : M ⟶ₛ N) : M ⇒ N := by
  induction h with
  | beta τ M N =>
    exact ParRed.beta (refl M) (refl N)
  | tbeta M τ =>
    exact ParRed.tbeta (refl M)
  | lam _ ih =>
    exact ParRed.lam ih
  | appL _ ih =>
    exact ParRed.app ih (refl _)
  | appR _ ih =>
    exact ParRed.app (refl _) ih
  | tlam _ ih =>
    exact ParRed.tlam ih
  | tappL _ ih =>
    exact ParRed.tapp ih

/-! ## Relationship to Multi-Step (Strong) -/

/-- Parallel reduction implies strong multi-step reduction -/
theorem toStrongMulti {M N : Term} (h : M ⇒ N) : M ⟶ₛ* N := by
  induction h with
  | var n => exact StrongMultiStep.refl _
  | lam _ ih => exact StrongMultiStep.lam ih
  | app _ _ ihM ihN =>
    exact StrongMultiStep.trans (StrongMultiStep.appL ihM) (StrongMultiStep.appR ihN)
  | tlam _ ih => exact StrongMultiStep.tlam ih
  | tapp _ ih => exact StrongMultiStep.tappL ih
  | @beta τ M M' N N' _ _ ihM ihN =>
    -- (λx:τ. M) N ⟶ₛ* (λx:τ. M') N' ⟶ₛ M'[N']
    have h1 : Term.app (Term.lam τ M) N ⟶ₛ* Term.app (Term.lam τ M') N' :=
      StrongMultiStep.trans
        (StrongMultiStep.appL (StrongMultiStep.lam ihM))
        (StrongMultiStep.appR ihN)
    have h2 : Term.app (Term.lam τ M') N' ⟶ₛ* substTerm0 N' M' :=
      StrongMultiStep.single (StrongStep.beta τ M' N')
    exact StrongMultiStep.trans h1 h2
  | @tbeta M M' τ _ ih =>
    -- (Λα. M) [τ] ⟶ₛ* (Λα. M') [τ] ⟶ₛ M'[τ/α]
    have h1 : Term.tapp (Term.tlam M) τ ⟶ₛ* Term.tapp (Term.tlam M') τ :=
      StrongMultiStep.tappL (StrongMultiStep.tlam ih)
    have h2 : Term.tapp (Term.tlam M') τ ⟶ₛ* substTypeInTerm0 τ M' :=
      StrongMultiStep.single (StrongStep.tbeta M' τ)
    exact StrongMultiStep.trans h1 h2

/-! ## Auxiliary Lemmas: Term Shifting -/

/-- Term shifting preserves parallel reduction -/
theorem shiftTermUp {M M' : Term} (d c : Nat) (h : M ⇒ M') :
    Term.shiftTermUp d c M ⇒ Term.shiftTermUp d c M' := by
  induction h generalizing c with
  | var n =>
    simp only [Term.shiftTermUp]
    split <;> exact ParRed.var _
  | lam _ ih =>
    simp only [Term.shiftTermUp]
    exact ParRed.lam (ih (c + 1))
  | app _ _ ihM ihN =>
    simp only [Term.shiftTermUp]
    exact ParRed.app (ihM c) (ihN c)
  | tlam _ ih =>
    simp only [Term.shiftTermUp]
    exact ParRed.tlam (ih c)
  | tapp _ ih =>
    simp only [Term.shiftTermUp]
    exact ParRed.tapp (ih c)
  | @beta τ M M' N N' _ _ ihM ihN =>
    simp only [Term.shiftTermUp]
    -- shiftTermUp d c (substTerm0 N' M') = substTerm0 (shiftTermUp d c N') (shiftTermUp d (c + 1) M')
    rw [shiftTermUp_substTerm0]
    exact ParRed.beta (ihM (c + 1)) (ihN c)
  | @tbeta M M' τ _ ih =>
    simp only [Term.shiftTermUp]
    -- shiftTermUp d c (substTypeInTerm0 τ M') = substTypeInTerm0 τ (shiftTermUp d c M')
    rw [shiftTermUp_substTypeInTerm0]
    exact ParRed.tbeta (ih c)

/-- Type shifting in terms preserves parallel reduction -/
theorem shiftTypeInTerm {M M' : Term} (d c : Nat) (h : M ⇒ M') :
    Term.shiftTypeInTerm d c M ⇒ Term.shiftTypeInTerm d c M' := by
  induction h generalizing c with
  | var n =>
    simp only [Term.shiftTypeInTerm]
    exact ParRed.var n
  | lam _ ih =>
    simp only [Term.shiftTypeInTerm]
    exact ParRed.lam (ih c)
  | app _ _ ihM ihN =>
    simp only [Term.shiftTypeInTerm]
    exact ParRed.app (ihM c) (ihN c)
  | tlam _ ih =>
    simp only [Term.shiftTypeInTerm]
    exact ParRed.tlam (ih (c + 1))
  | tapp _ ih =>
    simp only [Term.shiftTypeInTerm]
    exact ParRed.tapp (ih c)
  | @beta τ M M' N N' _ _ ihM ihN =>
    simp only [Term.shiftTypeInTerm]
    -- shiftTypeInTerm d c (substTerm0 N' M') = substTerm0 (shiftTypeInTerm d c N') (shiftTypeInTerm d c M')
    rw [shiftTypeInTerm_substTerm0]
    exact ParRed.beta (ihM c) (ihN c)
  | @tbeta M M' τ _ ih =>
    simp only [Term.shiftTypeInTerm]
    -- shiftTypeInTerm d c (substTypeInTerm0 τ M') = substTypeInTerm0 (shiftTyUp d c τ) (shiftTypeInTerm d (c+1) M')
    rw [shiftTypeInTerm_substTypeInTerm0]
    exact ParRed.tbeta (ih (c + 1))

/-! ## Auxiliary Lemmas: Substitution -/

/-- Parallel reduction is preserved under term substitution -/
theorem substTerm_gen {M M' : Term} (k : Nat) {N N' : Term}
    (hM : M ⇒ M') (hN : N ⇒ N') :
    substTerm k N M ⇒ substTerm k N' M' := by
  induction hM generalizing k N N' with
  | var n =>
    simp only [Term.substTerm]
    split
    · exact ParRed.var _
    · split
      · exact hN
      · exact ParRed.var _
  | lam hBody ih =>
    simp only [Term.substTerm]
    apply ParRed.lam
    exact ih (k + 1) (shiftTermUp 1 0 hN)
  | app hM hN' ihM ihN =>
    simp only [Term.substTerm]
    exact ParRed.app (ihM k hN) (ihN k hN)
  | tlam hBody ih =>
    simp only [Term.substTerm]
    apply ParRed.tlam
    exact ih k (shiftTypeInTerm 1 0 hN)
  | tapp hBody ih =>
    simp only [Term.substTerm]
    exact ParRed.tapp (ih k hN)
  | @beta τ M1 M1' M2 M2' hM1 hM2 ihM1 ihM2 =>
    simp only [Term.substTerm]
    -- substTerm k N' (substTerm0 M2' M1') = substTerm0 (substTerm k N' M2') (substTerm (k+1) (shiftTermUp 1 0 N') M1')
    rw [substTerm_substTerm 0 k (Nat.zero_le k) N' M2' M1']
    exact ParRed.beta (ihM1 (k + 1) (shiftTermUp 1 0 hN)) (ihM2 k hN)
  | @tbeta M1 M1' τ hM1 ihM1 =>
    simp only [Term.substTerm]
    -- Goal: tapp (tlam (substTerm k (shiftTypeInTerm 1 0 N) M1)) τ ⇒ substTerm k N' (substTypeInTerm0 τ M1')
    -- substTerm k N' (substTypeInTerm0 τ M1') = substTypeInTerm0 τ (substTerm k (shiftTypeInTerm 1 0 N') M1')
    have heq : substTerm k N' (substTypeInTerm0 τ M1') =
               substTypeInTerm0 τ (substTerm k (Term.shiftTypeInTerm 1 0 N') M1') := by
      -- substTypeInTerm0 τ (substTerm k (shiftTypeInTerm 1 0 N') M1')
      --   = substTerm k (substTypeInTerm0 τ (shiftTypeInTerm 1 0 N')) (substTypeInTerm0 τ M1')
      --   = substTerm k N' (substTypeInTerm0 τ M1')  -- by cancel lemma
      have h := substTypeInTerm_substTerm (k := 0) (σ := τ) k (Term.shiftTypeInTerm 1 0 N') M1'
      have hcancel : substTypeInTerm 0 τ (Term.shiftTypeInTerm 1 0 N') = N' :=
        substTypeInTerm_shiftTypeInTerm_cancel (k := 0) (σ := τ) N'
      simp only [substTypeInTerm0]
      rw [h, hcancel]
    rw [heq]
    exact ParRed.tbeta (ihM1 k (ParRed.shiftTypeInTerm 1 0 hN))

/-- Parallel reduction is preserved under type substitution in terms -/
theorem substTypeInTerm_parred {M M' : Term} (hM : M ⇒ M') :
    ∀ k τ, substTypeInTerm k τ M ⇒ substTypeInTerm k τ M' := by
  induction hM with
  | var n => intro k τ; simp only [Term.substTypeInTerm]; exact ParRed.var n
  | lam hBody ih =>
    intro k τ
    simp only [Term.substTypeInTerm]
    exact ParRed.lam (ih k τ)
  | app hM hN ihM ihN =>
    intro k τ
    simp only [Term.substTypeInTerm]
    exact ParRed.app (ihM k τ) (ihN k τ)
  | @tlam M M' hBody ih =>
    intro k τ
    simp only [Term.substTypeInTerm]
    exact ParRed.tlam (ih (k + 1) (shiftTyUp 1 0 τ))
  | tapp hBody ih =>
    intro k τ
    simp only [Term.substTypeInTerm]
    exact ParRed.tapp (ih k τ)
  | @beta τ' M1 M1' M2 M2' hM1 hM2 ihM1 ihM2 =>
    intro k τ
    simp only [Term.substTypeInTerm]
    -- substTypeInTerm k τ (substTerm0 M2' M1') = substTerm0 (substTypeInTerm k τ M2') (substTypeInTerm k τ M1')
    rw [substTypeInTerm_substTerm (k := k) (σ := τ) (j := 0) (N := M2') (M := M1')]
    exact ParRed.beta (ihM1 k τ) (ihM2 k τ)
  | @tbeta M1 M1' τ' hM1 ihM1 =>
    intro k τ
    simp only [Term.substTypeInTerm]
    -- substTypeInTerm k τ (substTypeInTerm0 τ' M1') = substTypeInTerm0 (substTy k τ τ') (substTypeInTerm (k+1) (shiftTyUp 1 0 τ) M1')
    rw [substTypeInTerm_substTypeInTerm0 (k := k) (σ := τ) (τ := τ') M1']
    exact ParRed.tbeta (ihM1 (k + 1) (shiftTyUp 1 0 τ))

/-! ## Main Substitution Lemmas -/

/-- Parallel reduction is preserved under term substitution at 0.
    This is the KEY lemma for proving the diamond property. -/
theorem substTerm {M M' N N' : Term} (hM : M ⇒ M') (hN : N ⇒ N') :
    substTerm0 N M ⇒ substTerm0 N' M' := substTerm_gen 0 hM hN

/-- Parallel reduction is preserved under type substitution at 0. -/
theorem substTypeInTerm {M M' : Term} (τ : Ty) (hM : M ⇒ M') :
    substTypeInTerm0 τ M ⇒ substTypeInTerm0 τ M' := substTypeInTerm_parred hM 0 τ

end ParRed

end Metatheory.SystemF
