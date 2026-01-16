/-
# Church-Rosser Theorem (Confluence) for System F

This module proves the Church-Rosser theorem: full (strong) reduction in System F
is confluent.

## The Church-Rosser Theorem

If M →ₛ* N₁ and M →ₛ* N₂, then there exists P such that N₁ →ₛ* P and N₂ →ₛ* P.

```
      M
     / \
    →*  →*
   /     \
  N₁     N₂
   \     /
    →*  →*
     \ /
      P
```

## Proof Strategy

We use the strip lemma repeatedly:
1. First, induct on M →ₛ* N₂ to build up parallel steps
2. Use strip lemma to complete each parallel step with the multi-step M →ₛ* N₁

## References

- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
-/

import Metatheory.SystemF.Diamond

namespace Metatheory.SystemF

open Term

/-! ## The Church-Rosser Theorem -/

/-- The Church-Rosser theorem: strong (full) reduction in System F is confluent.

    If M →ₛ* N₁ and M →ₛ* N₂, then there exists P with N₁ →ₛ* P and N₂ →ₛ* P. -/
theorem confluence {M N₁ N₂ : Term} (h1 : M ⟶ₛ* N₁) (h2 : M ⟶ₛ* N₂) :
    ∃ P, (N₁ ⟶ₛ* P) ∧ (N₂ ⟶ₛ* P) := by
  -- Induct on h2 : M →ₛ* N₂
  induction h2 generalizing N₁ with
  | refl _ =>
    -- M = N₂, so we can take P = N₁
    exact ⟨N₁, StrongMultiStep.refl N₁, h1⟩
  | step hstep _hmulti ih =>
    -- M →ₛ M' →ₛ* N₂
    -- We have M →ₛ* N₁ (from outer scope via generalizing)
    -- Use strip lemma: M ⇒ M' (from →ₛ) and M →ₛ* N₁ gives Q with M' →ₛ* Q and N₁ ⇒ Q
    have hpar := ParRed.of_strongStep hstep
    obtain ⟨Q, hM'_Q, hN₁_Q⟩ := strip hpar h1
    -- Now apply IH with M' →ₛ* Q: gives P with Q →ₛ* P and N₂ →ₛ* P
    obtain ⟨P, hQ_P, hN₂_P⟩ := ih hM'_Q
    -- Chain: N₁ ⇒ Q →ₛ* P, so N₁ →ₛ* P
    exact ⟨P, StrongMultiStep.trans (ParRed.toStrongMulti hN₁_Q) hQ_P, hN₂_P⟩

/-- Alternative formulation: the diagram commutes -/
theorem church_rosser {M N₁ N₂ : Term} (h1 : M ⟶ₛ* N₁) (h2 : M ⟶ₛ* N₂) :
    ∃ P, (N₁ ⟶ₛ* P) ∧ (N₂ ⟶ₛ* P) := confluence h1 h2

/-! ## Corollaries -/

/-- Beta-equivalent terms have a common reduct -/
theorem common_reduct {M N : Term} (h : M ⟶ₛ* N ∨ N ⟶ₛ* M) :
    ∃ P, (M ⟶ₛ* P) ∧ (N ⟶ₛ* P) := by
  cases h with
  | inl h => exact ⟨N, h, StrongMultiStep.refl N⟩
  | inr h => exact ⟨M, StrongMultiStep.refl M, h⟩

/-- If M and N both reduce to some common term, they have a common reduct -/
theorem diamond_multi {M N P : Term} (h1 : M ⟶ₛ* P) (h2 : N ⟶ₛ* P) :
    ∃ Q, (M ⟶ₛ* Q) ∧ (N ⟶ₛ* Q) :=
  ⟨P, h1, h2⟩

/-! ## Normal Forms -/

/-- A term is in strong normal form if it cannot reduce further under strong reduction -/
def IsStrongNormalForm (M : Term) : Prop := ∀ N, ¬(M ⟶ₛ N)

/-- Strong normal forms are unique (up to confluence) -/
theorem strong_normal_form_unique {M N₁ N₂ : Term}
    (h1 : M ⟶ₛ* N₁) (h2 : M ⟶ₛ* N₂)
    (hn1 : IsStrongNormalForm N₁) (hn2 : IsStrongNormalForm N₂) :
    N₁ = N₂ := by
  -- By confluence, there exists P with N₁ →ₛ* P and N₂ →ₛ* P
  obtain ⟨P, hN₁_P, hN₂_P⟩ := confluence h1 h2
  -- Since N₁ is in normal form, N₁ →ₛ* P means N₁ = P
  have eq1 : N₁ = P := by
    cases hN₁_P with
    | refl _ => rfl
    | step hstep _ => exact absurd hstep (hn1 _)
  -- Similarly, N₂ = P
  have eq2 : N₂ = P := by
    cases hN₂_P with
    | refl _ => rfl
    | step hstep _ => exact absurd hstep (hn2 _)
  -- Therefore N₁ = N₂
  rw [eq1, eq2]

/-- Strong normalization implies existence of a strong normal form. -/
theorem has_strong_normal_form {M : Term} (hM : SN M) :
    ∃ N, M ⟶ₛ* N ∧ IsStrongNormalForm N := by
  classical
  have hnf := Rewriting.hasNormalForm_of_acc (r := StrongStep) hM
  rcases hnf with ⟨N, hMN, hNnf⟩
  have hMN' : M ⟶ₛ* N := StrongMultiStep.of_star hMN
  have hNnf' : IsStrongNormalForm N := by
    intro P hstep
    exact hNnf P hstep
  exact ⟨N, hMN', hNnf'⟩

/-! ## Connection to Generic Framework -/

/-- Strong reduction is confluent (as a Rewriting.Confluent instance) -/
theorem strongStep_confluent : Rewriting.Confluent StrongStep := by
  intro M N₁ N₂ h1 h2
  -- Convert Rewriting.Star to StrongMultiStep
  have h1' : M ⟶ₛ* N₁ := StrongMultiStep.of_star h1
  have h2' : M ⟶ₛ* N₂ := StrongMultiStep.of_star h2
  obtain ⟨P, hN₁_P, hN₂_P⟩ := confluence h1' h2'
  exact ⟨P, StrongMultiStep.to_star hN₁_P, StrongMultiStep.to_star hN₂_P⟩

/-- Strong reduction is confluent in the generic rewriting framework. -/
theorem confluent_strongStep : Rewriting.Confluent StrongStep :=
  strongStep_confluent

/-- Strong reduction is Church-Rosser (alias of confluence). -/
theorem church_rosser_strongStep : Rewriting.Metatheory StrongStep :=
  strongStep_confluent

/-! ## Summary

We have proven the Church-Rosser theorem for System F strong (full) reduction:

1. **Types.lean**: Defined System F types with de Bruijn indices
2. **Terms.lean**: Defined System F terms (λ, Λ, application, type application)
3. **Typing.lean**: Defined typing relation for System F
4. **StrongNormalization.lean**: Defined strong reduction and substitution lemmas
5. **Parallel.lean**: Defined parallel reduction for System F
6. **Complete.lean**: Defined complete development and proved parRed_complete
7. **Diamond.lean**: Proved the diamond property for parallel reduction
8. **Confluence.lean**: Proved the Church-Rosser theorem

The key insight is using parallel reduction and complete development:
- Parallel reduction has the diamond property
- Complete development M⁺ is the "maximal reduct" of M
- If M ⇒ N, then N ⇒ M⁺
- This makes proving diamond trivial: both sides reduce to M⁺

System F has two kinds of redexes:
- Term beta: (λx:τ. M) N → M[N/x]
- Type beta: (Λα. M) [σ] → M[σ/α]

Both are handled uniformly by parallel reduction and complete development.
-/

end Metatheory.SystemF
