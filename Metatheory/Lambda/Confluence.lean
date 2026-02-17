/-
# Church-Rosser Theorem (Confluence)

This module proves the Church-Rosser theorem: beta reduction is confluent.

## The Church-Rosser Theorem

If M →* N₁ and M →* N₂, then there exists P such that N₁ →* P and N₂ →* P.

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
1. First, induct on M →* N₂ to build up parallel steps
2. Use strip lemma to complete each parallel step with the multi-step M →* N₁
-/

import Metatheory.Lambda.Diamond

namespace Metatheory.Lambda

open Term

/-! ## The Church-Rosser Theorem -/

/-- The Church-Rosser theorem: beta reduction is confluent.

    If M →* N₁ and M →* N₂, then there exists P with N₁ →* P and N₂ →* P. -/
theorem confluence {M N₁ N₂ : Term} (h1 : M →* N₁) (h2 : M →* N₂) :
    ∃ P, (N₁ →* P) ∧ (N₂ →* P) := by
  -- Induct on h2 : M →* N₂
  induction h2 generalizing N₁ with
  | refl _ =>
    -- M = N₂, so we can take P = N₁
    exact ⟨N₁, MultiStep.refl N₁, h1⟩
  | step hstep _hmulti ih =>
    -- M →β M' →* N₂
    -- We have M →* N₁ (from outer scope via generalizing)
    -- Use strip lemma: M ⇒ M' (from →β) and M →* N₁ gives Q with M' →* Q and N₁ ⇒ Q
    have hpar := ParRed.of_beta hstep
    obtain ⟨Q, hM'_Q, hN₁_Q⟩ := strip hpar h1
    -- Now apply IH with M' →* Q: gives P with Q →* P and N₂ →* P
    obtain ⟨P, hQ_P, hN₂_P⟩ := ih hM'_Q
    -- Chain: N₁ ⇒ Q →* P, so N₁ →* P
    exact ⟨P, MultiStep.trans (ParRed.toMulti hN₁_Q) hQ_P, hN₂_P⟩

/-- Alternative formulation: the diagram commutes -/
theorem church_rosser {M N₁ N₂ : Term} (h1 : M →* N₁) (h2 : M →* N₂) :
    ∃ P, (N₁ →* P) ∧ (N₂ →* P) := confluence h1 h2

/-! ## Corollaries -/

/-- Beta-equivalent terms have a common reduct -/
theorem common_reduct {M N : Term} (h : M →* N ∨ N →* M) :
    ∃ P, (M →* P) ∧ (N →* P) := by
  cases h with
  | inl h => exact ⟨N, h, MultiStep.refl N⟩
  | inr h => exact ⟨M, MultiStep.refl M, h⟩

/-- If M and N both reduce to some common term, they have a common reduct -/
theorem diamond_multi {M N P : Term} (h1 : M →* P) (h2 : N →* P) :
    ∃ Q, (M →* Q) ∧ (N →* Q) :=
  ⟨P, h1, h2⟩

/-! ## Normal Forms -/

/-- A term is in normal form if it cannot reduce further -/
def IsNormalForm (M : Term) : Prop := ∀ N, ¬(M →β N)

/-- Normal forms are unique (up to confluence) -/
theorem normal_form_unique {M N₁ N₂ : Term}
    (h1 : M →* N₁) (h2 : M →* N₂)
    (hn1 : IsNormalForm N₁) (hn2 : IsNormalForm N₂) :
    N₁ = N₂ := by
  -- By confluence, there exists P with N₁ →* P and N₂ →* P
  obtain ⟨P, hN₁_P, hN₂_P⟩ := confluence h1 h2
  -- Since N₁ is in normal form, N₁ →* P means N₁ = P
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

/-! ## Summary

We have proven the Church-Rosser theorem for beta reduction:

1. **Term.lean**: Defined lambda terms with de Bruijn indices
2. **Beta.lean**: Defined single-step beta reduction
3. **MultiStep.lean**: Defined multi-step reduction (reflexive-transitive closure)
4. **Parallel.lean**: Defined parallel reduction (reduces all redexes at once)
5. **Complete.lean**: Defined complete development and proved par_complete
6. **Diamond.lean**: Proved the diamond property for parallel reduction
7. **Confluence.lean**: Proved the Church-Rosser theorem

The key insight is using parallel reduction and complete development:
- Parallel reduction has the diamond property
- Complete development M⁺ is the "maximal reduct" of M
- If M ⇒ N, then N ⇒ M⁺
- This makes proving diamond trivial: both sides reduce to M⁺
-/

end Metatheory.Lambda
