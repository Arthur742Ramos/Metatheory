/-
# Diamond Property for System F Parallel Reduction

This module proves the diamond property for parallel reduction in System F,
which is the key step toward Church-Rosser.

## The Diamond Property

If M ⇒ N₁ and M ⇒ N₂, then there exists P such that N₁ ⇒ P and N₂ ⇒ P.

```
      M
     / \
    ⇒   ⇒
   /     \
  N₁     N₂
   \     /
    ⇒   ⇒
     \ /
      P
```

## Proof Strategy

Using complete development, we simply take P = complete M:
- M ⇒ N₁ implies N₁ ⇒ complete M (by parRed_complete)
- M ⇒ N₂ implies N₂ ⇒ complete M (by parRed_complete)

So P = complete M works!

## References

- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
-/

import Metatheory.SystemF.Complete
import Metatheory.Rewriting.Basic

namespace Metatheory.SystemF

open Term

/-! ## The Diamond Property -/

/-- The diamond property for parallel reduction.

    If M ⇒ N₁ and M ⇒ N₂, then there exists P with N₁ ⇒ P and N₂ ⇒ P.

    Proof: Take P = complete M. By parRed_complete:
    - N₁ ⇒ complete M
    - N₂ ⇒ complete M -/
theorem diamond {M N₁ N₂ : Term} (h1 : M ⇒ N₁) (h2 : M ⇒ N₂) :
    ∃ P, (N₁ ⇒ P) ∧ (N₂ ⇒ P) :=
  ⟨complete M, parRed_complete h1, parRed_complete h2⟩

/-! ## Strip Lemma

The strip lemma connects parallel reduction with multi-step reduction.
It's used to lift the diamond property from parallel to multi-step. -/

/-- Strip lemma: parallel step followed by multi-step can be completed.

    ```
        M ⇒ N
        |     \
        →*     ⇒
        |       \
        P →* →* Q
    ```

    If M ⇒ N and M →ₛ* P, then there exists Q with N →ₛ* Q and P ⇒ Q. -/
theorem strip {M N P : Term} (hpar : M ⇒ N) (hmulti : M ⟶ₛ* P) :
    ∃ Q, (N ⟶ₛ* Q) ∧ (P ⇒ Q) := by
  induction hmulti generalizing N with
  | refl _ =>
    -- M = P, need Q with N →ₛ* Q and M ⇒ Q
    -- Take Q = N, then N →ₛ* N (refl) and M ⇒ N (given)
    exact ⟨N, StrongMultiStep.refl N, hpar⟩
  | step hstep _hmulti' ih =>
    -- We're in M →ₛ M' →ₛ* P
    -- hstep : M →ₛ M', _hmulti' : M' →ₛ* P
    -- hpar : M ⇒ N (from outer scope via generalizing)
    -- Use diamond: M ⇒ N and M ⇒ M' (since →ₛ implies ⇒)
    have hpar' := ParRed.of_strongStep hstep
    obtain ⟨Q₁, hN_Q₁, hM'_Q₁⟩ := diamond hpar hpar'
    -- Now M' ⇒ Q₁ and N ⇒ Q₁
    -- Apply IH: M' ⇒ Q₁ and M' →ₛ* P gives Q with Q₁ →ₛ* Q and P ⇒ Q
    obtain ⟨Q, hQ₁_Q, hP_Q⟩ := ih hM'_Q₁
    -- Chain: N ⇒ Q₁ →ₛ* Q
    exact ⟨Q, StrongMultiStep.trans (ParRed.toStrongMulti hN_Q₁) hQ₁_Q, hP_Q⟩

/-! ## Alternative Diamond Formulation -/

/-- Diamond property packaged as a structure -/
structure DiamondWitness (M N₁ N₂ : Term) where
  peak : Term
  left : N₁ ⇒ peak
  right : N₂ ⇒ peak

/-- Construct the diamond witness -/
def mkDiamond {M N₁ N₂ : Term} (h1 : M ⇒ N₁) (h2 : M ⇒ N₂) : DiamondWitness M N₁ N₂ :=
  ⟨complete M, parRed_complete h1, parRed_complete h2⟩

/-! ## Connection to Generic Framework -/

/-- ParRed satisfies the generic diamond property -/
theorem parRed_diamond : Rewriting.Diamond ParRed := fun _ _ _ h1 h2 => diamond h1 h2

end Metatheory.SystemF
