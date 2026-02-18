/-
# Diamond Property for Parallel Reduction

This module proves the diamond property for parallel reduction,
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
- M ⇒ N₁ implies N₁ ⇒ complete M (by par_complete)
- M ⇒ N₂ implies N₂ ⇒ complete M (by par_complete)

So P = complete M works!
-/

import Metatheory.Lambda.Complete

namespace Metatheory.Lambda

open Term

/-! ## The Diamond Property -/

/-- The diamond property for parallel reduction.

    If M ⇒ N₁ and M ⇒ N₂, then there exists P with N₁ ⇒ P and N₂ ⇒ P.

    Proof: Take P = complete M. By par_complete:
    - N₁ ⇒ complete M
    - N₂ ⇒ complete M -/
theorem diamond {M N₁ N₂ : Term} (h1 : M ⇒ N₁) (h2 : M ⇒ N₂) :
    ∃ P, (N₁ ⇒ P) ∧ (N₂ ⇒ P) :=
  ⟨complete M, par_complete h1, par_complete h2⟩

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

    If M ⇒ N and M →* P, then there exists Q with N →* Q and P ⇒ Q. -/
theorem strip {M N P : Term} (hpar : M ⇒ N) (hmulti : M →* P) :
    ∃ Q, (N →* Q) ∧ (P ⇒ Q) := by
  induction hmulti generalizing N with
  | refl _ =>
    -- M = P, need Q with N →* Q and M ⇒ Q
    -- Take Q = N, then N →* N (refl) and M ⇒ N (given)
    exact ⟨N, MultiStep.refl N, hpar⟩
  | step hstep _hmulti' ih =>
    -- We're in M →β M' →* P
    -- hstep : M →β M', _hmulti' : M' →* P
    -- hpar : M ⇒ N (from outer scope via generalizing)
    -- Use diamond: M ⇒ N and M ⇒ M' (since →β implies ⇒)
    have hpar' := ParRed.of_beta hstep
    obtain ⟨Q₁, hN_Q₁, hM'_Q₁⟩ := diamond hpar hpar'
    -- Now M' ⇒ Q₁ and N ⇒ Q₁
    -- Apply IH: M' ⇒ Q₁ and M' →* P gives Q with Q₁ →* Q and P ⇒ Q
    obtain ⟨Q, hQ₁_Q, hP_Q⟩ := ih hM'_Q₁
    -- Chain: N ⇒ Q₁ →* Q
    exact ⟨Q, MultiStep.trans (ParRed.toMulti hN_Q₁) hQ₁_Q, hP_Q⟩

/-! ## Alternative Diamond Formulation -/

/-- Diamond property packaged as a structure -/
structure DiamondWitness (M N₁ N₂ : Term) where
  peak : Term
  left : N₁ ⇒ peak
  right : N₂ ⇒ peak

/-- Construct the diamond witness -/
def mkDiamond {M N₁ N₂ : Term} (h1 : M ⇒ N₁) (h2 : M ⇒ N₂) : DiamondWitness M N₁ N₂ :=
  ⟨complete M, par_complete h1, par_complete h2⟩

end Metatheory.Lambda
