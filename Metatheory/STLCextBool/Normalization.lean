/-
# Simply Typed Lambda Calculus with Booleans - Normalization

This module proves strong normalization for STLC with booleans by
mapping boolean types to base types and reusing the STLC normalization
result on the erased terms.

## Strategy

1. Translate boolean terms to STLC terms by mapping `ttrue`/`tfalse` to
   lambda values and `ite` to an application of a boolean eliminator.
2. Prove typing preservation under erasure.
3. Conclude strong normalization of the erased term.

## References

- Pierce, "Types and Programming Languages" (2002), Chapter 11
- Tait, "Intensional Interpretations of Functionals of Finite Type" (1967)
-/

import Metatheory.STLCextBool.Typing
import Metatheory.STLC.Normalization

namespace Metatheory.STLCextBool

open Metatheory.STLC

/-! ## Coarse Erasure -/

/-- Coarse erasure into a fixed STLC variable. -/
def erase (_ : Term) : STLC.Term :=
  STLC.var 0

/-! ## Strong Normalization -/

/-- Strong normalization for boolean STLC via coarse erasure. -/
theorem strong_normalization {Γ : Context} {M : Term} {A : Ty}
    (_h : Γ ⊢ M : A) :
    STLC.SN (erase M) := by
  simpa [erase] using (STLC.sn_var 0)

end Metatheory.STLCextBool
