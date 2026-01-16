/-
# Simply Typed Lambda Calculus with Booleans - Normalization

This module proves strong normalization for STLC with booleans by
mapping boolean types to sums of unit in STLCext and reusing its
normalization result on the erased terms.

## Strategy

1. Translate boolean terms to STLCext terms by mapping `ttrue`/`tfalse`
   to injections into `unit ⊕ unit` and `ite` to a case analysis.
2. Prove typing preservation under erasure.
3. Conclude strong normalization of the erased term.

## References

- Pierce, "Types and Programming Languages" (2002), Chapter 11
- Tait, "Intensional Interpretations of Functionals of Finite Type" (1967)
-/

import Metatheory.STLCextBool.Typing
import Metatheory.STLCext.Normalization

namespace Metatheory.STLCextBool

open Metatheory.STLCext


/-- Axiom-free version of List.getElem?_map. -/
theorem List.getElem?_map_af {α β : Type} (f : α → β) (l : List α) (n : Nat) :
    (l.map f)[n]? = l[n]?.map f := by
  induction l generalizing n with
  | nil => rfl
  | cons a as ih =>
    cases n with
    | zero => rfl
    | succ n' => exact ih n'


/-! ## Type and Term Erasure -/

/-- Translate boolean types into STLCext types (booleans become unit sums). -/
def eraseTy : Ty → STLCext.Ty
  | Ty.base n => STLCext.Ty.base (n + 1)
  | Ty.arr A B => STLCext.Ty.arr (eraseTy A) (eraseTy B)
  | Ty.bool => STLCext.Ty.unit ⊕ STLCext.Ty.unit

/-- Translate contexts by erasing types. -/
def eraseCtx : Context → STLCext.Context :=
  List.map eraseTy

/-- Translate boolean terms to STLCext terms. -/
def erase : Term → STLCext.Term
  | Term.var n => STLCext.Term.var n
  | Term.lam M => STLCext.Term.lam (erase M)
  | Term.app M N => STLCext.Term.app (erase M) (erase N)
  | Term.ttrue => STLCext.Term.inl STLCext.Term.unit
  | Term.tfalse => STLCext.Term.inr STLCext.Term.unit
  | Term.ite M N₁ N₂ =>
    STLCext.Term.case (erase M)
      (STLCext.Term.shift1 (erase N₁))
      (STLCext.Term.shift1 (erase N₂))

/-! ## Typing Preservation -/

/-- Type erasure preserves typing. -/
theorem erase_typing {Γ : Context} {M : Term} {A : Ty} (h : Γ ⊢ M : A) :
    eraseCtx Γ ⊢ erase M : eraseTy A := by
  induction h with
  | @var Γ' n A' hget =>
    apply STLCext.HasType.var
    have hmap : (eraseCtx Γ')[n]? = (Γ'[n]?).map eraseTy :=
      List.getElem?_map_af eraseTy Γ' n
    rw [hget] at hmap
    simpa [eraseCtx] using hmap
  | @lam Γ' M' A' B' hbody ih =>
    apply STLCext.HasType.lam
    have ih' : eraseTy A' :: eraseCtx Γ' ⊢ erase M' : eraseTy B' := by
      simp [eraseCtx] at ih
      exact ih
    exact ih'
  | @app Γ' M' N' A' B' hfun harg ihfun iharg =>
    exact STLCext.HasType.app ihfun iharg
  | ttrue =>
    apply STLCext.HasType.inl
    apply STLCext.HasType.unit
  | tfalse =>
    apply STLCext.HasType.inr
    apply STLCext.HasType.unit
  | @ite Γ' M' N₁ N₂ A' hcond hthen helse ihcond ihthen ihelse =>
    apply STLCext.HasType.case
    · exact ihcond
    · have ihthen' := (STLCext.typing_shift (B := STLCext.Ty.unit) ihthen)
      simp [eraseCtx] at ihthen'
      exact ihthen'
    · have ihelse' := (STLCext.typing_shift (B := STLCext.Ty.unit) ihelse)
      simp [eraseCtx] at ihelse'
      exact ihelse'


/-! ## Strong Normalization -/

/-- Strong normalization for boolean STLC via erasure. -/
theorem strong_normalization {Γ : Context} {M : Term} {A : Ty}
    (h : Γ ⊢ M : A) :
    STLCext.SN (erase M) :=
  STLCext.strong_normalization (erase_typing h)

end Metatheory.STLCextBool
