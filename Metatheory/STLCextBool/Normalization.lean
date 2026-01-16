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

/-! ## Erasure Lemmas -/

/-- Erasure commutes with shift (by 1). -/
theorem erase_shift1_at (c : Nat) (M : Term) :
    erase (Term.shift 1 c M) = STLCext.Term.shift 1 c (erase M) := by
  induction M generalizing c with
  | var n =>
    by_cases h : n < c
    · simp [Term.shift, STLCext.Term.shift, erase, h]
    · simp [Term.shift, STLCext.Term.shift, erase, h]
  | lam M ih =>
    simp [Term.shift, STLCext.Term.shift, erase, ih]
  | app M N ihM ihN =>
    simp [Term.shift, STLCext.Term.shift, erase, ihM, ihN]
  | ttrue =>
    simp [Term.shift, STLCext.Term.shift, erase]
  | tfalse =>
    simp [Term.shift, STLCext.Term.shift, erase]
  | ite M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp [Term.shift, STLCext.Term.shift, erase, ihM, ihN₁, ihN₂]
    have hcomm (T : STLCext.Term) :
        STLCext.Term.shift 1 0 (STLCext.Term.shift 1 c T) =
          STLCext.Term.shift 1 (c + 1) (STLCext.Term.shift 1 0 T) := by
      simpa using
        (STLCext.Term.shift_shift_comm 1 1 0 c T (Nat.zero_le c))
    simp [STLCext.Term.shift1, hcomm]

/-- Erasure commutes with shift1. -/
theorem erase_shift1 (M : Term) :
    erase (Term.shift1 M) = STLCext.Term.shift1 (erase M) := by
  simpa [Term.shift1, STLCext.Term.shift1] using erase_shift1_at 0 M

/-- Erasure commutes with substitution. -/
theorem erase_subst (j : Nat) (N M : Term) :
    erase (Term.subst j N M) = STLCext.Term.subst j (erase N) (erase M) := by
  induction M generalizing j N with
  | var n =>
    by_cases hEq : n = j
    · simp [Term.subst, STLCext.Term.subst, erase, hEq]
    · by_cases hGt : n > j
      · simp [Term.subst, STLCext.Term.subst, erase, hEq, hGt]
      · simp [Term.subst, STLCext.Term.subst, erase, hEq, hGt]
  | lam M ih =>
    simp [Term.subst, STLCext.Term.subst, erase, ih, erase_shift1_at]
  | app M N ihM ihN =>
    simp [Term.subst, STLCext.Term.subst, erase, ihM, ihN]
  | ttrue =>
    simp [Term.subst, STLCext.Term.subst, erase]
  | tfalse =>
    simp [Term.subst, STLCext.Term.subst, erase]
  | ite M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp [Term.subst, STLCext.Term.subst, erase, ihM, ihN₁, ihN₂]
    have hshift_N₁ :
        STLCext.Term.shift1 (STLCext.Term.subst j (erase N) (erase N₁)) =
          STLCext.Term.subst (j + 1) (STLCext.Term.shift1 (erase N))
            (STLCext.Term.shift1 (erase N₁)) := by
      simpa [STLCext.Term.shift1] using
        (STLCext.Term.shift1_subst (erase N₁) (erase N) j)
    have hshift_N₂ :
        STLCext.Term.shift1 (STLCext.Term.subst j (erase N) (erase N₂)) =
          STLCext.Term.subst (j + 1) (STLCext.Term.shift1 (erase N))
            (STLCext.Term.shift1 (erase N₂)) := by
      simpa [STLCext.Term.shift1] using
        (STLCext.Term.shift1_subst (erase N₂) (erase N) j)
    simp [hshift_N₁, hshift_N₂]

/-- Erasure commutes with substitution at 0. -/
theorem erase_subst0 (N M : Term) :
    erase (Term.subst0 N M) = STLCext.Term.subst0 (erase N) (erase M) := by
  simpa [Term.subst0, STLCext.Term.subst0] using erase_subst 0 N M

/-- Erasure preserves values. -/
theorem erase_value {M : Term} (hval : STLCextBool.IsValue M) :
    STLCext.IsValue (erase M) := by
  cases M <;> simp [STLCextBool.IsValue, STLCext.IsValue, erase] at hval ⊢

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

/-- Erasure preserves progress for closed terms. -/
theorem erase_progress {M : Term} {A : Ty} (h : ([] : Context) ⊢ M : A) :
    STLCext.IsValue (erase M) ∨ ∃ N, STLCext.Step (erase M) N := by
  have h' := erase_typing (Γ := []) h
  simpa [eraseCtx] using (STLCext.progress h')


/-! ## Strong Normalization -/

/-- Strong normalization for boolean STLC via erasure. -/
theorem strong_normalization {Γ : Context} {M : Term} {A : Ty}
    (h : Γ ⊢ M : A) :
    STLCext.SN (erase M) :=
  STLCext.strong_normalization (erase_typing h)

end Metatheory.STLCextBool
