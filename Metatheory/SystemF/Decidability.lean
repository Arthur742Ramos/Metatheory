/-
# Decidability of Type Checking for System F

This module proves that type checking is decidable for Church-style System F.
Because lambdas carry explicit type annotations and type abstractions are
syntactically marked, we can implement a complete type-checking algorithm as
a total function `typeCheck` and show it is both sound and complete with
respect to the `HasType` relation.

## Main Results

- `typeCheck`: algorithmic type checker returning `Option Ty`
- `typeCheck_sound`: `typeCheck` agrees with `HasType` (soundness)
- `typeCheck_complete`: `HasType` implies `typeCheck` succeeds (completeness)
- `Decidable (HasType k Γ M τ)`: decidability instance
- `type_unique`: referenced from `Typing.lean`

## References

- Pierce, "Types and Programming Languages" (2002), Chapter 23
- Wells, "Typability and type checking in System F are equivalent and
  undecidable" (1999) — for *type inference*; type *checking* with
  Church-style annotations is decidable.
-/

import Metatheory.SystemF.Typing

namespace Metatheory.SystemF

open Ty Term

/-! ## Decidable Well-Formedness of Types -/

/-- Boolean check for well-formedness of types. -/
def Ty.checkWF (n : Nat) : Ty → Bool
  | tvar k => decide (k < n)
  | arr τ₁ τ₂ => checkWF n τ₁ && checkWF n τ₂
  | all τ => checkWF (n + 1) τ

theorem Ty.checkWF_iff {n : Nat} {τ : Ty} : Ty.checkWF n τ = true ↔ Ty.WF n τ := by
  induction τ generalizing n with
  | tvar k =>
    simp [checkWF, WF]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp [checkWF, WF, ih₁, ih₂, Bool.and_eq_true]
  | all τ ih =>
    simpa [checkWF, WF] using ih

/-- Well-formedness of types is decidable. -/
instance decWF (n : Nat) (τ : Ty) : Decidable (Ty.WF n τ) :=
  if h : Ty.checkWF n τ then
    isTrue (Ty.checkWF_iff.mp h)
  else
    isFalse (fun hwf => h (Ty.checkWF_iff.mpr hwf))

/-! ## Type Checking Algorithm -/

/-- Algorithmic type checker for Church-style System F.

    Given a type-variable depth `k`, a context `Γ`, and a term `M`,
    returns `some τ` when `M` has type `τ`, or `none` when `M` is
    ill-typed. -/
def typeCheck (k : TyVarCount) (Γ : Context) : Term → Option Ty
  | var n => lookup Γ n
  | lam τ₁ M =>
    if Ty.checkWF k τ₁ then
      match typeCheck k (τ₁ :: Γ) M with
      | some τ₂ => some (arr τ₁ τ₂)
      | none => none
    else none
  | app M N =>
    match typeCheck k Γ M with
    | some (arr τ₁ τ₂) =>
      match typeCheck k Γ N with
      | some σ => if σ == τ₁ then some τ₂ else none
      | none => none
    | _ => none
  | tlam M =>
    match typeCheck (k + 1) (shiftContext Γ) M with
    | some τ => some (all τ)
    | none => none
  | tapp M σ =>
    if Ty.checkWF k σ then
      match typeCheck k Γ M with
      | some (all τ) => some (substTy0 σ τ)
      | _ => none
    else none

/-! ## Soundness

If `typeCheck` returns a type, then `HasType` holds. -/

theorem typeCheck_sound {k : TyVarCount} {Γ : Context} {M : Term} {τ : Ty}
    (h : typeCheck k Γ M = some τ) : HasType k Γ M τ := by
  induction M generalizing k Γ τ with
  | var n =>
    simp only [typeCheck] at h
    exact HasType.var h
  | lam τ₁ M ih =>
    simp only [typeCheck] at h
    split at h
    · rename_i hwf
      match heq : typeCheck k (τ₁ :: Γ) M with
      | some τ₂ =>
        rw [heq] at h
        simp at h
        rw [← h]
        exact HasType.lam (Ty.checkWF_iff.mp hwf) (ih heq)
      | none =>
        rw [heq] at h
        exact absurd h (by simp)
    · exact absurd h (by simp)
  | app M N ihM ihN =>
    simp only [typeCheck] at h
    match heqM : typeCheck k Γ M with
    | some (arr τ₁ τ₂) =>
      rw [heqM] at h
      match heqN : typeCheck k Γ N with
      | some σ =>
        rw [heqN] at h
        simp only [beq_iff_eq] at h
        split at h
        · rename_i heq
          simp at h
          subst heq
          rw [← h]
          exact HasType.app (ihM heqM) (ihN heqN)
        · exact absurd h (by simp)
      | none =>
        rw [heqN] at h
        exact absurd h (by simp)
    | some (tvar _) =>
      rw [heqM] at h
      exact absurd h (by simp)
    | some (all _) =>
      rw [heqM] at h
      exact absurd h (by simp)
    | none =>
      rw [heqM] at h
      exact absurd h (by simp)
  | tlam M ih =>
    simp only [typeCheck] at h
    match heq : typeCheck (k + 1) (shiftContext Γ) M with
    | some τ' =>
      rw [heq] at h
      simp at h
      rw [← h]
      exact HasType.tlam (ih heq)
    | none =>
      rw [heq] at h
      exact absurd h (by simp)
  | tapp M σ ih =>
    simp only [typeCheck] at h
    split at h
    · rename_i hwf
      match heq : typeCheck k Γ M with
      | some (all τ') =>
        rw [heq] at h
        simp at h
        rw [← h]
        exact HasType.tapp (ih heq) (Ty.checkWF_iff.mp hwf)
      | some (tvar _) =>
        rw [heq] at h
        exact absurd h (by simp)
      | some (arr _ _) =>
        rw [heq] at h
        exact absurd h (by simp)
      | none =>
        rw [heq] at h
        exact absurd h (by simp)
    · exact absurd h (by simp)

/-! ## Completeness

If `HasType` holds, then `typeCheck` returns the same type. -/

theorem typeCheck_complete {k : TyVarCount} {Γ : Context} {M : Term} {τ : Ty}
    (h : HasType k Γ M τ) : typeCheck k Γ M = some τ := by
  induction h with
  | var hlook =>
    simp only [typeCheck]
    exact hlook
  | lam hwf _ ih =>
    simp only [typeCheck, Ty.checkWF_iff.mpr hwf, ite_true, ih]
  | app _ _ ihM ihN =>
    simp only [typeCheck, ihM, ihN, beq_self_eq_true, ite_true]
  | tlam _ ih =>
    simp only [typeCheck, ih]
  | tapp _ hwf ih =>
    simp only [typeCheck, Ty.checkWF_iff.mpr hwf, ite_true, ih]

/-! ## Decidability of HasType -/

/-- Type checking is decidable for Church-style System F. -/
noncomputable instance hasType_decidable (k : TyVarCount) (Γ : Context) (M : Term) (τ : Ty) :
    Decidable (HasType k Γ M τ) :=
  match h : typeCheck k Γ M with
  | some τ' =>
    if heq : τ' = τ then
      isTrue (heq ▸ typeCheck_sound h)
    else
      isFalse fun hty => by
        have hc := typeCheck_complete hty
        rw [hc] at h
        exact heq (Option.some.inj h.symm)
  | none =>
    isFalse fun hty => by
      have hc := typeCheck_complete hty
      rw [hc] at h
      exact Option.noConfusion h

/-! ## Corollaries -/

/-- Boolean check for whether a term is well-typed. -/
def isWellTyped (k : TyVarCount) (Γ : Context) (M : Term) : Bool :=
  (typeCheck k Γ M).isSome

/-- `isWellTyped` is true iff the term has some type. -/
theorem isWellTyped_iff {k : TyVarCount} {Γ : Context} {M : Term} :
    isWellTyped k Γ M = true ↔ ∃ τ, HasType k Γ M τ := by
  simp only [isWellTyped, Option.isSome_iff_exists]
  constructor
  · rintro ⟨τ, h⟩
    exact ⟨τ, typeCheck_sound h⟩
  · rintro ⟨τ, h⟩
    exact ⟨τ, typeCheck_complete h⟩

/-- `isWellTyped` is false iff the term has no type. -/
theorem not_isWellTyped_iff {k : TyVarCount} {Γ : Context} {M : Term} :
    isWellTyped k Γ M = false ↔ ∀ τ, ¬HasType k Γ M τ := by
  constructor
  · intro hf τ hty
    have := isWellTyped_iff.mpr ⟨τ, hty⟩
    rw [hf] at this
    exact Bool.noConfusion this
  · intro hall
    match hc : isWellTyped k Γ M with
    | true =>
      obtain ⟨τ, hty⟩ := isWellTyped_iff.mp hc
      exact absurd hty (hall τ)
    | false => rfl

/-- Decidability of "is there a type for M?". -/
noncomputable instance wellTyped_decidable (k : TyVarCount) (Γ : Context) (M : Term) :
    Decidable (∃ τ, HasType k Γ M τ) :=
  match h : typeCheck k Γ M with
  | some τ => isTrue ⟨τ, typeCheck_sound h⟩
  | none =>
    isFalse fun ⟨τ, hty⟩ => by
      have hc := typeCheck_complete hty
      rw [hc] at h
      exact Option.noConfusion h

/-- Type uniqueness (re-exported from Typing for convenience). -/
theorem type_unique' {k : TyVarCount} {Γ : Context} {M : Term} {τ₁ τ₂ : Ty}
    (h1 : HasType k Γ M τ₁) (h2 : HasType k Γ M τ₂) : τ₁ = τ₂ :=
  type_unique h1 h2

/-- `typeCheck` computes exactly the unique type, when it exists. -/
theorem typeCheck_eq_iff {k : TyVarCount} {Γ : Context} {M : Term} {τ : Ty} :
    typeCheck k Γ M = some τ ↔ HasType k Γ M τ :=
  ⟨typeCheck_sound, typeCheck_complete⟩

/-- When a term is well-typed, `typeCheck` returns the unique type. -/
theorem typeCheck_unique {k : TyVarCount} {Γ : Context} {M : Term} {τ : Ty}
    (h : HasType k Γ M τ) : typeCheck k Γ M = some τ :=
  typeCheck_complete h

end Metatheory.SystemF
