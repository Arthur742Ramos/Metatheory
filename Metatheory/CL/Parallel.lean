/-
# Combinatory Logic - Parallel Reduction

This module defines parallel reduction for CL, which is the key
to proving the diamond property and hence confluence.

## Strategy

Parallel reduction allows multiple redexes to be contracted simultaneously.
It has the diamond property, which implies confluence of weak reduction.

## References

- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
- Hindley, "Church-Rosser for Combinatory Weak Reduction" (1974)
-/

import Metatheory.CL.Reduction

namespace Metatheory.CL

open Term

/-! ## Parallel Reduction -/

/-- Parallel reduction: reduce zero or more redexes simultaneously.

    The key insight is that parallel reduction has the diamond property,
    even though weak reduction does not. -/
inductive ParRed : Term → Term → Prop where
  | s_refl : ParRed S S
  | k_refl : ParRed K K
  | app : ParRed M M' → ParRed N N' → ParRed (M ⬝ N) (M' ⬝ N')
  | k_red : ParRed M M' → ParRed N N' → ParRed (K ⬝ M ⬝ N) M'
  | s_red : ParRed M M' → ParRed N N' → ParRed P P' →
            ParRed (S ⬝ M ⬝ N ⬝ P) ((M' ⬝ P') ⬝ (N' ⬝ P'))

/-- Notation for parallel reduction -/
scoped infix:50 " ⇒ " => ParRed

namespace ParRed

/-! ## Basic Properties -/

/-- Parallel reduction is reflexive -/
theorem refl (M : Term) : M ⇒ M := by
  induction M with
  | S => exact s_refl
  | K => exact k_refl
  | app M N ihM ihN => exact app ihM ihN

/-- Single-step reduction implies parallel reduction -/
theorem of_step {M N : Term} (h : M ⟶ N) : M ⇒ N := by
  induction h with
  | k_red M N => exact k_red (refl M) (refl N)
  | s_red M N P => exact s_red (refl M) (refl N) (refl P)
  | appL _ ih => exact app ih (refl _)
  | appR _ ih => exact app (refl _) ih

/-- Parallel reduction implies multi-step reduction -/
theorem to_multi {M N : Term} (h : M ⇒ N) : M ⟶* N := by
  induction h with
  | s_refl => exact MultiStep.refl S
  | k_refl => exact MultiStep.refl K
  | app _ _ ihM ihN => exact MultiStep.app ihM ihN
  | k_red hM hN ihM ihN =>
    -- K ⬝ M ⬝ N →* K ⬝ M' ⬝ N' →* M'
    apply MultiStep.trans
    · apply MultiStep.trans
      · exact MultiStep.appL (MultiStep.appL (MultiStep.refl K))
      · exact MultiStep.appL (MultiStep.appR ihM)
    · apply MultiStep.trans
      · exact MultiStep.appR ihN
      · exact MultiStep.single (WeakStep.k_red _ _)
  | s_red hM hN hP ihM ihN ihP =>
    -- S ⬝ M ⬝ N ⬝ P →* S ⬝ M' ⬝ N' ⬝ P' →* (M' ⬝ P') ⬝ (N' ⬝ P')
    apply MultiStep.trans
    · apply MultiStep.trans
      · apply MultiStep.trans
        · exact MultiStep.appL (MultiStep.appL (MultiStep.appL (MultiStep.refl S)))
        · exact MultiStep.appL (MultiStep.appL (MultiStep.appR ihM))
      · exact MultiStep.appL (MultiStep.appR ihN)
    · apply MultiStep.trans
      · exact MultiStep.appR ihP
      · exact MultiStep.single (WeakStep.s_red _ _ _)

/-! ## Inversion Lemmas -/

/-- Inversion for K ⬝ M: if K ⬝ M ⇒ N, then N = K ⬝ M' for some M' with M ⇒ M' -/
theorem app_K_inv {M N : Term} (h : K ⬝ M ⇒ N) : ∃ M', N = K ⬝ M' ∧ M ⇒ M' := by
  cases h with
  | app hK hM =>
    cases hK
    exact ⟨_, rfl, hM⟩

/-- Inversion for S ⬝ M: if S ⬝ M ⇒ N, then N = S ⬝ M' for some M' with M ⇒ M' -/
theorem app_S_inv {M N : Term} (h : S ⬝ M ⇒ N) : ∃ M', N = S ⬝ M' ∧ M ⇒ M' := by
  cases h with
  | app hS hM =>
    cases hS
    exact ⟨_, rfl, hM⟩

/-- Inversion for S ⬝ M ⬝ N -/
theorem app_SM_inv {M N P : Term} (h : S ⬝ M ⬝ N ⇒ P) :
    ∃ M' N', P = S ⬝ M' ⬝ N' ∧ M ⇒ M' ∧ N ⇒ N' := by
  cases h with
  | app hSM hN =>
    obtain ⟨M', rfl, hM⟩ := app_S_inv hSM
    exact ⟨M', _, rfl, hM, hN⟩

/-- Inversion for K ⬝ M ⬝ N: either reduces via app or via k_red -/
theorem app_KM_inv {M N P : Term} (h : K ⬝ M ⬝ N ⇒ P) :
    (∃ M' N', P = K ⬝ M' ⬝ N' ∧ M ⇒ M' ∧ N ⇒ N') ∨
    (∃ M', P = M' ∧ M ⇒ M') := by
  cases h with
  | app hKM hN =>
    obtain ⟨M', rfl, hM⟩ := app_K_inv hKM
    left
    exact ⟨M', _, rfl, hM, hN⟩
  | k_red hM hN =>
    right
    exact ⟨_, rfl, hM⟩

end ParRed

end Metatheory.CL
