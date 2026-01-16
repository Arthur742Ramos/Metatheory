import Metatheory.STLCextBool.Parallel

/-!
# Complete Development for STLC with Booleans

Complete development reduces all redexes in a term and is used to
prove the diamond property for parallel reduction.
-/

namespace Metatheory.STLCextBool

open Term

/-! ## Complete Development -/

/-- Complete development: reduce all redexes in a term. -/
def complete : Term → Term
  | var n => var n
  | lam M => lam (complete M)
  | app (lam M) N => (complete M)[complete N]
  | app M N => app (complete M) (complete N)
  | ttrue => ttrue
  | tfalse => tfalse
  | Term.ite Term.ttrue N₁ _ => complete N₁
  | Term.ite Term.tfalse _ N₂ => complete N₂
  | Term.ite M N₁ N₂ => ite (complete M) (complete N₁) (complete N₂)

/-! ## Basic Properties -/

@[simp] theorem complete_var (n : Nat) : complete (var n) = var n := rfl
@[simp] theorem complete_lam (M : Term) : complete (lam M) = lam (complete M) := rfl
@[simp] theorem complete_beta (M N : Term) : complete (app (lam M) N) = (complete M)[complete N] := rfl
@[simp] theorem complete_ite_true (N₁ N₂ : Term) : complete (Term.ite ttrue N₁ N₂) = complete N₁ := rfl
@[simp] theorem complete_ite_false (N₁ N₂ : Term) : complete (Term.ite tfalse N₁ N₂) = complete N₂ := rfl

/-! ## Inversion -/

/-- Inversion for parallel reduction under lambda. -/
theorem par_lam_inv {M M' : Term} (h : lam M ⇒ lam M') : M ⇒ M' := by
  cases h with
  | lam h' => exact h'

/-! ## Key Lemma -/

/-- If M ⇒ N, then N ⇒ complete M. -/
theorem par_complete {M N : Term} (h : M ⇒ N) : N ⇒ complete M := by
  induction h with
  | var n =>
    simpa [complete] using (ParRed.refl (Term.var n))
  | lam hM ih =>
    simpa [complete] using (ParRed.lam ih)
  | app hM hN ihM ihN =>
    cases hM with
    | var n =>
      simp [complete]
      exact ParRed.app ihM ihN
    | app _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | lam hBody =>
      simp [complete]
      have ihM' := par_lam_inv (by simpa [complete] using ihM)
      exact ParRed.beta ihM' ihN
    | beta _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | ttrue =>
      simp [complete]
      exact ParRed.app ihM ihN
    | tfalse =>
      simp [complete]
      exact ParRed.app ihM ihN
    | ite _ _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | iteTrue _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
    | iteFalse _ _ =>
      simp [complete]
      exact ParRed.app ihM ihN
  | ttrue =>
    simpa [complete] using ParRed.ttrue
  | tfalse =>
    simpa [complete] using ParRed.tfalse
  | ite hM hN₁ hN₂ ihM ihN₁ ihN₂ =>
    cases hM with
    | ttrue =>
      simp [complete]
      exact ParRed.iteTrue ihN₁ ihN₂
    | tfalse =>
      simp [complete]
      exact ParRed.iteFalse ihN₁ ihN₂
    | var n =>
      simp [complete]
      exact ParRed.ite ihM ihN₁ ihN₂
    | lam _ =>
      simp [complete]
      exact ParRed.ite ihM ihN₁ ihN₂
    | app _ _ =>
      simp [complete]
      exact ParRed.ite ihM ihN₁ ihN₂
    | ite _ _ _ =>
      simp [complete]
      exact ParRed.ite ihM ihN₁ ihN₂
    | beta _ _ =>
      simp [complete]
      exact ParRed.ite ihM ihN₁ ihN₂
    | iteTrue _ _ =>
      simp [complete]
      exact ParRed.ite ihM ihN₁ ihN₂
    | iteFalse _ _ =>
      simp [complete]
      exact ParRed.ite ihM ihN₁ ihN₂
  | beta hM hN ihM ihN =>
    simp [complete]
    exact ParRed.subst ihM ihN
  | iteTrue hN₁ hN₂ ihN₁ ihN₂ =>
    simp [complete]
    exact ihN₁
  | iteFalse hN₁ hN₂ ihN₁ ihN₂ =>
    simp [complete]
    exact ihN₂

/-! ## Diamond Property -/

/-- Parallel reduction satisfies the diamond property. -/
theorem diamond {M N₁ N₂ : Term} (h1 : M ⇒ N₁) (h2 : M ⇒ N₂) :
    ∃ P, (N₁ ⇒ P) ∧ (N₂ ⇒ P) :=
  ⟨complete M, par_complete h1, par_complete h2⟩

end Metatheory.STLCextBool
