import Metatheory.STLCextBool.Typing
import Metatheory.Rewriting.Basic

/-!
# Call-by-Value Reduction for STLC with Booleans

Defines CBV reduction and proves determinism (hence confluence).
-/

namespace Metatheory.STLCextBool

open Term

/-! ## Call-by-Value Reduction -/

/-- Single-step call-by-value reduction. -/
inductive CBVStep : Term → Term → Prop where
  | beta : ∀ M V, IsValue V → CBVStep (app (lam M) V) (M[V])
  | appL : ∀ {M M' N}, CBVStep M M' → CBVStep (app M N) (app M' N)
  | appR : ∀ {V N N'}, IsValue V → CBVStep N N' → CBVStep (app V N) (app V N')
  | iteTrue : ∀ N₁ N₂, CBVStep (ite ttrue N₁ N₂) N₁
  | iteFalse : ∀ N₁ N₂, CBVStep (ite tfalse N₁ N₂) N₂
  | iteC : ∀ {M M' N₁ N₂}, CBVStep M M' → CBVStep (ite M N₁ N₂) (ite M' N₁ N₂)

/-- Notation for CBV reduction. -/
scoped infix:50 " →cbv " => CBVStep

namespace CBVStep

/-! ## Basic Properties -/

/-- Values do not step in CBV. -/
theorem value_no_step {V N : Term} (hV : IsValue V) : ¬(V →cbv N) := by
  intro h
  cases V with
  | var n => cases hV
  | app _ _ => cases hV
  | ite _ _ _ => cases hV
  | lam _ => cases h
  | ttrue => cases h
  | tfalse => cases h

/-- CBV is deterministic. -/
theorem deterministic {M N₁ N₂ : Term} (h1 : M →cbv N₁) (h2 : M →cbv N₂) : N₁ = N₂ := by
  induction h1 generalizing N₂ with
  | beta M V hV =>
    cases h2 with
    | beta M' V' hV' => rfl
    | appL h => cases h
    | appR hV' h => exact (value_no_step hV h).elim
  | appL hM ih =>
    cases h2 with
    | beta M' V' hV' => cases hM
    | appL hM' =>
      have h := ih hM'
      cases h
      rfl
    | appR hV' hN' => exact (value_no_step hV' hM).elim
  | appR hV hN ih =>
    cases h2 with
    | beta M' V' hV' => exact (value_no_step hV' hN).elim
    | appL hM' => exact (value_no_step hV hM').elim
    | appR hV' hN' =>
      have h := ih hN'
      cases h
      rfl
  | iteTrue N₁ N₂ =>
    cases h2 with
    | iteTrue _ _ => rfl
    | iteC h => cases h
  | iteFalse N₁ N₂ =>
    cases h2 with
    | iteFalse _ _ => rfl
    | iteC h => cases h
  | iteC hM ih =>
    cases h2 with
    | iteTrue _ _ => cases hM
    | iteFalse _ _ => cases hM
    | iteC hM' =>
      have h := ih hM'
      cases h
      rfl

end CBVStep

/-! ## Confluence via Determinism -/

/-- CBV reduction is deterministic. -/
theorem cbv_deterministic : Rewriting.Deterministic CBVStep := by
  intro M N₁ N₂ h1 h2
  exact CBVStep.deterministic h1 h2

/-- CBV reduction is confluent, since it is deterministic. -/
theorem cbv_confluent : Rewriting.Confluent CBVStep :=
  Rewriting.confluent_of_deterministic cbv_deterministic

end Metatheory.STLCextBool
