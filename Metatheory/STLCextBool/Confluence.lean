import Metatheory.STLCextBool.Complete
import Metatheory.Rewriting.Diamond
import Metatheory.STLCextBool.Normalization
import Metatheory.STLCextBool.CBV

/-!
# Church-Rosser Theorem for STLC with Booleans

Confluence is proved via parallel reduction and the diamond property.
-/

namespace Metatheory.STLCextBool

open Term
open Rewriting (Diamond Confluent Star)

/-! ## Parallel Reduction has Diamond -/

/-- Parallel reduction satisfies the diamond property. -/
theorem parRed_diamond : Diamond ParRed := by
  intro M N₁ N₂ h1 h2
  obtain ⟨P, hp1, hp2⟩ := diamond h1 h2
  exact ⟨P, hp1, hp2⟩

/-- Parallel reduction is confluent (generic framework). -/
theorem parRed_confluent : Confluent ParRed :=
  Rewriting.confluent_of_diamond parRed_diamond

/-! ## Relating MultiStep and Star -/

/-- MultiStep implies generic Star. -/
theorem multiStep_to_star {M N : Term} (h : M ⟶* N) : Star Step M N := by
  induction h with
  | refl _ => exact Star.refl _
  | step hstep _ ih => exact Star.trans (Star.single hstep) ih

/-- Generic Star implies MultiStep. -/
theorem star_to_multiStep {M N : Term} (h : Star Step M N) : M ⟶* N := by
  induction h with
  | refl => exact MultiStep.refl _
  | tail hab hbc ih =>
    exact MultiStep.trans ih (MultiStep.single hbc)

/-- The two definitions are equivalent. -/
theorem multiStep_iff_star {M N : Term} : (M ⟶* N) ↔ Star Step M N :=
  ⟨multiStep_to_star, star_to_multiStep⟩

/-! ## Confluence for STLCextBool -/

/-- Parallel reduction implies multi-step reduction. -/
theorem parRedStar_to_multiStep {M N : Term} (h : Star ParRed M N) : M ⟶* N := by
  induction h with
  | refl => exact MultiStep.refl _
  | tail hab hbc ih =>
    exact MultiStep.trans ih (ParRed.toMulti hbc)

/-- Multi-step implies parallel reduction star. -/
theorem multiStep_to_parRedStar {M N : Term} (h : M ⟶* N) : Star ParRed M N := by
  induction h with
  | refl _ => exact Star.refl _
  | step hstep _ ih =>
    exact Star.trans (Star.single (ParRed.of_step hstep)) ih

/-- Confluence of single-step reduction (generic `Star`). -/
theorem step_confluent : Confluent Step := by
  intro M N₁ N₂ h1 h2
  have h1' := multiStep_to_parRedStar (star_to_multiStep h1)
  have h2' := multiStep_to_parRedStar (star_to_multiStep h2)
  obtain ⟨P, hp1, hp2⟩ := parRed_confluent M N₁ N₂ h1' h2'
  exact ⟨P, multiStep_to_star (parRedStar_to_multiStep hp1),
    multiStep_to_star (parRedStar_to_multiStep hp2)⟩

/-- Church-Rosser (multi-step) form of confluence. -/
theorem confluence {M N₁ N₂ : Term} (h1 : M ⟶* N₁) (h2 : M ⟶* N₂) :
    ∃ P, (N₁ ⟶* P) ∧ (N₂ ⟶* P) := by
  have h1' : Star Step M N₁ := multiStep_to_star h1
  have h2' : Star Step M N₂ := multiStep_to_star h2
  obtain ⟨P, hp1, hp2⟩ := step_confluent M N₁ N₂ h1' h2'
  exact ⟨P, star_to_multiStep hp1, star_to_multiStep hp2⟩

/-- Church-Rosser synonym. -/
theorem church_rosser {M N₁ N₂ : Term} (h1 : M ⟶* N₁) (h2 : M ⟶* N₂) :
    ∃ P, (N₁ ⟶* P) ∧ (N₂ ⟶* P) :=
  confluence h1 h2

/-! ## Unique Normal Forms (Step) -/

theorem existsUnique_normalForm_of_hasType {Γ : Context} {M : Term} {A : Ty} (h : Γ ⊢ M : A) :
    ∃ n, Rewriting.Star Step M n ∧ Rewriting.IsNormalForm Step n ∧
      ∀ n', (Rewriting.Star Step M n' ∧ Rewriting.IsNormalForm Step n') → n' = n :=
  Rewriting.existsUnique_normalForm_of_confluent_hasNormalForm step_confluent
    (hasNormalForm_of_hasType h)

theorem existsUnique_normalForm_closed {M : Term} {A : Ty} (h : ([] : Context) ⊢ M : A) :
    ∃ n, Rewriting.Star Step M n ∧ Rewriting.IsNormalForm Step n ∧
      ∀ n', (Rewriting.Star Step M n' ∧ Rewriting.IsNormalForm Step n') → n' = n :=
  existsUnique_normalForm_of_hasType h

/-! ## CBV Normal Forms -/

theorem cbv_hasNormalForm_of_hasType {Γ : Context} {M : Term} {A : Ty} (h : Γ ⊢ M : A) :
    Rewriting.HasNormalForm CBVStep M :=
  cbv_hasNormalForm h

end Metatheory.STLCextBool
