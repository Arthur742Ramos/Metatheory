/-
# Lambda Calculus as an Instance of Generic Rewriting

This module demonstrates how lambda calculus with parallel reduction
is an instance of the generic abstract rewriting system framework.

## Main Results

1. `ParRed` has the diamond property (in the generic sense)
2. Lambda's `MultiStep` is equivalent to `Rewriting.Star BetaStep`
3. Confluence follows from the generic `confluent_of_diamond` theorem

This shows that the generic framework correctly captures the lambda calculus case.
-/

import Metatheory.Lambda.Diamond
import Metatheory.Rewriting.Diamond
import Metatheory.Rewriting.Newman

namespace Metatheory.Lambda

open Term
open Rewriting (Diamond Confluent SemiConfluent Joinable Star)

/-! ## Parallel Reduction has Diamond Property

We show that `ParRed` satisfies the generic `Rewriting.Diamond` predicate.
-/

/-- Parallel reduction satisfies the generic diamond property -/
theorem parRed_diamond : Diamond ParRed := by
  intro M N₁ N₂ h1 h2
  -- Use the existing diamond theorem
  obtain ⟨P, hp1, hp2⟩ := diamond h1 h2
  exact ⟨P, hp1, hp2⟩

/-! ## Semi-Confluence and Confluence via Generic Framework

Using the generic framework's theorems, we can derive semi-confluence
and confluence for parallel reduction.
-/

/-- Semi-confluence of parallel reduction (via generic framework) -/
theorem parRed_semiConfluent : SemiConfluent ParRed :=
  Rewriting.semiConfluent_of_diamond parRed_diamond

/-- Confluence of parallel reduction (via generic framework) -/
theorem parRed_confluent : Confluent ParRed :=
  Rewriting.confluent_of_diamond parRed_diamond

/-! ## Relating MultiStep and Rewriting.Star

The lambda-specific `MultiStep` and the generic `Rewriting.Star BetaStep`
represent the same relation, just with different definitions.
-/

/-- Lambda MultiStep implies generic Star -/
theorem multiStep_to_star {M N : Term} (h : M →* N) : Star BetaStep M N := by
  induction h with
  | refl _ => exact Star.refl _
  | step hstep _ ih => exact Star.head hstep ih

/-- Generic Star implies lambda MultiStep -/
theorem star_to_multiStep {M N : Term} (h : Star BetaStep M N) : M →* N := by
  induction h with
  | refl => exact MultiStep.refl _
  | tail hab hbc ih =>
    -- hab : Star BetaStep M b, hbc : BetaStep b N
    -- ih : M →* b
    exact MultiStep.trans ih (MultiStep.single hbc)

/-- The two definitions are equivalent -/
theorem multiStep_iff_star {M N : Term} : (M →* N) ↔ Star BetaStep M N :=
  ⟨multiStep_to_star, star_to_multiStep⟩

/-! ## Generic Star for ParRed

We can also form the reflexive-transitive closure of parallel reduction.
-/

/-- ParRed multi-step implies lambda MultiStep -/
theorem parRedStar_to_multiStep {M N : Term} (h : Star ParRed M N) : M →* N := by
  induction h with
  | refl => exact MultiStep.refl _
  | tail _ hbc ih =>
    exact MultiStep.trans ih (ParRed.toMulti hbc)

/-- Lambda MultiStep implies ParRed multi-step -/
theorem multiStep_to_parRedStar {M N : Term} (h : M →* N) : Star ParRed M N := by
  induction h with
  | refl _ => exact Star.refl _
  | step hstep _ ih =>
    exact Star.head (ParRed.of_beta hstep) ih

/-- MultiStep and Star ParRed are equivalent -/
theorem multiStep_iff_parRedStar {M N : Term} : (M →* N) ↔ Star ParRed M N :=
  ⟨multiStep_to_parRedStar, parRedStar_to_multiStep⟩

/-! ## Alternative Church-Rosser via Generic Framework

This provides an alternative proof using the generic framework's confluent_of_diamond.
-/

/-- Parallel reduction is confluent (generic version) -/
theorem parRed_confluent_generic : ∀ M N₁ N₂,
    Star ParRed M N₁ → Star ParRed M N₂ →
    Joinable ParRed N₁ N₂ :=
  Rewriting.confluent_of_diamond parRed_diamond

/-- Church-Rosser via generic framework -/
theorem confluence_via_generic {M N₁ N₂ : Term}
    (h1 : M →* N₁) (h2 : M →* N₂) : ∃ P, (N₁ →* P) ∧ (N₂ →* P) := by
  -- Convert to Star ParRed
  have h1' := multiStep_to_parRedStar h1
  have h2' := multiStep_to_parRedStar h2
  -- Apply generic confluence
  obtain ⟨P, hp1, hp2⟩ := parRed_confluent_generic M N₁ N₂ h1' h2'
  -- Convert back to MultiStep
  exact ⟨P, parRedStar_to_multiStep hp1, parRedStar_to_multiStep hp2⟩

/-! ## Confluence of β-Reduction (generic `Star`) -/

/-- The one-step β-reduction relation is confluent, stated using the generic `Rewriting.Star`. -/
theorem betaStep_confluent : Confluent BetaStep := by
  intro M N₁ N₂ h1 h2
  have h1' : M →* N₁ := star_to_multiStep h1
  have h2' : M →* N₂ := star_to_multiStep h2
  obtain ⟨P, hp1, hp2⟩ := confluence_via_generic (M := M) (N₁ := N₁) (N₂ := N₂) h1' h2'
  exact ⟨P, multiStep_to_star hp1, multiStep_to_star hp2⟩

/-! ## Summary

This module demonstrates that:

1. **ParRed has diamond**: `parRed_diamond : Rewriting.Diamond ParRed`
2. **Generic framework applies**: `parRed_confluent : Rewriting.Confluent ParRed`
3. **Definitions align**: `multiStep_iff_star` shows equivalence

The lambda calculus proof structure (parallel reduction → diamond → confluence)
matches exactly the generic pattern provided by the Rewriting framework.

This validates the design of the generic framework: it correctly abstracts
the common structure while allowing specific instances like lambda calculus
to provide concrete implementations.
-/

end Metatheory.Lambda
