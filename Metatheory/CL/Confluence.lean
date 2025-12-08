/-
# Combinatory Logic - Confluence

This module proves confluence (Church-Rosser) for Combinatory Logic
using the generic rewriting framework.

## Strategy

We use the Takahashi method:
1. Define "complete development" that contracts all redexes
2. Show parallel reduction reaches complete development
3. Derive diamond property for parallel reduction
4. Use generic `confluent_of_diamond` theorem

## References

- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
- Hindley, "Church-Rosser for Combinatory Weak Reduction" (1974)
-/

import Metatheory.CL.Parallel
import Metatheory.Rewriting.Diamond

namespace Metatheory.CL

open Term ParRed

/-! ## Complete Development -/

/-- Complete development: contract ALL redexes in one step.

    This gives the "most reduced" form reachable in one parallel step.
    The key property is that any parallel reduction reaches the
    complete development. -/
def complete : Term → Term
  | S => S
  | K => K
  | Term.app (Term.app K M) _ => complete M
  | Term.app (Term.app (Term.app S M) N) P => (complete M ⬝ complete P) ⬝ (complete N ⬝ complete P)
  | Term.app M N => Term.app (complete M) (complete N)

/-! ## Key Lemmas -/

/-- Every parallel reduction reaches the complete development.

    This is the key lemma for proving the diamond property.
    The proof is by induction on the parallel reduction, showing
    that N ⇒ complete M whenever M ⇒ N.

    The proof involves careful case analysis on the term structure
    to match how `complete` unfolds.

    Standard reference: Takahashi (1995), Lemma 3.2
    See also: Hindley (1974), "Church-Rosser for Combinatory Weak Reduction" -/
theorem parRed_complete {M N : Term} (h : M ⇒ N) : N ⇒ complete M := by
  induction h with
  | s_refl =>
    exact s_refl
  | k_refl =>
    exact k_refl
  | @app M₁ N₁ M' N' hM hN ihM ihN =>
    -- M₁ ⬝ N₁ ⇒ M' ⬝ N', need: M' ⬝ N' ⇒ complete (M₁ ⬝ N₁)
    -- ihM : M' ⇒ complete M₁
    -- ihN : N' ⇒ complete N₁
    -- Case on the structure of M₁ to determine complete (M₁ ⬝ N₁)
    match M₁ with
    | S =>
      cases hM
      simp [complete]
      exact app s_refl ihN
    | K =>
      cases hM
      simp [complete]
      exact app k_refl ihN
    | Term.app (Term.app K M₁₁) M₁₂ =>
      -- M₁ = (K ⬝ M₁₁) ⬝ M₁₂, so M₁ ⬝ N₁ = ((K ⬝ M₁₁) ⬝ M₁₂) ⬝ N₁
      -- complete (((K ⬝ M₁₁) ⬝ M₁₂) ⬝ N₁) = complete M₁₁
      rcases app_KM_inv hM with ⟨M₁₁', M₁₂', rfl, _, _⟩ | ⟨M₁₁', rfl, _⟩
      · -- M' = (K ⬝ M₁₁') ⬝ M₁₂' (no contraction at K level)
        -- ihM : ((K ⬝ M₁₁') ⬝ M₁₂') ⇒ complete ((K ⬝ M₁₁) ⬝ M₁₂)
        -- complete ((K ⬝ M₁₁) ⬝ M₁₂) = complete M₁₁
        -- So ihM : ((K ⬝ M₁₁') ⬝ M₁₂') ⇒ complete M₁₁
        -- Need: ((K ⬝ M₁₁') ⬝ M₁₂') ⬝ N' ⇒ complete M₁₁
        -- Use k_red: (K ⬝ M ⬝ N) ⇒ M' if M ⇒ M'
        -- Here (K ⬝ (M₁₁') ⬝ (M₁₂')) ⬝ N' with (M₁₁') = first arg to K
        -- Wait, that's not right. Let me reconsider.
        -- ((K ⬝ M₁₁') ⬝ M₁₂') ⬝ N' has the structure (app (app K M₁₁') M₁₂') ⬝ N'
        -- This matches the K-redex pattern: app (app K M₁₁') _ where _ = M₁₂' ⬝ N'
        -- So ((K ⬝ M₁₁') ⬝ (M₁₂' ⬝ N')) reduces to M₁₁'
        -- But our term is ((K ⬝ M₁₁') ⬝ M₁₂') ⬝ N', not (K ⬝ M₁₁') ⬝ (M₁₂' ⬝ N')
        -- Due to left-associativity, ((K ⬝ M₁₁') ⬝ M₁₂') ⬝ N' = (app (app (app K M₁₁') M₁₂') N')
        -- The K-redex pattern is app (app K M) _ which would be (K ⬝ M₁₁') ⬝ anything
        -- So ((K ⬝ M₁₁') ⬝ M₁₂') matches with M = M₁₁', _ = M₁₂'
        -- Therefore ((K ⬝ M₁₁') ⬝ M₁₂') contracts to M₁₁' via k_red
        -- Then ((K ⬝ M₁₁') ⬝ M₁₂') ⬝ N' contracts to M₁₁' ⬝ N' via app congruence
        -- But I have ihM saying ((K ⬝ M₁₁') ⬝ M₁₂') ⇒ complete M₁₁
        -- So I can use app to get ((K ⬝ M₁₁') ⬝ M₁₂') ⬝ N' ⇒ complete M₁₁ ⬝ N'
        -- Then I need complete M₁₁ ⬝ N' ⇒ complete M₁₁, but that's not true!
        -- Wait, I need to look at complete (((K ⬝ M₁₁) ⬝ M₁₂) ⬝ N₁) more carefully
        -- Line 38 says: Term.app (Term.app K M) _ => complete M
        -- So complete ((K ⬝ M₁₁) ⬝ anything) = complete M₁₁
        -- Therefore complete (((K ⬝ M₁₁) ⬝ M₁₂) ⬝ N₁) = complete M₁₁
        -- Good! So I need ((K ⬝ M₁₁') ⬝ M₁₂') ⬝ N' ⇒ complete M₁₁
        -- And looking at the k_red pattern again: ParRed (K ⬝ M ⬝ N) M' if M ⇒ M'
        -- So (K ⬝ ((M₁₁') ⬝ M₁₂')) ⬝ N' ⇒ complete M₁₁ if (M₁₁') ⬝ M₁₂' ⇒ complete M₁₁
        -- But we have ((K ⬝ M₁₁') ⬝ M₁₂') not (K ⬝ (M₁₁' ⬝ M₁₂'))
        -- They're different due to associativity!
        -- Actually, since ⬝ is left-associative, K ⬝ M₁₁' ⬝ M₁₂' = (K ⬝ M₁₁') ⬝ M₁₂'
        -- So k_red says: (K ⬝ M₁₁' ⬝ M₁₂') ⬝ N' ⇒ M' if M₁₁' ⇒ M'
        -- But I need ihM : (K ⬝ M₁₁') ⬝ M₁₂' ⇒ complete M₁₁
        -- This doesn't match! Let me look at k_red more carefully.
        -- k_red : ParRed M M' → ParRed N N' → ParRed (K ⬝ M ⬝ N) M'
        -- This is: ParRed (Term.app (Term.app K M) N) M'
        -- So (K ⬝ M ⬝ N) = (app (app K M) N)
        -- For our case, we want (app (app (app K M₁₁') M₁₂') N') ⇒ complete M₁₁
        -- Using k_red with M = (app K M₁₁'), N = M₁₂', we'd get
        -- (K ⬝ (app K M₁₁') ⬝ M₁₂') ⬝ N' ⇒ complete M₁₁ if (app K M₁₁') ⇒ complete M₁₁
        -- But that's also not what we have!
        --
        -- OK let me think differently. The term ((K ⬝ M₁₁') ⬝ M₁₂') ⬝ N' matches
        -- the K-redex pattern from complete: Term.app (Term.app K M) _
        -- where M = M₁₁' and _ = M₁₂' ⬝ N' (but we're at the wrong level!)
        --
        -- Actually, let me re-examine: ((K ⬝ M₁₁') ⬝ M₁₂') ⬝ N'
        -- = app (app (app K M₁₁') M₁₂') N'
        -- Does this match app (app K M) _? Let's see:
        -- app (app (app K M₁₁') M₁₂') N' vs app (app K M) _
        -- These don't match because the first has an extra app
        --
        -- So the K-redex is NOT at this level. Instead, I should use the fact that
        -- ihM : ((K ⬝ M₁₁') ⬝ M₁₂') ⇒ complete M₁₁ and then apply app:
        simp [complete]
        exact app ihM ihN
      · -- M' = M₁₁' (K contraction happened at the inner level)
        -- ihM : M₁₁' ⇒ complete ((K ⬝ M₁₁) ⬝ M₁₂)
        -- complete ((K ⬝ M₁₁) ⬝ M₁₂) = complete M₁₁
        -- So ihM : M₁₁' ⇒ complete M₁₁
        -- Need: M₁₁' ⬝ N' ⇒ complete M₁₁
        simp [complete]
        exact app ihM ihN
    | Term.app (Term.app (Term.app S M₁₁) M₁₂) M₁₃ =>
      -- M₁ = ((S ⬝ M₁₁) ⬝ M₁₂) ⬝ M₁₃, so M₁ ⬝ N₁ = (((S ⬝ M₁₁) ⬝ M₁₂) ⬝ M₁₃) ⬝ N₁
      -- But this doesn't match the S-redex pattern for complete!
      -- ((S ⬝ M₁₁) ⬝ M₁₂) ⬝ M₁₃ has 3 nested apps, BUT we need the pattern
      -- (S ⬝ M) ⬝ N ⬝ P where the outer app is the third one
      -- So ((S ⬝ M₁₁) ⬝ M₁₂) ⬝ M₁₃ DOES match! It's S ⬝ M₁₁ ⬝ M₁₂ ⬝ M₁₃
      -- Wait no - let me reconsider. The term is M₁ ⬝ N₁ where M₁ = ((S ⬝ M₁₁) ⬝ M₁₂) ⬝ M₁₃
      -- So the full term is (((S ⬝ M₁₁) ⬝ M₁₂) ⬝ M₁₃) ⬝ N₁, which is S ⬝ M₁₁ ⬝ M₁₂ ⬝ M₁₃ ⬝ N₁
      -- This is too many apps! Let me reconsider...
      -- Actually wait - M₁ was defined at the start as the first argument to the app
      -- So if M₁ = ((S ⬝ M₁₁) ⬝ M₁₂) ⬝ M₁₃, then complete (M₁ ⬝ N₁)
      -- = complete ((((S ⬝ M₁₁) ⬝ M₁₂) ⬝ M₁₃) ⬝ N₁)
      -- This doesn't match the S-redex pattern which is  Term.app (Term.app (Term.app S M) N) P
      -- So this would fall through to the default case
      simp [complete]
      exact app ihM ihN
    | Term.app (Term.app S M₁₁) M₁₂ =>
      -- M₁ = (S ⬝ M₁₁) ⬝ M₁₂, so M₁ ⬝ N₁ = ((S ⬝ M₁₁) ⬝ M₁₂) ⬝ N₁
      -- This IS the S-redex pattern! complete (((S ⬝ M₁₁) ⬝ M₁₂) ⬝ N₁)
      -- = (complete M₁₁ ⬝ complete N₁) ⬝ (complete M₁₂ ⬝ complete N₁)
      obtain ⟨M₁₁', M₁₂', rfl, _, _⟩ := app_SM_inv hM
      -- M' = (S ⬝ M₁₁') ⬝ M₁₂', so M' ⬝ N' = ((S ⬝ M₁₁') ⬝ M₁₂') ⬝ N'
      -- ihM : ((S ⬝ M₁₁') ⬝ M₁₂') ⇒ complete ((S ⬝ M₁₁) ⬝ M₁₂)
      -- complete ((S ⬝ M₁₁) ⬝ M₁₂) = (S ⬝ complete M₁₁) ⬝ complete M₁₂ (NOT an S-redex!)
      -- Need to extract M₁₁' ⇒ complete M₁₁ and M₁₂' ⇒ complete M₁₂ from ihM
      obtain ⟨M₁₁'', M₁₂'', e, h₁₁, h₁₂⟩ := app_SM_inv ihM
      -- e : (S ⬝ complete M₁₁) ⬝ complete M₁₂ = (S ⬝ M₁₁'') ⬝ M₁₂''
      simp [complete] at e
      -- e : complete M₁₁ = M₁₁'' ∧ complete M₁₂ = M₁₂''
      rcases e with ⟨e1, e2⟩
      subst e1 e2
      -- Now h₁₁ : M₁₁' ⇒ complete M₁₁ and h₁₂ : M₁₂' ⇒ complete M₁₂
      -- Need: ((S ⬝ M₁₁') ⬝ M₁₂') ⬝ N' ⇒ (complete M₁₁ ⬝ complete N₁) ⬝ (complete M₁₂ ⬝ complete N₁)
      simp [complete]
      exact s_red h₁₁ h₁₂ ihN
    | Term.app S M₁₂ =>
      -- M₁ = S ⬝ M₁₂, complete (M₁ ⬝ N₁) = (S ⬝ complete M₁₂) ⬝ complete N₁
      obtain ⟨M₁₂', rfl, _⟩ := app_S_inv hM
      -- ihM : S ⬝ M₁₂' ⇒ complete (S ⬝ M₁₂) = S ⬝ complete M₁₂
      obtain ⟨M₁₂'', e, h₁₂⟩ := app_S_inv ihM
      simp [complete] at e
      subst e
      simp [complete]
      exact app (app s_refl h₁₂) ihN
    | Term.app K M₁₂ =>
      -- M₁ = K ⬝ M₁₂, so M₁ ⬝ N₁ = (K ⬝ M₁₂) ⬝ N₁
      -- This IS a K-redex! complete ((K ⬝ M₁₂) ⬝ N₁) = complete M₁₂
      obtain ⟨M₁₂', rfl, _⟩ := app_K_inv hM
      -- ihM : K ⬝ M₁₂' ⇒ complete (K ⬝ M₁₂) = K ⬝ complete M₁₂
      obtain ⟨M₁₂'', e, h₁₂⟩ := app_K_inv ihM
      simp [complete] at e
      subst e
      -- h₁₂ : M₁₂' ⇒ complete M₁₂
      -- Need: (K ⬝ M₁₂') ⬝ N' ⇒ complete M₁₂
      simp only [complete]
      exact k_red h₁₂ ihN
    | Term.app (Term.app (Term.app _ _) _) _ =>
      -- Deeply nested, no redex
      simp [complete]
      exact app ihM ihN
  | k_red _ _ ihM _ =>
    simp [complete]
    exact ihM
  | s_red _ _ _ ihM ihN ihP =>
    simp [complete]
    exact app (app ihM ihP) (app ihN ihP)

/-! ## Diamond Property -/

/-- Parallel reduction has the diamond property.

    ```
        M
       / \
      N₁  N₂
       \ /
        P
    ```

    If M ⇒ N₁ and M ⇒ N₂, then both reach complete M. -/
theorem parRed_diamond : Rewriting.Diamond ParRed := by
  intro M N₁ N₂ h1 h2
  exact ⟨complete M, parRed_complete h1, parRed_complete h2⟩

/-! ## Main Confluence Theorem -/

/-- Parallel reduction is confluent (immediate from diamond) -/
theorem parRed_confluent : Rewriting.Confluent ParRed :=
  Rewriting.confluent_of_diamond parRed_diamond

/-- Multi-step parallel reduction -/
abbrev ParRedStar := Rewriting.Star ParRed

/-- Convert multi-step parallel reduction to multi-step weak reduction -/
theorem parRedStar_to_multi {M N : Term} (h : ParRedStar M N) : M ⟶* N := by
  induction h with
  | refl => exact MultiStep.refl _
  | tail _ hstep ih => exact MultiStep.trans ih (ParRed.to_multi hstep)

/-- Convert multi-step weak reduction to multi-step parallel reduction -/
theorem multi_to_parRedStar {M N : Term} (h : M ⟶* N) : ParRedStar M N := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hstep ih => exact Rewriting.Star.tail ih (ParRed.of_step hstep)

/-- Weak reduction is confluent.

    We prove this by showing:
    1. WeakStep ⊆ ParRed (via ParRed.of_step)
    2. ParRed ⊆ WeakStep* (via ParRed.to_multi)
    3. ParRed has diamond property
    4. Therefore WeakStep* is confluent -/
theorem confluent : Rewriting.Confluent WeakStep := by
  intro M N₁ N₂ h1 h2
  -- Convert WeakStep* to ParRed*
  have hp1 : ParRedStar M N₁ := multi_to_parRedStar h1
  have hp2 : ParRedStar M N₂ := multi_to_parRedStar h2
  -- Use confluence of ParRed
  obtain ⟨P, hpN1, hpN2⟩ := parRed_confluent M N₁ N₂ hp1 hp2
  -- Convert back to WeakStep*
  exact ⟨P, parRedStar_to_multi hpN1, parRedStar_to_multi hpN2⟩

/-! ## Church-Rosser Property -/

/-- Church-Rosser theorem for Combinatory Logic.

    If M ⟶* N₁ and M ⟶* N₂, then N₁ and N₂ have a common reduct. -/
theorem church_rosser {M N₁ N₂ : Term} (h1 : M ⟶* N₁) (h2 : M ⟶* N₂) :
    ∃ P, (N₁ ⟶* P) ∧ (N₂ ⟶* P) :=
  confluent M N₁ N₂ h1 h2

/-! ## Corollaries -/

/-- An element is in normal form if it cannot be reduced -/
def IsNormal (M : Term) : Prop := ∀ N, ¬(M ⟶ N)

/-- Normal forms are unique -/
theorem normalForm_unique {M N₁ N₂ : Term}
    (h1 : M ⟶* N₁) (h2 : M ⟶* N₂)
    (hn1 : IsNormal N₁) (hn2 : IsNormal N₂) : N₁ = N₂ := by
  have hn1' : Rewriting.IsNormalForm WeakStep N₁ := fun _ h => hn1 _ h
  have hn2' : Rewriting.IsNormalForm WeakStep N₂ := fun _ h => hn2 _ h
  exact Rewriting.normalForm_unique confluent h1 h2 hn1' hn2'

end Metatheory.CL
