/-
# Newman's Lemma

This module proves Newman's lemma: for terminating relations, local confluence
implies confluence.

## Main Result

`confluent_of_terminating_localConfluent`: If r is terminating and locally
confluent, then r is confluent.

## Proof Strategy

We use well-founded induction on the termination order (converse of transitive
closure). Given a →* b and a →* c, we must show b ↓ c. By well-founded induction,
we can assume the result holds for all elements reachable from a.

## References

- Newman, "On Theories with a Combinatorial Definition of Equivalence" (1942)
- Huet, "Confluent Reductions: Abstract Properties and Applications" (1980)
- Terese, "Term Rewriting Systems" (2003), Chapter 1
-/

import Metatheory.Rewriting.Basic

namespace Rewriting

/-! ## Newman's Lemma via Well-Founded Induction

The proof requires well-founded induction on the termination order.
The key insight is that at each branching point, we can:
1. Apply local confluence to close the immediate divergence
2. Use the induction hypothesis on the intermediate points (which are "smaller")

 The nested induction structure is a bit fiddly in Lean 4, so we implement the
 core lemma directly using well-founded induction (following standard textbook
 presentations).
-/

universe u

/-! ## Helper Lemmas -/

/-- Inversion lemma for Star: if Star r a b holds, either a = b or there exists
    a first step a → a' with Star r a' b. -/
theorem star_cases {α : Sort u} {r : α → α → Prop} {a b : α} (h : Star r a b) :
    (a = b) ∨ (∃ a', r a a' ∧ Star r a' b) := by
  induction h with
  | refl => left; rfl
  | tail hab hbc ih =>
    right
    cases ih with
    | inl eq =>
      -- a = b, and b → c, so a → c and c →* c
      subst eq
      exact ⟨_, hbc, Star.refl _⟩
    | inr h =>
      -- a → a' →* b → c
      obtain ⟨a', haa', ha'b⟩ := h
      exact ⟨a', haa', Star.tail ha'b hbc⟩

/-- Transitive closure from a single step and a Star path -/
theorem plus_of_step_star {α : Sort u} {r : α → α → Prop} {a b c : α}
    (hab : r a b) (hbc : Star r b c) : Plus r a c := by
  induction hbc with
  | refl => exact Plus.single hab
  | tail _ hde ih => exact Plus.tail ih hde

/-- Newman's Lemma (core): Under termination and local confluence, any divergence
    from a common source can be closed.

    The proof proceeds by well-founded induction on the termination order,
    applying local confluence at each branching point.

    Standard references:
    - Newman (1942), "On Theories with a Combinatorial Definition of Equivalence"
    - Terese (2003), "Term Rewriting Systems", Lemma 1.1.12
    - Huet (1980), "Confluent Reductions: Abstract Properties and Applications"

    Proof strategy:
    By well-founded induction on a (using termination order).
    Given a →* b and a →* c:
    - If a = b or a = c: trivial
    - Otherwise: a → b₁ →* b and a → c₁ →* c for some b₁, c₁
      By local confluence: ∃ d, b₁ →* d ∧ c₁ →* d
      By IH on b₁: b ↓ d (since a →⁺ b₁)
      By IH on c₁: c ↓ d (since a →⁺ c₁)
      Combine to get b ↓ c -/
theorem newman_core {α : Sort u} {r : α → α → Prop}
    (hterm : Terminating r) (hlc : LocalConfluent r)
    (a b c : α) (hab : Star r a b) (hac : Star r a c) : Joinable r b c := by
  -- Well-founded induction on a using the termination order
  induction a using hterm.induction generalizing b c with
  | h a ih =>
    -- Case analysis on the two Star paths
    cases star_cases hab with
    | inl eq_ab =>
      -- Case: a = b
      subst eq_ab
      exact Joinable.of_star hac
    | inr h1 =>
      obtain ⟨b₁, hab₁, hb₁b⟩ := h1
      -- Case: a → b₁ →* b
      cases star_cases hac with
      | inl eq_ac =>
        -- Case: a = c
        subst eq_ac
        exact Joinable.symm (Joinable.of_star (Star.head hab₁ hb₁b))
      | inr h2 =>
        obtain ⟨c₁, hac₁, hc₁c⟩ := h2
        -- Case: a → c₁ →* c
        -- Apply local confluence at a: a → b₁ and a → c₁
        obtain ⟨d, hb₁d, hc₁d⟩ := hlc a b₁ c₁ hab₁ hac₁

        -- By IH on b₁ (since a →⁺ b₁): join b and d
        have ih_b₁ : Joinable r b d := ih b₁ (plus_of_step_star hab₁ (Star.refl b₁)) b d hb₁b hb₁d

        -- By IH on c₁ (since a →⁺ c₁): join c and d
        have ih_c₁ : Joinable r c d := ih c₁ (plus_of_step_star hac₁ (Star.refl c₁)) c d hc₁c hc₁d

        -- Combine: b →* e ←* d →* f ←* c for some e, f
        obtain ⟨e, hbe, hde⟩ := ih_b₁
        obtain ⟨f, hcf, hdf⟩ := ih_c₁

        -- Now: b →* e, d →* e, d →* f, c →* f
        -- To use IH on d, we need a →⁺ d
        -- We have a → b₁ →* d, so a →⁺ d
        have had_plus : Plus r a d := plus_of_step_star hab₁ hb₁d

        -- Use IH on d to join e and f
        have ih_d : Joinable r e f := ih d had_plus e f hde hdf

        obtain ⟨g, heg, hfg⟩ := ih_d

        -- Final: b →* e →* g and c →* f →* g
        exact ⟨g, Star.trans hbe heg, Star.trans hcf hfg⟩

/-! ## Main Theorem -/

/-- Newman's Lemma: Termination + Local Confluence implies Confluence

    For terminating relations, local confluence is sufficient for full confluence.
    This is a fundamental result in term rewriting theory, enabling us to prove
    confluence by checking only one-step divergences (when termination holds).

    **Important**: This does NOT hold without termination! The classic counterexample
    is the relation with rules a → b, a → c, c → a, c → d which is locally confluent
    but not confluent (b and d have no common reduct). -/
theorem confluent_of_terminating_localConfluent {r : α → α → Prop}
    (hterm : Terminating r) (hlc : LocalConfluent r) : Confluent r :=
  fun a b c hab hac => newman_core hterm hlc a b c hab hac

/-- Synonym using the more evocative name -/
theorem newmans_lemma {r : α → α → Prop}
    (hterm : Terminating r) (hlc : LocalConfluent r) : Confluent r :=
  confluent_of_terminating_localConfluent hterm hlc

/-! ## Corollaries -/

/-- For terminating relations, local confluence implies Church-Rosser -/
theorem churchRosser_of_terminating_localConfluent {r : α → α → Prop}
    (hterm : Terminating r) (hlc : LocalConfluent r) : Metatheory r :=
  confluent_of_terminating_localConfluent hterm hlc

/-- Terminating + locally confluent implies unique normal forms -/
theorem normalForm_unique_of_terminating_localConfluent {r : α → α → Prop}
    (hterm : Terminating r) (hlc : LocalConfluent r) :
    ∀ {a n₁ n₂}, Star r a n₁ → Star r a n₂ →
      IsNormalForm r n₁ → IsNormalForm r n₂ → n₁ = n₂ := by
  intro a n₁ n₂ h1 h2 hn1 hn2
  exact normalForm_unique (confluent_of_terminating_localConfluent hterm hlc) h1 h2 hn1 hn2

/-- Termination + local confluence gives existence and uniqueness of normal forms. -/
theorem existsUnique_normalForm_of_terminating_localConfluent {r : α → α → Prop}
    (hterm : Terminating r) (hlc : LocalConfluent r) (a : α) :
    ∃ n, Star r a n ∧ IsNormalForm r n ∧
      ∀ n', Star r a n' ∧ IsNormalForm r n' → n' = n :=
  existsUnique_normalForm_of_terminating_confluent hterm
    (confluent_of_terminating_localConfluent hterm hlc) a

end Rewriting
