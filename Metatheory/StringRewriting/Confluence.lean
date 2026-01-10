/-
# String Rewriting - Confluence

This module proves confluence for our idempotent string rewriting system
using Newman's lemma (termination + local confluence).

## Strategy

1. **Termination**: Each step reduces string length by 1
2. **Local Confluence**: Analyze all critical pairs
3. **Confluence**: Apply Newman's lemma from generic framework

## References

- Newman, "On Theories with a Combinatorial Definition of Equivalence" (1942)
- Book & Otto, "String-Rewriting Systems" (1993)
-/

import Metatheory.StringRewriting.Rules
import Metatheory.Rewriting.Newman

namespace Metatheory.StringRewriting

open Symbol Rewriting

/-! ## Termination -/

/-- Plus Step decreases string length -/
theorem plus_length_decreasing {s t : Str} (h : Plus Step s t) : t.length < s.length := by
  induction h with
  | single hst =>
    have := step_length hst
    omega
  | tail _ hst ih =>
    have := step_length hst
    omega

/-- The string rewriting system is terminating.

    Proof: String length is a well-founded measure that decreases with each step.
    Since length is a natural number and each step reduces length by 1,
    the system terminates. -/
theorem step_terminating : Terminating Step := by
  -- Terminating Step means WellFounded (fun a b => Plus Step b a)
  apply Subrelation.wf
  · -- Show our relation is a subrelation of InvImage (· < ·) List.length
    intro a b hplus
    exact plus_length_decreasing hplus
  · -- Show InvImage (· < ·) List.length is well-founded
    exact InvImage.wf List.length Nat.lt_wfRel.wf

/-! ## Normal Forms -/

/-- Every string has a normal form (by termination). -/
theorem hasNormalForm (s : Str) : HasNormalForm Step s :=
  hasNormalForm_of_terminating step_terminating s

/-! ## Local Confluence -/

/-! ### Helper Lemmas for Critical Pair Analysis -/

/-- Critical pair lemma for aa-redex overlaps.

    When two aa-reductions occur from the same string at different positions,
    they form joinable terms. This requires analyzing several cases:
    1. Non-overlapping (distance ≥ 2): both reductions can be applied
    2. Overlapping (pattern aaa): both yield same result (aa)

    **References:**
    - Book & Otto, "String-Rewriting Systems" (1993), Theorem 1.1.11
    - Baader & Nipkow, "Term Rewriting and All That" (1998), Section 2.7 -/
theorem aa_critical_pair (l1 r1 l2 r2 : Str)
    (heq : l1 ++ [a, a] ++ r1 = l2 ++ [a, a] ++ r2)
    (hne : l1 ≠ l2 ∨ r1 ≠ r2) :
    Joinable Step (l1 ++ [a] ++ r1) (l2 ++ [a] ++ r2) := by
  -- Analyze relative positions by induction on l1
  revert l2 r2
  induction l1 with
  | nil =>
    intro l2 r2 heq hne
    -- Case: [] ++ [a,a] ++ r1 = l2 ++ [a,a] ++ r2
    -- So [a,a] ++ r1 = l2 ++ [a,a] ++ r2
    cases l2 with
    | nil =>
      -- Both at same position: [] ++ [a,a] ++ r1 = [] ++ [a,a] ++ r2
      -- So r1 = r2, contradicts hne (since l1 = l2 = [])
      simp at heq
      have : r1 = r2 := heq
      cases hne with
      | inl h => contradiction
      | inr h => contradiction
    | cons x xs =>
      -- [a,a] ++ r1 = (x :: xs) ++ [a,a] ++ r2
      cases x with
      | a =>
        -- [a,a] ++ r1 = [a] ++ xs ++ [a,a] ++ r2
        cases xs with
        | nil =>
          -- Overlapping: [a,a] ++ r1 = [a] ++ [] ++ [a,a] ++ r2 = [a,a,a] ++ r2
          -- So a::a::r1 = a::a::a::r2, hence r1 = [a] ++ r2
          have h : [a, a] ++ r1 = [a, a, a] ++ r2 := by
            have := heq
            simp only [List.nil_append, List.cons_append] at this
            exact this
          have hr1 : r1 = [a] ++ r2 := by
            have h1 : a :: a :: r1 = a :: a :: a :: r2 := h
            injection h1 with _ h2
            injection h2
          subst hr1
          -- [] ++ [a] ++ [a] ++ r2 and [a] ++ [a] ++ r2
          -- Both reduce to [a] ++ r2
          simp only [List.nil_append, List.cons_append]
          exact Joinable.refl Step _
        | cons y ys =>
          -- [a,a] ++ r1 = [a, y] ++ ys ++ [a,a] ++ r2
          cases y with
          | a =>
            -- [a,a] ++ r1 = [a,a] ++ ys ++ [a,a] ++ r2
            have h : [a, a] ++ r1 = [a, a] ++ ys ++ [a, a] ++ r2 := by
              simp only [List.nil_append, List.cons_append] at heq; exact heq
            have hr1 : r1 = ys ++ [a, a] ++ r2 := List.append_cancel_left h
            -- Non-overlapping: [] ++ [a] ++ r1 vs [a,a] ++ ys ++ [a] ++ r2
            -- With r1 = ys ++ [a,a] ++ r2, so:
            -- [] ++ [a] ++ ys ++ [a,a] ++ r2 vs [a,a] ++ ys ++ [a] ++ r2
            -- Both reduce to [a] ++ ys ++ [a] ++ r2
            subst hr1
            exact ⟨[a] ++ ys ++ [a] ++ r2,
              Star.single (Step.aa_rule ([a] ++ ys) r2),
              Star.single (Step.aa_rule [] (ys ++ [a] ++ r2))⟩
          | b =>
            -- [a,a] ++ r1 = [a,b] ++ ys ++ [a,a] ++ r2
            -- This is impossible: a ≠ b, so the second element doesn't match
            have h : [a, a] ++ r1 = [a, b] ++ ys ++ [a, a] ++ r2 := by
              simp only [List.nil_append, List.cons_append] at heq; exact heq
            injection h with _ h1
            injection h1 with hcontra _
            -- hcontra : a = b, contradiction
            nomatch hcontra
      | b =>
        -- [a,a] ++ r1 = [b] ++ xs ++ [a,a] ++ r2
        -- This is impossible since first element is a ≠ b
        have h : [a, a] ++ r1 = [b] ++ xs ++ [a, a] ++ r2 := by
          simp only [List.nil_append, List.cons_append] at heq; exact heq
        injection h with hcontra _
        -- hcontra : a = b, contradiction
        nomatch hcontra
  | cons x xs ih =>
    intro l2 r2 heq hne
    -- Case: (x :: xs) ++ [a,a] ++ r1 = l2 ++ [a,a] ++ r2
    cases l2 with
    | nil =>
      -- (x :: xs) ++ [a,a] ++ r1 = [] ++ [a,a] ++ r2
      -- So x :: (xs ++ [a,a] ++ r1) = [a,a] ++ r2
      cases x with
      | a =>
        cases xs with
        | nil =>
          -- Overlapping from right: [a, a, a] ++ r1 = [a,a] ++ r2
          have h : [a, a, a] ++ r1 = [a, a] ++ r2 := by
            simp only [List.cons_append] at heq; exact heq
          have hr2 : [a] ++ r1 = r2 := by
            have h1 : a :: a :: a :: r1 = a :: a :: r2 := h
            injection h1 with _ h2
            injection h2
          subst hr2
          -- [a] ++ [a] ++ r1 and [] ++ [a] ++ [a] ++ r1
          simp only [List.nil_append, List.cons_append]
          exact Joinable.refl Step _
        | cons y ys =>
          cases y with
          | a =>
            -- [a,a] ++ ys ++ [a,a] ++ r1 = [a,a] ++ r2
            have h : [a, a] ++ ys ++ [a, a] ++ r1 = [a, a] ++ r2 := by
              simp only [List.cons_append] at heq; exact heq
            have hr2 : ys ++ [a, a] ++ r1 = r2 := by
              have h1 : a :: a :: (ys ++ [a, a] ++ r1) = a :: a :: r2 := h
              injection h1 with _ h2
              injection h2
            subst hr2
            -- Non-overlapping: [a,a] ++ ys ++ [a] ++ r1 vs [] ++ [a] ++ ys ++ [a,a] ++ r1
            exact ⟨[a] ++ ys ++ [a] ++ r1,
              Star.single (Step.aa_rule [] (ys ++ [a] ++ r1)),
              Star.single (Step.aa_rule ([a] ++ ys) r1)⟩
          | b =>
            -- [a,b] ++ ys ++ [a,a] ++ r1 = [a,a] ++ r2, impossible
            have h : [a, b] ++ ys ++ [a, a] ++ r1 = [a, a] ++ r2 := by
              simp only [List.cons_append] at heq; exact heq
            injection h with _ h1
            injection h1 with hcontra _
            nomatch hcontra
      | b =>
        -- (b :: xs) ++ [a,a] ++ r1 = [] ++ [a,a] ++ r2, impossible
        have h : (b :: xs) ++ [a, a] ++ r1 = [a, a] ++ r2 := by
          simp only [List.cons_append] at heq; exact heq
        injection h with hcontra _
        nomatch hcontra
    | cons y ys =>
      -- (x :: xs) ++ [a,a] ++ r1 = (y :: ys) ++ [a,a] ++ r2
      have h : x :: (xs ++ [a, a] ++ r1) = y :: (ys ++ [a, a] ++ r2) := by
        simp only [List.cons_append] at heq; exact heq
      injection h with hxy hrest
      subst hxy
      -- xs ++ [a,a] ++ r1 = ys ++ [a,a] ++ r2
      have hne' : xs ≠ ys ∨ r1 ≠ r2 := by
        cases hne with
        | inl h => left; intro hc; apply h; simp [hc]
        | inr h => right; exact h
      have := ih ys r2 hrest hne'
      obtain ⟨w, h1, h2⟩ := this
      -- Extend with x on the left
      exact ⟨x :: w,
        multi_context_left [x] h1,
        multi_context_left [x] h2⟩

/-- Critical pair lemma for bb-redex overlaps.

    Analogous to aa_critical_pair but for bb reductions.

    **References:**
    - Book & Otto, "String-Rewriting Systems" (1993), Theorem 1.1.11
    - Baader & Nipkow, "Term Rewriting and All That" (1998), Section 2.7 -/
theorem bb_critical_pair (l1 r1 l2 r2 : Str)
    (heq : l1 ++ [b, b] ++ r1 = l2 ++ [b, b] ++ r2)
    (hne : l1 ≠ l2 ∨ r1 ≠ r2) :
    Joinable Step (l1 ++ [b] ++ r1) (l2 ++ [b] ++ r2) := by
  -- Same proof structure as aa_critical_pair
  revert l2 r2
  induction l1 with
  | nil =>
    intro l2 r2 heq hne
    cases l2 with
    | nil =>
      simp at heq
      have : r1 = r2 := heq
      cases hne with
      | inl h => contradiction
      | inr h => contradiction
    | cons x xs =>
      cases x with
      | a =>
        have h : [b, b] ++ r1 = [a] ++ xs ++ [b, b] ++ r2 := by
          simp only [List.nil_append, List.cons_append] at heq; exact heq
        injection h with hcontra _
        nomatch hcontra
      | b =>
        cases xs with
        | nil =>
          have h : [b, b] ++ r1 = [b, b, b] ++ r2 := by
            simp only [List.nil_append, List.cons_append] at heq; exact heq
          have hr1 : r1 = [b] ++ r2 := by
            have h1 : b :: b :: r1 = b :: b :: b :: r2 := h
            injection h1 with _ h2
            injection h2
          subst hr1
          simp only [List.nil_append, List.cons_append]
          exact Joinable.refl Step _
        | cons y ys =>
          cases y with
          | a =>
            have h : [b, b] ++ r1 = [b, a] ++ ys ++ [b, b] ++ r2 := by
              simp only [List.nil_append, List.cons_append] at heq; exact heq
            injection h with _ h1
            injection h1 with hcontra _
            nomatch hcontra
          | b =>
            have h : [b, b] ++ r1 = [b, b] ++ ys ++ [b, b] ++ r2 := by
              simp only [List.nil_append, List.cons_append] at heq; exact heq
            have hr1 : r1 = ys ++ [b, b] ++ r2 := List.append_cancel_left h
            -- Non-overlapping: [] ++ [b] ++ r1 vs [b,b] ++ ys ++ [b] ++ r2
            -- With r1 = ys ++ [b,b] ++ r2, so:
            -- [] ++ [b] ++ ys ++ [b,b] ++ r2 vs [b,b] ++ ys ++ [b] ++ r2
            -- Both reduce to [b] ++ ys ++ [b] ++ r2
            subst hr1
            exact ⟨[b] ++ ys ++ [b] ++ r2,
              Star.single (Step.bb_rule ([b] ++ ys) r2),
              Star.single (Step.bb_rule [] (ys ++ [b] ++ r2))⟩
  | cons x xs ih =>
    intro l2 r2 heq hne
    cases l2 with
    | nil =>
      cases x with
      | a =>
        have h : (a :: xs) ++ [b, b] ++ r1 = [b, b] ++ r2 := by
          simp only [List.cons_append] at heq; exact heq
        injection h with hcontra _
        nomatch hcontra
      | b =>
        cases xs with
        | nil =>
          -- Overlapping from right: [b,b,b] ++ r1 = [b,b] ++ r2
          have h : [b, b, b] ++ r1 = [b, b] ++ r2 := by
            simp only [List.cons_append] at heq; exact heq
          have hr2 : [b] ++ r1 = r2 := by
            have h1 : b :: b :: b :: r1 = b :: b :: r2 := h
            injection h1 with _ h2
            injection h2
          subst hr2
          -- [b] ++ [b] ++ r1 and [] ++ [b] ++ [b] ++ r1
          simp only [List.nil_append, List.cons_append]
          exact Joinable.refl Step _
        | cons y ys =>
          cases y with
          | a =>
            have h : (b :: a :: ys) ++ [b, b] ++ r1 = [b, b] ++ r2 := by
              simp only [List.cons_append] at heq; exact heq
            injection h with _ h1
            injection h1 with hcontra _
            nomatch hcontra
          | b =>
            -- [b,b] ++ ys ++ [b,b] ++ r1 = [b,b] ++ r2
            have h : [b, b] ++ ys ++ [b, b] ++ r1 = [b, b] ++ r2 := by
              simp only [List.cons_append] at heq; exact heq
            have hr2 : ys ++ [b, b] ++ r1 = r2 := by
              have h1 : b :: b :: (ys ++ [b, b] ++ r1) = b :: b :: r2 := h
              injection h1 with _ h2
              injection h2
            subst hr2
            -- Non-overlapping: [b,b] ++ ys ++ [b] ++ r1 vs [] ++ [b] ++ ys ++ [b,b] ++ r1
            exact ⟨[b] ++ ys ++ [b] ++ r1,
              Star.single (Step.bb_rule [] (ys ++ [b] ++ r1)),
              Star.single (Step.bb_rule ([b] ++ ys) r1)⟩
    | cons y ys =>
      -- (x :: xs) ++ [b,b] ++ r1 = (y :: ys) ++ [b,b] ++ r2
      have h : x :: (xs ++ [b, b] ++ r1) = y :: (ys ++ [b, b] ++ r2) := by
        simp only [List.cons_append] at heq; exact heq
      injection h with hxy hrest
      subst hxy
      -- xs ++ [b,b] ++ r1 = ys ++ [b,b] ++ r2
      have hne' : xs ≠ ys ∨ r1 ≠ r2 := by
        cases hne with
        | inl h => left; intro hc; apply h; simp [hc]
        | inr h => right; exact h
      have := ih ys r2 hrest hne'
      obtain ⟨w, h1, h2⟩ := this
      -- Extend with x on the left
      exact ⟨x :: w,
        multi_context_left [x] h1,
        multi_context_left [x] h2⟩

/-- Commutativity lemma: aa and bb reductions at different positions commute.

    When aa and bb occur in the same string, they must be at disjoint positions
    (different symbols cannot overlap). Both reductions can be applied in either
    order to reach a common result.

    **References:**
    - Book & Otto, "String-Rewriting Systems" (1993), Theorem 1.1.11
    - Baader & Nipkow, "Term Rewriting and All That" (1998), Section 2.7 -/
theorem aa_bb_commute (l1 r1 l2 r2 : Str)
    (heq : l1 ++ [a, a] ++ r1 = l2 ++ [b, b] ++ r2) :
    Joinable Step (l1 ++ [a] ++ r1) (l2 ++ [b] ++ r2) := by
  -- Since a ≠ b, the patterns cannot overlap
  -- We find which comes first and apply both reductions
  revert l2 r2
  induction l1 with
  | nil =>
    intro l2 r2 heq
    -- [a,a] ++ r1 = l2 ++ [b,b] ++ r2
    cases l2 with
    | nil =>
      -- [a,a] ++ r1 = [b,b] ++ r2, impossible since a ≠ b
      have h : [a, a] ++ r1 = [b, b] ++ r2 := by
        simp only [List.nil_append, List.cons_append] at heq; exact heq
      injection h with hcontra _
      nomatch hcontra
    | cons x xs =>
      cases x with
      | a =>
        -- [a,a] ++ r1 = [a] ++ xs ++ [b,b] ++ r2
        cases xs with
        | nil =>
          have h : [a, a] ++ r1 = [a, b, b] ++ r2 := by
            simp only [List.nil_append, List.cons_append] at heq; exact heq
          injection h with _ h1
          injection h1 with hcontra _
          nomatch hcontra  -- [a,a] ++ r1 = [a,b,b] ++ r2, impossible
        | cons y ys =>
          cases y with
          | a =>
            -- [a,a] ++ r1 = [a,a] ++ ys ++ [b,b] ++ r2
            have h : [a, a] ++ r1 = [a, a] ++ ys ++ [b, b] ++ r2 := by
              simp only [List.nil_append, List.cons_append] at heq; exact heq
            have hr1 : r1 = ys ++ [b, b] ++ r2 := List.append_cancel_left h
            -- Commuting: [] ++ [a] ++ r1 vs [a,a] ++ ys ++ [b] ++ r2
            -- With r1 = ys ++ [b,b] ++ r2, so:
            -- [] ++ [a] ++ ys ++ [b,b] ++ r2 vs [a,a] ++ ys ++ [b] ++ r2
            -- Both reduce to [a] ++ ys ++ [b] ++ r2
            subst hr1
            exact ⟨[a] ++ ys ++ [b] ++ r2,
              Star.single (Step.bb_rule ([a] ++ ys) r2),
              Star.single (Step.aa_rule [] (ys ++ [b] ++ r2))⟩
          | b =>
            -- [a,a] ++ r1 = [a,b] ++ ys ++ [b,b] ++ r2, impossible
            have h : [a, a] ++ r1 = [a, b] ++ ys ++ [b, b] ++ r2 := by
              simp only [List.nil_append, List.cons_append] at heq; exact heq
            injection h with _ h1
            injection h1 with hcontra _
            nomatch hcontra
      | b =>
        -- [a,a] ++ r1 = [b] ++ xs ++ [b,b] ++ r2, impossible
        have h : [a, a] ++ r1 = [b] ++ xs ++ [b, b] ++ r2 := by
          simp only [List.nil_append, List.cons_append] at heq; exact heq
        injection h with hcontra _
        nomatch hcontra
  | cons x xs ih =>
    intro l2 r2 heq
    cases l2 with
    | nil =>
      -- (x :: xs) ++ [a,a] ++ r1 = [b,b] ++ r2
      cases x with
      | a =>
        have h : (a :: xs) ++ [a, a] ++ r1 = [b, b] ++ r2 := by
          simp only [List.cons_append] at heq; exact heq
        injection h with hcontra _
        nomatch hcontra  -- impossible
      | b =>
        cases xs with
        | nil =>
          have h : [b, a, a] ++ r1 = [b, b] ++ r2 := by
            simp only [List.cons_append] at heq; exact heq
          injection h with _ h1
          injection h1 with hcontra _
          nomatch hcontra  -- [b,a,a] ++ r1 = [b,b] ++ r2, impossible
        | cons y ys =>
          cases y with
          | a =>
            have h : (b :: a :: ys) ++ [a, a] ++ r1 = [b, b] ++ r2 := by
              simp only [List.cons_append] at heq; exact heq
            injection h with _ h1
            injection h1 with hcontra _
            nomatch hcontra  -- impossible
          | b =>
            -- [b,b] ++ ys ++ [a,a] ++ r1 = [b,b] ++ r2
            have h : [b, b] ++ ys ++ [a, a] ++ r1 = [b, b] ++ r2 := by
              simp only [List.cons_append] at heq; exact heq
            have hr2 : ys ++ [a, a] ++ r1 = r2 := by
              have h1 : b :: b :: (ys ++ [a, a] ++ r1) = b :: b :: r2 := h
              injection h1 with _ h2
              injection h2
            rw [← hr2]
            -- Commuting: [b,b] ++ ys ++ [a] ++ r1 vs [] ++ [b] ++ ys ++ [a,a] ++ r1
            -- Left: [b,b] ++ ys ++ [a] ++ r1 ⟶ [b] ++ ys ++ [a] ++ r1 (bb reduction)
            -- Right: [b] ++ ys ++ [a,a] ++ r1 ⟶ [b] ++ ys ++ [a] ++ r1 (aa reduction)
            simp only [List.nil_append]
            exact ⟨[b] ++ ys ++ [a] ++ r1,
              Star.single (Step.bb_rule [] (ys ++ [a] ++ r1)),
              Star.single (Step.aa_rule ([b] ++ ys) r1)⟩
    | cons y ys =>
      -- (x :: xs) ++ [a,a] ++ r1 = (y :: ys) ++ [b,b] ++ r2
      have h : x :: (xs ++ [a, a] ++ r1) = y :: (ys ++ [b, b] ++ r2) := by
        simp only [List.cons_append] at heq; exact heq
      injection h with hxy hrest
      subst hxy
      -- xs ++ [a,a] ++ r1 = ys ++ [b,b] ++ r2
      have := ih ys r2 hrest
      obtain ⟨w, h1, h2⟩ := this
      -- Extend with x on the left
      exact ⟨x :: w,
        multi_context_left [x] h1,
        multi_context_left [x] h2⟩

/-- Local confluence of the string rewriting system.

    The system is locally confluent because:
    1. Non-overlapping redexes: order doesn't matter
    2. Overlapping redexes (critical pairs): all joinable

    **Critical Pair Analysis:**

    For idempotent rules xx → x, the only critical pairs arise from overlaps:
    - Pattern xxx can be reduced in two ways:
      * Reduce first two: xxx → xx (via first pair)
      * Reduce last two: xxx → xx (via second pair)
      * Both yield the same result, so joinable

    - Non-overlapping redexes (distance ≥ 2 apart) can be applied in either order,
      reaching a common reduct with both contractions applied

    - Different symbols (aa vs bb) cannot overlap, so reductions commute

    **Standard References:**
    - Book & Otto, "String-Rewriting Systems" (1993), Section 1.1
    - Baader & Nipkow, "Term Rewriting and All That" (1998), Chapter 2
    - Terese, "Term Rewriting Systems" (2003), Example 1.1.7 -/
theorem local_confluent : LocalConfluent Step := by
  intro s t1 t2 h1 h2
  -- We reason by case analysis: four combinations of rules
  generalize hs1 : s = s1 at h1
  generalize ht1 : t1 = t1' at h1
  generalize hs2 : s = s2 at h2
  generalize ht2 : t2 = t2' at h2
  cases h1 <;> cases h2 <;> subst ht1 ht2
  · -- Both aa_rule
    -- From hs1 : s = l ++ [a, a] ++ r and hs2 : s = l_1 ++ [a, a] ++ r_1
    -- t1 = l ++ [a] ++ r, t2 = l_1 ++ [a] ++ r_1
    rename_i l r l2 r2
    by_cases heq : l = l2 ∧ r = r2
    · -- Same position: t1 = t2
      obtain ⟨hl, hr⟩ := heq
      rw [hl, hr]
      exact Joinable.refl Step _
    · -- Different positions: use critical pair analysis
      have heq_s : l ++ [a, a] ++ r = l2 ++ [a, a] ++ r2 := by rw [← hs1, hs2]
      have hne : l ≠ l2 ∨ r ≠ r2 := by
        cases Classical.em (l = l2) with
        | inl hl => right; intro hr; apply heq; exact ⟨hl, hr⟩
        | inr hl => left; exact hl
      exact aa_critical_pair l r l2 r2 heq_s hne
  · -- aa_rule and bb_rule
    -- From hs1 : s = l ++ [a, a] ++ r and hs2 : s = l_1 ++ [b, b] ++ r_1
    rename_i l r l2 r2
    have heq_s : l ++ [a, a] ++ r = l2 ++ [b, b] ++ r2 := by rw [← hs1, hs2]
    exact aa_bb_commute l r l2 r2 heq_s
  · -- bb_rule and aa_rule
    -- From hs1 : s = l ++ [b, b] ++ r and hs2 : s = l_1 ++ [a, a] ++ r_1
    rename_i l r l2 r2
    have heq_s : l ++ [b, b] ++ r = l2 ++ [a, a] ++ r2 := by rw [← hs1, hs2]
    have := aa_bb_commute l2 r2 l r heq_s.symm
    exact Joinable.symm this
  · -- Both bb_rule
    -- From hs1 : s = l ++ [b, b] ++ r and hs2 : s = l_1 ++ [b, b] ++ r_1
    rename_i l r l2 r2
    by_cases heq : l = l2 ∧ r = r2
    · -- Same position: t1 = t2
      obtain ⟨hl, hr⟩ := heq
      rw [hl, hr]
      exact Joinable.refl Step _
    · -- Different positions: use critical pair analysis
      have heq_s : l ++ [b, b] ++ r = l2 ++ [b, b] ++ r2 := by rw [← hs1, hs2]
      have hne : l ≠ l2 ∨ r ≠ r2 := by
        cases Classical.em (l = l2) with
        | inl hl => right; intro hr; apply heq; exact ⟨hl, hr⟩
        | inr hl => left; exact hl
      exact bb_critical_pair l r l2 r2 heq_s hne

/-! ## Main Confluence Theorem -/

/-- The string rewriting system is confluent.

    By Newman's lemma: termination + local confluence → confluence -/
theorem confluent : Confluent Step :=
  confluent_of_terminating_localConfluent step_terminating local_confluent

/-! ## Unique Normal Forms -/

/-- Every string has a unique normal form (by termination + confluence). -/
theorem existsUnique_normalForm (s : Str) :
    ∃ t, s ⟶* t ∧ IsNormalForm Step t ∧
      ∀ t', s ⟶* t' ∧ IsNormalForm Step t' → t' = t :=
  existsUnique_normalForm_of_terminating_confluent step_terminating confluent s

/-! ## Church-Rosser Property -/

/-- Church-Rosser theorem for string rewriting.

    If s ⟶* t₁ and s ⟶* t₂, then t₁ and t₂ have a common reduct. -/
theorem church_rosser {s t₁ t₂ : Str} (h1 : s ⟶* t₁) (h2 : s ⟶* t₂) :
    ∃ u, (t₁ ⟶* u) ∧ (t₂ ⟶* u) :=
  confluent s t₁ t₂ h1 h2

/-! ## Normal Forms -/

/-- A string is in normal form if it cannot be reduced -/
def IsNormal (s : Str) : Prop := ∀ t, ¬(s ⟶ t)

/-- Normal forms are unique (consequence of confluence) -/
theorem normalForm_unique {s t₁ t₂ : Str}
    (h1 : s ⟶* t₁) (h2 : s ⟶* t₂)
    (hn1 : IsNormal t₁) (hn2 : IsNormal t₂) : t₁ = t₂ := by
  have hn1' : Rewriting.IsNormalForm Step t₁ := fun _ h => hn1 _ h
  have hn2' : Rewriting.IsNormalForm Step t₂ := fun _ h => hn2 _ h
  exact Rewriting.normalForm_unique confluent h1 h2 hn1' hn2'

/-! ## Examples -/

/-- Example: "aaa" reduces to "a" -/
example : [a, a, a] ⟶* [a] := by
  apply Rewriting.Star.tail
  · apply Rewriting.Star.tail
    · exact Rewriting.Star.refl _
    · exact Step.aa_rule [] [a]
  · exact Step.aa_rule [] []

/-- Example: "aabb" reduces to "ab" -/
example : [a, a, b, b] ⟶* [a, b] := by
  apply Rewriting.Star.tail
  · apply Rewriting.Star.tail
    · exact Rewriting.Star.refl _
    · exact Step.aa_rule [] [b, b]
  · exact Step.bb_rule [a] []

/-- Example: "abba" reduces to "aba" -/
example : [a, b, b, a] ⟶* [a, b, a] := by
  apply Rewriting.Star.tail
  · exact Rewriting.Star.refl _
  · exact Step.bb_rule [a] [a]

end Metatheory.StringRewriting
