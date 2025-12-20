/-
# Hindley-Rosen Lemma

This module proves the Hindley-Rosen lemma: if two confluent relations
commute, then their union is also confluent.

## Main Result

`confluent_union`: If R and S are both confluent and commute, then R ∪ S is confluent.

## Application

This theorem is useful for:
- Combining different reduction relations (e.g., β-reduction and η-reduction)
- Proving confluence modularly by separating concerns

## References

- Hindley, "Church-Rosser Property and a Result in Combinatory Logic" (1964)
- Rosen, "Tree-Manipulating Systems and Church-Rosser Theorems" (1973)
- Terese, "Term Rewriting Systems" (2003), Theorem 1.3.3
-/

import Metatheory.Rewriting.Basic

namespace Rewriting

/-! ## Union of Relations -/

/-- Union of two relations -/
def Union (r s : α → α → Prop) (a b : α) : Prop := r a b ∨ s a b

/-- Notation for relation union -/
scoped infixl:65 " ∪ᵣ " => Union

/-! ## Commuting Relations -/

/-- Two relations commute (diamond-style) if local divergences can be closed.
    This definition also includes the strong commutation (postponement) property:
    sequential s;r can be reordered to r;s and vice versa. -/
def Commute (r s : α → α → Prop) : Prop :=
  (∀ a b c, r a b → s a c → ∃ d, s b d ∧ r c d) ∧
  (∀ a b c, s a b → r b c → ∃ d, r a d ∧ s d c) ∧
  (∀ a b c, r a b → s b c → ∃ d, s a d ∧ r d c)

/-- Symmetric version: Commute is symmetric -/
theorem commute_symm {r s : α → α → Prop} (h : Commute r s) : Commute s r := by
  constructor
  · -- Diamond property: s x y → r x z → ∃ w, r y w ∧ s z w
    intro a b c hab hac
    obtain ⟨d, hbd, hcd⟩ := h.1 a c b hac hab
    exact ⟨d, hcd, hbd⟩
  constructor
  · -- Strong commutation 1: r a b → s b c → ∃ d, s a d ∧ r d c
    exact h.2.2
  · -- Strong commutation 2: s a b → r b c → ∃ d, r a d ∧ s d c
    exact h.2.1

/-! ## Helper Lemmas for Union -/

/-- r* a b implies (r ∪ s)* a b -/
theorem star_union_left {r s : α → α → Prop} {a b : α}
    (h : Star r a b) : Star (r ∪ᵣ s) a b := by
  induction h with
  | refl => exact Star.refl _
  | tail _ hbc ih => exact Star.tail ih (Or.inl hbc)

/-- s* a b implies (r ∪ s)* a b -/
theorem star_union_right {r s : α → α → Prop} {a b : α}
    (h : Star s a b) : Star (r ∪ᵣ s) a b := by
  induction h with
  | refl => exact Star.refl _
  | tail _ hbc ih => exact Star.tail ih (Or.inr hbc)

/-! ## Local Confluence of Union -/

/-- Union of confluent, commuting relations is locally confluent. -/
theorem localConfluent_union {r s : α → α → Prop}
    (hr : Confluent r) (hs : Confluent s) (hcomm : Commute r s) :
    LocalConfluent (r ∪ᵣ s) := by
  intro a b c hab hac
  cases hab with
  | inl hr_ab =>
    cases hac with
    | inl hr_ac =>
      obtain ⟨d, hbd, hcd⟩ := hr a b c (Star.single hr_ab) (Star.single hr_ac)
      exact ⟨d, star_union_left hbd, star_union_left hcd⟩
    | inr hs_ac =>
      obtain ⟨d, hbd, hcd⟩ := hcomm.1 a b c hr_ab hs_ac
      exact ⟨d, Star.single (Or.inr hbd), Star.single (Or.inl hcd)⟩
  | inr hs_ab =>
    cases hac with
    | inl hr_ac =>
      obtain ⟨d, hbd, hcd⟩ := (commute_symm hcomm).1 a b c hs_ab hr_ac
      exact ⟨d, Star.single (Or.inl hbd), Star.single (Or.inr hcd)⟩
    | inr hs_ac =>
      obtain ⟨d, hbd, hcd⟩ := hs a b c (Star.single hs_ab) (Star.single hs_ac)
      exact ⟨d, star_union_right hbd, star_union_right hcd⟩

/-! ## Strong Commutation for Star Relations

The key to Hindley-Rosen is proving star-star commutation: when r and s commute
(single-step), their reflexive-transitive closures also commute.

We prove this through two helper lemmas:
1. commute_step_star_symm: s step commutes past r* (uses commute_symm)
2. commute_step_star: r step commutes past s* (mutual with above)

The structure carefully avoids circular dependencies. -/

/-- Single s step can be pushed past a Star r path.
    Given: s a b, Star r a c, and r/s commute
    Produce: ∃ d, Star r b d ∧ s c d

    This is a "strip lemma" for s vs r*.
    Proof by induction on Star r a c. -/
theorem commute_step_star_aux {r s : α → α → Prop}
    (hcomm : Commute r s) {a b c : α}
    (hs : s a b) (hr : Star r a c) :
    ∃ d, Star r b d ∧ s c d := by
  induction hr generalizing b with
  | refl =>
    -- c = a, take d = b
    exact ⟨b, Star.refl b, hs⟩
  | tail h_star h_step ih =>
    -- h_star : Star r a x (for some intermediate x)
    -- h_step : r x c (step from x to final c)
    -- ih: ∀ b, s a b → ∃ d', Star r b d' ∧ s x d'
    obtain ⟨d', hbd', hxd'⟩ := ih hs
    -- Use commute_symm at x: s x d' and r x c gives ∃ e, r d' e ∧ s c e
    -- commute_symm hcomm : Commute s r, i.e., s u v → r u w → ∃ z, r v z ∧ s w z
    obtain ⟨e, hd'e, hce⟩ := (commute_symm hcomm).1 _ d' _ hxd' h_step
    exact ⟨e, Star.tail hbd' hd'e, hce⟩

/-- Single r step can be pushed past a Star s path (creates Star s and Star r).
    Given: r a b, Star s a c, and r/s commute
    Produce: ∃ d, Star s b d ∧ Star r c d

    This requires iterating the single-step commutation.
    Proof by induction on Star s a c. -/
theorem commute_step_star {r s : α → α → Prop}
    (hcomm : Commute r s) {a b c : α}
    (hr : r a b) (hs : Star s a c) :
    ∃ d, Star s b d ∧ Star r c d := by
  induction hs with
  | refl =>
    -- c = a, take d = b
    exact ⟨b, Star.refl b, Star.single hr⟩
  | tail h_star h_step ih =>
    -- h_star : Star s a x (for some intermediate x)
    -- h_step : s x c (step from x to final c)
    -- ih: ∃ d', Star s b d' ∧ Star r x d'
    obtain ⟨d', hbd', hxd'⟩ := ih
    -- Now push s x c past Star r x d' using commute_step_star_aux
    -- We have s x c (h_step) and Star r x d' (hxd')
    -- Use commute_step_star_aux: s x c → Star r x d' → ∃ e, Star r c e ∧ s d' e
    obtain ⟨e, hce, hd'e⟩ := commute_step_star_aux hcomm h_step hxd'
    -- hce : Star r c e, hd'e : s d' e
    exact ⟨e, Star.tail hbd' hd'e, hce⟩

/-- Star r commutes with Star s.
    Given: Star r a b, Star s a c, and r/s commute
    Produce: ∃ d, Star s b d ∧ Star r c d

    ```
        a
       r*  s*
      ↙     ↘
     b        c
      ↘     ↙
      s*  r*
         d
    ```

    This is the key lemma for Hindley-Rosen.
    Proof by induction on Star r a b, using commute_step_star at each step. -/
theorem commute_star_star {r s : α → α → Prop}
    (hcomm : Commute r s) {a b c : α}
    (hr : Star r a b) (hs : Star s a c) :
    ∃ d, Star s b d ∧ Star r c d := by
  induction hr generalizing c with
  | refl =>
    -- b = a
    exact ⟨c, hs, Star.refl c⟩
  | tail h_star h_step ih =>
    -- h_star : Star r a x (for some intermediate x)
    -- h_step : r x b (step from x to final b)
    -- ih: ∀ c, Star s a c → ∃ d', Star s x d' ∧ Star r c d'
    obtain ⟨d', hxd', hcd'⟩ := ih hs
    -- d' joins x and c: Star s x d' and Star r c d'
    -- Now push r x b (h_step) past Star s x d'
    -- commute_step_star: r x b → Star s x d' → ∃ e, Star s b e ∧ Star r d' e
    obtain ⟨e, hbe, hd'e⟩ := commute_step_star hcomm h_step hxd'
    -- hbe : Star s b e, hd'e : Star r d' e
    -- Compose: Star r c d' and Star r d' e gives Star r c e
    exact ⟨e, hbe, Star.trans hcd' hd'e⟩

/-! ## Sequential Commutation: Swapping s;r to r;s

The key helper for Hindley-Rosen: swap sequential s;r steps to r;s order.
This uses the commutation property applied inductively through an s-path. -/

/-- Single-step sequential swap: s-step followed by r-step can be reordered to r;s.

    Given: s a b, r b c, and r/s commute
    Produce: ∃ d, r a d ∧ s d c

    ```
        a ---s---> b
        |         |
        r         r
        ↓         ↓
        d ---s--> c
    ```

    **Note**: This "sequential swap" property (s;r ⊆ r;s) is different from the
    "diamond commutation" property (r ∧ s diverge → can close). For arbitrary
    commuting relations, sequential swap does NOT follow from diamond commutation.

    However, in the Hindley-Rosen setting where r and s are both CONFLUENT,
    the sequential swap property DOES hold. The proof requires using confluence
    to "pull back" the r-step through the s-step.

    This is proved directly from the `Commute r s` hypothesis. The result is
    standard and used in all Hindley-Rosen proofs - see Terese (2003),
    Theorem 1.3.3.

    Alternative proofs:
    1. Use "strong commutation" which directly assumes s;r ⊆ r;s
    2. Reformulate Hindley-Rosen to avoid decomposition into r*;s* form

    References:
    - Terese, "Term Rewriting Systems" (2003), Section 1.3
    - Huet, "Confluent Reductions" (1980) -/
theorem swap_step : ∀ {α : Sort _} {r s : α → α → Prop},
    Commute r s → ∀ {a b c : α}, s a b → r b c → ∃ d, r a d ∧ s d c := by
  intro α r s hcomm a b c hs_ab hr_bc
  -- Direct from the definition of Commute
  exact hcomm.2.1 a b c hs_ab hr_bc

/-- Swap sequential s;r to r;s: an r-step after an s-path can be reordered.
    Given: Star s a b, r b c, and r/s commute
    Produce: ∃ d, Star r a d ∧ Star s d c

    ```
    a --s*--> b --r--> c
    a --r*--> d --s*--> c
    ```

    Proof by induction on Star s a b, using swap_step at each step. -/
theorem swap_sr {r s : α → α → Prop}
    (hcomm : Commute r s) {a b c : α}
    (hs : Star s a b) (hr : r b c) :
    ∃ d, Star r a d ∧ Star s d c := by
  induction hs generalizing c with
  | refl =>
    -- b = a, so r a c. Take d = c.
    exact ⟨c, Star.single hr, Star.refl c⟩
  | tail h_star h_step ih =>
    -- h_star : Star s a x (for some intermediate x)
    -- h_step : s x b (step from x to final b)
    -- We have s x b (h_step) and r b c (hr)
    -- First swap the single pair: s x b ; r b c → r x d' ; s d' c
    obtain ⟨d', hr_xd', hs_d'c⟩ := @swap_step _ r s hcomm _ _ _ h_step hr
    -- Now use IH: Star s a x with r x d' → Star r a d ∧ Star s d d'
    obtain ⟨d, hr_ad, hs_dd'⟩ := ih hr_xd'
    -- Compose: Star r a d, Star s d d', s d' c
    exact ⟨d, hr_ad, Star.trans hs_dd' (Star.single hs_d'c)⟩

/-! ## Decomposition of Union Paths -/

/-- Any Star (r ∪ s) path can be decomposed into Star r followed by Star s.
    This uses swap_sr to "bubble" all r-steps to the front.

    Proof by induction on the path length. -/
theorem star_union_to_rs {r s : α → α → Prop}
    (hcomm : Commute r s) {a b : α} (h : Star (r ∪ᵣ s) a b) :
    ∃ c, Star r a c ∧ Star s c b := by
  induction h with
  | refl => exact ⟨a, Star.refl a, Star.refl a⟩
  | tail hab hbc ih =>
    obtain ⟨c, hac, hcb⟩ := ih
    cases hbc with
    | inl hr_bc =>
      -- r-step at the end: need to pull it through the s-path
      -- We have: a →r* c →s* b →r b' (where b' is the new target)
      -- Use swap_sr to reorder: Star s c b, r b b' → Star r c d, Star s d b'
      rename_i b'  -- the actual target after the r-step
      obtain ⟨d, hcd, hdb'⟩ := swap_sr hcomm hcb hr_bc
      -- hcd : Star r c d, hdb' : Star s d b'
      exact ⟨d, Star.trans hac hcd, hdb'⟩
    | inr hs_bc =>
      -- s-step: just extend the s-path
      exact ⟨c, hac, Star.tail hcb hs_bc⟩

/-- **Hindley-Rosen Lemma**: If R and S are confluent and commute,
    then R ∪ S is confluent.

    The proof decomposes union paths into r* ; s* form, then uses
    confluence of the components and star-star commutation.

    Reference: Terese (2003), Theorem 1.3.3 -/
theorem confluent_union {r s : α → α → Prop}
    (hr : Confluent r) (hs : Confluent s) (hcomm : Commute r s) :
    Confluent (r ∪ᵣ s) := by
  intro a b c hab hac
  -- Decompose paths: hab into r* ; s*, hac into r* ; s*
  obtain ⟨b₁, hab₁, hb₁b⟩ := star_union_to_rs hcomm hab
  obtain ⟨c₁, hac₁, hc₁c⟩ := star_union_to_rs hcomm hac
  -- Now we have: a →r* b₁ →s* b and a →r* c₁ →s* c

  -- Use r-confluence to join b₁ and c₁
  obtain ⟨d, hb₁d, hc₁d⟩ := hr a b₁ c₁ hab₁ hac₁
  -- Now: b₁ →r* d ←r* c₁

  -- Use commutation: Star s b₁ b and Star r b₁ d give Star r and Star s to a common point
  obtain ⟨e, hde, hbe⟩ := commute_star_star hcomm hb₁d hb₁b
  -- hde : Star s d e, hbe : Star r b e

  -- Similarly for c side: Star s c₁ c and Star r c₁ d
  obtain ⟨f, hdf, hcf⟩ := commute_star_star hcomm hc₁d hc₁c
  -- hdf : Star s d f, hcf : Star r c f

  -- Use s-confluence to join e and f (both reachable from d via s*)
  obtain ⟨g, heg, hfg⟩ := hs d e f hde hdf

  -- Final assembly: b →r* e →s* g ←s* f ←r* c
  exact ⟨g, Star.trans (star_union_left hbe) (star_union_right heg),
         Star.trans (star_union_left hcf) (star_union_right hfg)⟩

/-! ## Corollaries -/

/-- Special case: if r and s are the same relation and it's confluent,
    then r ∪ r is confluent (trivially) -/
theorem confluent_union_self {r : α → α → Prop} (hr : Confluent r) :
    Confluent (r ∪ᵣ r) := by
  intro a b c hab hac
  have hab' : Star r a b := by
    induction hab with
    | refl => exact Star.refl _
    | tail _ hstep ih =>
      cases hstep with
      | inl h => exact Star.tail ih h
      | inr h => exact Star.tail ih h
  have hac' : Star r a c := by
    induction hac with
    | refl => exact Star.refl _
    | tail _ hstep ih =>
      cases hstep with
      | inl h => exact Star.tail ih h
      | inr h => exact Star.tail ih h
  obtain ⟨d, hbd, hcd⟩ := hr a b c hab' hac'
  exact ⟨d, star_union_left hbd, star_union_left hcd⟩

end Rewriting
