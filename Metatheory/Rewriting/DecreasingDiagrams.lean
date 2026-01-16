/-
# Decreasing Diagrams

This module implements van Oostrom's decreasing diagrams technique for proving
confluence of abstract rewriting systems.

## Overview

The decreasing diagrams method is one of the most powerful and versatile techniques
for proving confluence. It works by labeling each rewriting step with elements from
a well-founded ordered set. If every local peak can be "closed" using steps with
strictly smaller labels, then the relation is confluent.

## Key Definitions

- `LabeledARS`: A family of relations indexed by labels from a well-founded order
- `StarPred`: Multi-step reduction using only labels satisfying a predicate
- `LocallyDecreasing`: The decreasing diagrams property
- `confluent_of_locallyDecreasing`: Main theorem

## Completeness

The decreasing diagrams technique is complete for countable confluent systems:
any confluent relation can be equipped with a labeling that makes it locally decreasing.
(van Oostrom 1994, Endrullis et al. 2018)

## References

- van Oostrom, "Confluence by Decreasing Diagrams" (1994)
- Klop, van Oostrom, de Vrijer, "A Geometric Proof of Confluence by Decreasing Diagrams" (2000)
- Terese, "Term Rewriting Systems" (2003), Section 14.2
-/

import Metatheory.Rewriting.Basic
import Metatheory.Rewriting.Newman

namespace Rewriting

/-! ## Labeled Abstract Rewriting Systems -/

universe u v

/-- A labeled ARS: a family of step relations indexed by labels.
    `r l a b` means "a reduces to b with label l" -/
abbrev LabeledARS (α : Sort u) (L : Type v) := L → α → α → Prop

/-- The unlabeled union: a step exists with some label -/
def LabeledUnion {α : Sort u} {L : Type v} (r : LabeledARS α L) (a b : α) : Prop :=
  ∃ l, r l a b

/-! ## Multi-Step with Label Restrictions

We define multi-step reductions restricted to labels satisfying a predicate.
This is the key ingredient for decreasing diagrams. -/

/-- Multi-step reduction using only labels satisfying predicate P.
    `StarPred r P a b` means a →* b using only steps with labels l where P l holds. -/
inductive StarPred {α : Sort u} {L : Type v} (r : LabeledARS α L) (P : L → Prop) : α → α → Prop where
  | refl (a : α) : StarPred r P a a
  | tail {a b c : α} : StarPred r P a b → (l : L) → P l → r l b c → StarPred r P a c

namespace StarPred

variable {α : Sort u} {L : Type v} {r : LabeledARS α L}

/-- Single step satisfying P implies StarPred -/
theorem single {P : L → Prop} {a b : α} (l : L) (hl : P l) (h : r l a b) : StarPred r P a b :=
  StarPred.tail (StarPred.refl a) l hl h

/-- StarPred is transitive -/
theorem trans {P : L → Prop} {a b c : α} (h1 : StarPred r P a b) (h2 : StarPred r P b c) :
    StarPred r P a c := by
  induction h2 with
  | refl => exact h1
  | tail _ l hl hstep ih => exact StarPred.tail ih l hl hstep

/-- Weakening: if P implies Q, then StarPred P implies StarPred Q -/
theorem mono {P Q : L → Prop} (hPQ : ∀ l, P l → Q l) {a b : α} (h : StarPred r P a b) :
    StarPred r Q a b := by
  induction h with
  | refl => exact StarPred.refl _
  | tail _ l hl hstep ih => exact StarPred.tail ih l (hPQ l hl) hstep

/-- StarPred with True predicate equals full Star -/
theorem of_star {a b : α} (h : Star (LabeledUnion r) a b) : StarPred r (fun _ => True) a b := by
  induction h with
  | refl => exact StarPred.refl _
  | tail _ hbc ih =>
    obtain ⟨l, hl⟩ := hbc
    exact StarPred.tail ih l trivial hl

/-- StarPred with True predicate implies Star -/
theorem toStar {a b : α} (h : StarPred r (fun _ => True) a b) : Star (LabeledUnion r) a b := by
  induction h with
  | refl => exact Star.refl _
  | tail _ l _ hstep ih => exact Star.tail ih ⟨l, hstep⟩

end StarPred

/-! ## Decreasing Diagrams Property

The core definition: local peaks must close with strictly smaller labels.

We use a strict order `lt : L → L → Prop` on labels, assumed to be well-founded. -/

/-- **Decreasing Diagrams Property** (symmetric strict version)

    A labeled ARS is locally decreasing (with respect to a strict order lt on labels)
    if for every local peak
    ```
        a
       / \
      l₁  l₂
     ↓     ↓
     b     c
    ```
    there exists a closing diagram using only labels strictly smaller than both l₁ and l₂:
    ```
        a
       / \
      l₁  l₂
     ↓     ↓
     b     c
      \   /
      <l₁ ∧ <l₂
         d
    ```

    This symmetric version requires both sides to use strictly smaller labels.
    It's slightly stronger than van Oostrom's original formulation but simpler to state
    and sufficient for many applications. -/
def LocallyDecreasing {α : Sort u} {L : Type v}
    (r : LabeledARS α L) (lt : L → L → Prop) : Prop :=
  ∀ a b c l₁ l₂, r l₁ a b → r l₂ a c →
    ∃ d, StarPred r (fun l => lt l l₁ ∧ lt l l₂) b d ∧
         StarPred r (fun l => lt l l₁ ∧ lt l l₂) c d

/-! ## Helper Lemmas -/

/-- Helper lemma: StarPred with conjunction predicate (left projection) -/
theorem starPred_and_left {α : Sort u} {L : Type v} {r : LabeledARS α L}
    {P Q : L → Prop} {a b : α} (h : StarPred r (fun l => P l ∧ Q l) a b) :
    StarPred r P a b :=
  StarPred.mono (fun _ ⟨hp, _⟩ => hp) h

/-- Helper lemma: StarPred with conjunction predicate (right projection) -/
theorem starPred_and_right {α : Sort u} {L : Type v} {r : LabeledARS α L}
    {P Q : L → Prop} {a b : α} (h : StarPred r (fun l => P l ∧ Q l) a b) :
    StarPred r Q a b :=
  StarPred.mono (fun _ ⟨_, hq⟩ => hq) h

/-- Convert StarPred to Star for LabeledUnion -/
theorem starPred_to_star {α : Sort u} {L : Type v} {r : LabeledARS α L}
    {P : L → Prop} {a b : α} (h : StarPred r P a b) :
    Star (LabeledUnion r) a b := by
  induction h with
  | refl => exact Star.refl _
  | tail _ l _ hstep ih => exact Star.tail ih ⟨l, hstep⟩

/-! ## Immediate Consequences -/

/-- Locally decreasing implies local confluence of the unlabeled union. -/
theorem localConfluent_of_locallyDecreasing {α : Sort u} {L : Type v}
    {r : LabeledARS α L} {lt : L → L → Prop} :
    LocallyDecreasing r lt → LocalConfluent (LabeledUnion r) := by
  intro hld a b c hab hac
  obtain ⟨l1, hab⟩ := hab
  obtain ⟨l2, hac⟩ := hac
  obtain ⟨d, hbd, hcd⟩ := hld a b c l1 l2 hab hac
  exact ⟨d, starPred_to_star hbd, starPred_to_star hcd⟩

/-- If the unlabeled union is terminating, locally decreasing implies confluence (via Newman's lemma). -/
theorem confluent_of_terminating_locallyDecreasing {α : Sort u} {L : Type v}
    {r : LabeledARS α L} {lt : L → L → Prop} :
    Terminating (LabeledUnion r) → LocallyDecreasing r lt → Confluent (LabeledUnion r) := by
  intro hterm hld
  exact confluent_of_terminating_localConfluent hterm (localConfluent_of_locallyDecreasing hld)

/-- Single step to StarPred -/
theorem step_to_starPred {α : Sort u} {L : Type v} {r : LabeledARS α L}
    {P : L → Prop} {a b : α} (l : L) (hl : P l) (h : r l a b) :
    StarPred r P a b :=
  StarPred.single l hl h

/-- Star to StarPred with True predicate -/
theorem star_to_starPred_true {α : Sort u} {L : Type v} {r : LabeledARS α L}
    {a b : α} (h : Star (LabeledUnion r) a b) :
    StarPred r (fun _ => True) a b :=
  StarPred.of_star h

/-! ## Main Theorem

The main theorem `confluent_of_locallyDecreasing` states that if every local peak
can be closed using strictly smaller labels, and the label order is well-founded,
then the unlabeled relation is confluent.

This file uses a standard route to confluence:
- show that local decreasing implies **semi-confluence** (one step vs multi-step),
  by well-founded induction on the label of the single step, and a "strip" lemma
  that commutes a path of strictly smaller labels past an arbitrary multi-step;
- conclude confluence using `SemiConfluent.toConfluent` from `Rewriting.Basic`.

**References**:
- van Oostrom, "Confluence by Decreasing Diagrams" TCS 126 (1994)
- Klop, van Oostrom, de Vrijer, "A Geometric Proof..." J. Logic Comput. (2000)
- Terese, "Term Rewriting Systems" (2003), Section 14.2 -/

section MainTheorem
variable {α : Sort u} {L : Type v} {r : LabeledARS α L} {lt : L → L → Prop}

/-- Strip lemma: if all labels in a path are `< l₀`, and we have semi-confluence for all labels `< l₀`,
then we can commute that path past any multi-step reduction from the same source. -/
theorem joinable_of_starPred_lt {l₀ : L}
    (hsemi :
      ∀ l, lt l l₀ →
        ∀ {a b c : α}, r l a b → Star (LabeledUnion r) a c → Joinable (LabeledUnion r) b c)
    {a b c : α} (hab : StarPred r (fun l => lt l l₀) a b) (hac : Star (LabeledUnion r) a c) :
    Joinable (LabeledUnion r) b c := by
  induction hab with
  | refl =>
    simpa using (Joinable.of_star hac)
  | tail hab l hl hstep ih =>
    obtain ⟨d, hbd, hcd⟩ := ih
    have hj : Joinable (LabeledUnion r) _ d := hsemi l hl hstep hbd
    obtain ⟨e, hce, hde⟩ := hj
    exact ⟨e, hce, Star.trans hcd hde⟩

/-- Local decreasing implies semi-confluence of the unlabeled union. -/
theorem semiConfluent_of_locallyDecreasing (wf : WellFounded lt) (hld : LocallyDecreasing r lt) :
    SemiConfluent (LabeledUnion r) := by
  intro a b c hab hac
  obtain ⟨l₀, hab⟩ := hab

  -- Prove semi-confluence for each label by well-founded induction on `lt`.
  have hlabel :
      ∀ l : L, ∀ {a b c : α},
        r l a b → Star (LabeledUnion r) a c → Joinable (LabeledUnion r) b c := by
    intro l
    -- `C l` is: steps labeled `l` are semi-confluent with any Star reduction.
    refine (WellFounded.induction (r := lt) wf (C :=
      fun l => ∀ {a b c : α},
        r l a b → Star (LabeledUnion r) a c → Joinable (LabeledUnion r) b c) l ?_)
    intro l ih a b c hab hac
    -- Decompose the Star path from `a` to `c` to expose the first step (if any).
    cases star_cases hac with
    | inl eq_ac =>
      subst eq_ac
      exact ⟨b, Star.refl b, Star.single ⟨l, hab⟩⟩
    | inr h =>
      obtain ⟨c₁, hac₁, hc₁c⟩ := h
      obtain ⟨l₂, hac₁⟩ := hac₁
      -- Close the local peak `b ← a → c₁` decreasingly.
      obtain ⟨d, hbd, hc₁d⟩ := hld a b c₁ l l₂ hab hac₁
      have hb_d : Star (LabeledUnion r) b d := starPred_to_star hbd

      -- The closing path from `c₁` to `d` uses labels `< l` (and `< l₂`), so we can strip it.
      have hc₁d_lt : StarPred r (fun l' => lt l' l) c₁ d :=
        starPred_and_left (P := fun l' => lt l' l) (Q := fun l' => lt l' l₂) hc₁d

      have hdc : Joinable (LabeledUnion r) d c :=
        joinable_of_starPred_lt (r := r) (lt := lt) (l₀ := l) (fun l' hl => ih l' hl) hc₁d_lt hc₁c

      obtain ⟨e, hde, hce⟩ := hdc
      exact ⟨e, Star.trans hb_d hde, hce⟩

  exact hlabel l₀ hab hac

/-- **Decreasing Diagrams Theorem** (symmetric strict formulation):
if `lt` is well-founded and the labeled system is locally decreasing, then the unlabeled union is confluent. -/
theorem confluent_of_locallyDecreasing (wf : WellFounded lt) (hld : LocallyDecreasing r lt) :
    Confluent (LabeledUnion r) :=
  SemiConfluent.toConfluent (semiConfluent_of_locallyDecreasing (r := r) (lt := lt) wf hld)

/-- Church-Rosser phrasing of decreasing diagrams confluence. -/
theorem church_rosser_of_locallyDecreasing (wf : WellFounded lt) (hld : LocallyDecreasing r lt) :
    Metatheory (LabeledUnion r) :=
  confluent_of_locallyDecreasing (r := r) (lt := lt) wf hld

end MainTheorem

/-! ## Special Cases and Connections

Decreasing diagrams generalize many classical confluence criteria:

**Diamond property**: When there's only one label (Unit), LocallyDecreasing reduces to:
for every peak b ← a → c, there exists d with b →* d ←* c using labels < ().
Since there are no labels less than (), this means b = d = c. If the base relation
has the diamond property, then using a single label gives locally decreasing.

**Newman's lemma**: For terminating systems, we can label steps by their "height"
(distance to normal form). Since termination ensures this is well-founded, and
local confluence provides the closing diagrams, we get confluence.
This shows decreasing diagrams subsume Newman's lemma.

**Hindley-Rosen**: For combining relations R and S, we can use Bool as labels
(R = false, S = true). With the appropriate commutation property, peaks can be
closed decreasingly. This connection formalizes how decreasing diagrams generalize
modular confluence. -/

/-! ## References

- van Oostrom, "Confluence by Decreasing Diagrams" TCS 126 (1994)
- Klop, van Oostrom, de Vrijer, "A Geometric Proof of Confluence by
  Decreasing Diagrams" J. Logic and Computation 10(3) (2000)
- Terese, "Term Rewriting Systems" (2003), Section 14.2
- Endrullis et al., "Decreasing Diagrams with Two Labels Are Complete"
  FSCD 2018
- Felgenhauer, van Oostrom, "Proof Orders for Decreasing Diagrams" RTA 2013
-/

end Rewriting
