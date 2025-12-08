/-
# Abstract Rewriting Systems - Core Definitions

This module provides a generic framework for abstract rewriting systems (ARS)
and confluence theory, independent of any specific rewriting system.

## Overview

An abstract rewriting system is simply a set A with a binary relation →.
This module defines:
- Reflexive-transitive closure (multi-step reduction)
- Joinability: two elements can reach a common reduct
- Diamond property: one-step divergence can be closed in one step
- Local confluence: one-step divergence can be closed in multi-step
- Confluence (Church-Rosser): multi-step divergence can be closed

## References

- Barendregt et al., "Term Rewriting Systems" (2003)
- Terese, "Term Rewriting Systems" (2003), Chapter 1
- Huet, "Confluent Reductions: Abstract Properties and Applications" (1980)
-/

namespace Rewriting

/-! ## Reflexive-Transitive Closure -/

/-- Reflexive-transitive closure of a relation.

    `Star r a b` means `a` reduces to `b` in zero or more steps. -/
inductive Star (r : α → α → Prop) : α → α → Prop where
  | refl : ∀ a, Star r a a
  | tail : ∀ {a b c}, Star r a b → r b c → Star r a c

namespace Star

/-- Single step implies multi-step -/
theorem single {r : α → α → Prop} {a b : α} (h : r a b) : Star r a b :=
  Star.tail (Star.refl a) h

/-- Multi-step is transitive -/
theorem trans {r : α → α → Prop} {a b c : α} (h1 : Star r a b) (h2 : Star r b c) : Star r a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hbc ih => exact Star.tail ih hbc

/-- Lift a single step on the left -/
theorem head {r : α → α → Prop} {a b c : α} (hab : r a b) (hbc : Star r b c) : Star r a c :=
  trans (single hab) hbc

/-- Induction principle for Star that's more convenient for proofs -/
theorem rec_on {r : α → α → Prop} {motive : (a b : α) → Star r a b → Prop}
    {a b : α} (h : Star r a b)
    (refl : ∀ a, motive a a (Star.refl a))
    (tail : ∀ {a b c} (hab : Star r a b) (hbc : r b c),
            motive a b hab → motive a c (Star.tail hab hbc)) :
    motive a b h := by
  induction h with
  | refl => exact refl _
  | tail hab hbc ih => exact tail hab hbc ih

end Star

/-! ## Transitive Closure -/

/-- Transitive closure of a relation.

    `Plus r a b` means `a` reduces to `b` in one or more steps. -/
inductive Plus (r : α → α → Prop) : α → α → Prop where
  | single : ∀ {a b}, r a b → Plus r a b
  | tail : ∀ {a b c}, Plus r a b → r b c → Plus r a c

namespace Plus

/-- Transitive closure is transitive -/
theorem trans {r : α → α → Prop} {a b c : α} (h1 : Plus r a b) (h2 : Plus r b c) : Plus r a c := by
  induction h2 with
  | single hbc => exact Plus.tail h1 hbc
  | tail _ hcd ih => exact Plus.tail ih hcd

/-- Plus implies Star -/
theorem toStar {r : α → α → Prop} {a b : α} (h : Plus r a b) : Star r a b := by
  induction h with
  | single h => exact Star.single h
  | tail _ hbc ih => exact Star.tail ih hbc

end Plus

/-! ## Joinability -/

/-- Two elements are joinable if they have a common reduct.

    a ↓ b  iff  ∃ c, a →* c ∧ b →* c

    Joinability is the key concept for confluence. -/
def Joinable (r : α → α → Prop) (a b : α) : Prop :=
  ∃ c, Star r a c ∧ Star r b c

namespace Joinable

/-- Joinability is reflexive -/
theorem refl (r : α → α → Prop) (a : α) : Joinable r a a :=
  ⟨a, Star.refl a, Star.refl a⟩

/-- Joinability is symmetric -/
theorem symm {r : α → α → Prop} {a b : α} (h : Joinable r a b) : Joinable r b a :=
  let ⟨c, hac, hbc⟩ := h
  ⟨c, hbc, hac⟩

/-- If a →* b, then a and b are joinable -/
theorem of_star {r : α → α → Prop} {a b : α} (h : Star r a b) : Joinable r a b :=
  ⟨b, h, Star.refl b⟩

/-- If a → b, then a and b are joinable -/
theorem of_step {r : α → α → Prop} {a b : α} (h : r a b) : Joinable r a b :=
  of_star (Star.single h)

end Joinable

/-! ## Diamond Property -/

/-- The diamond property (one-step version).

    If a → b and a → c, then there exists d with b → d and c → d.

    ```
        a
       / \
      b   c
       \ /
        d
    ```

    This is a very strong property - single steps can close the diamond. -/
def Diamond (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r a c → ∃ d, r b d ∧ r c d

/-- The semi-diamond property (allows multi-step on one side).

    If a → b and a → c, then there exists d with b →* d and c → d. -/
def SemiDiamond (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r a c → ∃ d, Star r b d ∧ r c d

/-! ## Local Confluence -/

/-- Local confluence (weak Church-Rosser property).

    If a → b and a → c, then b and c are joinable.

    ```
        a
       / \
      b   c
       \ /
       →*
        d
    ```

    Local confluence allows multi-step closing of one-step divergence. -/
def LocalConfluent (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r a c → Joinable r b c

namespace LocalConfluent

/-- Diamond property implies local confluence -/
theorem of_diamond {r : α → α → Prop} (h : Diamond r) : LocalConfluent r := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := h a b c hab hac
  exact ⟨d, Star.single hbd, Star.single hcd⟩

end LocalConfluent

/-! ## Confluence -/

/-- Confluence (Church-Rosser property).

    If a →* b and a →* c, then b and c are joinable.

    ```
        a
       /∗ \∗
      b     c
       \∗ /∗
         d
    ```

    This is the main property we want to establish for rewriting systems. -/
def Confluent (r : α → α → Prop) : Prop :=
  ∀ a b c, Star r a b → Star r a c → Joinable r b c

/-- Church-Rosser is a synonym for confluence -/
abbrev Metatheory (r : α → α → Prop) : Prop := Confluent r

namespace Confluent

/-- Confluence implies local confluence -/
theorem toLocalConfluent {r : α → α → Prop} (h : Confluent r) : LocalConfluent r := by
  intro a b c hab hac
  exact h a b c (Star.single hab) (Star.single hac)

/-- If confluent, any two elements reachable from a common source are joinable -/
theorem joinable_of_common_source {r : α → α → Prop} (hconf : Confluent r) {a b c : α}
    (hab : Star r a b) (hac : Star r a c) : Joinable r b c :=
  hconf a b c hab hac

end Confluent

/-! ## Semi-Confluence -/

/-- Semi-confluence: single step vs multi-step can be closed.

    If a → b and a →* c, then b and c are joinable.

    ```
        a
       / \∗
      b   c
       \ /
       →*
        d
    ```

    This is intermediate between local confluence and confluence. -/
def SemiConfluent (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → Star r a c → Joinable r b c

namespace SemiConfluent

/-- Confluence implies semi-confluence -/
theorem of_confluent {r : α → α → Prop} (h : Confluent r) : SemiConfluent r := by
  intro a b c hab hac
  exact h a b c (Star.single hab) hac

/-- Semi-confluence implies local confluence -/
theorem toLocalConfluent {r : α → α → Prop} (h : SemiConfluent r) : LocalConfluent r := by
  intro a b c hab hac
  exact h a b c hab (Star.single hac)

/-- Semi-confluence implies confluence (key lemma!)

    Proof by induction on the first multi-step derivation. -/
theorem toConfluent {r : α → α → Prop} (hsemi : SemiConfluent r) : Confluent r := by
  intro a x y hax hay
  -- Induction on hax, generalizing y and hay so IH applies to any endpoint
  induction hax generalizing y with
  | refl => exact Joinable.of_star hay
  | tail hab hbc ih =>
    -- hab : Star r a b, hbc : r b c (where c is the current x)
    -- ih : ∀ y, Star r a y → Joinable r b y
    obtain ⟨z, hbz, hyz⟩ := ih y hay
    -- By semi-confluence on hbc : r b c and hbz : Star r b z, we get c ↓ z
    obtain ⟨w, hcw, hzw⟩ := hsemi _ _ z hbc hbz
    -- Combine: c →* w and y →* z →* w
    exact ⟨w, hcw, Star.trans hyz hzw⟩

end SemiConfluent

/-! ## Termination / Strong Normalization -/

/-- A relation is terminating (strongly normalizing) if there are no infinite
    reduction sequences. Formally: the converse of the transitive closure is well-founded. -/
def Terminating (r : α → α → Prop) : Prop :=
  WellFounded (fun a b => Plus r b a)

/-! ## Normal Forms -/

/-- An element is in normal form if it cannot be reduced further -/
def IsNormalForm (r : α → α → Prop) (a : α) : Prop :=
  ∀ b, ¬ r a b

/-- An element has a normal form if it can reduce to one -/
def HasNormalForm (r : α → α → Prop) (a : α) : Prop :=
  ∃ b, Star r a b ∧ IsNormalForm r b

/-- If a is in normal form and a →* b, then a = b -/
theorem star_normalForm_eq {r : α → α → Prop} {a b : α}
    (h : Star r a b) (hn : IsNormalForm r a) : a = b := by
  induction h with
  | refl => rfl
  | tail hab' hstep ih =>
    -- hab' : Star r a b', hstep : r b' b, ih : a = b', goal : a = b
    -- Substitute ih into hstep to get r a b
    rw [← ih] at hstep
    -- This contradicts IsNormalForm r a
    exact absurd hstep (hn _)

/-- Normal forms are unique under confluence -/
theorem normalForm_unique {r : α → α → Prop}
    (hconf : Confluent r) {a n₁ n₂ : α}
    (h1 : Star r a n₁) (h2 : Star r a n₂)
    (hn1 : IsNormalForm r n₁) (hn2 : IsNormalForm r n₂) : n₁ = n₂ := by
  -- By confluence, n₁ and n₂ are joinable
  obtain ⟨c, hn1c, hn2c⟩ := hconf a n₁ n₂ h1 h2
  -- Since n₁ is in normal form, n₁ →* c means n₁ = c
  have eq1 : n₁ = c := star_normalForm_eq hn1c hn1
  -- Similarly n₂ = c
  have eq2 : n₂ = c := star_normalForm_eq hn2c hn2
  rw [eq1, eq2]

/-! ## Key Equivalences -/

/-- Semi-confluence is equivalent to confluence -/
theorem confluent_iff_semiConfluent {r : α → α → Prop} :
    Confluent r ↔ SemiConfluent r :=
  ⟨SemiConfluent.of_confluent, SemiConfluent.toConfluent⟩

end Rewriting
