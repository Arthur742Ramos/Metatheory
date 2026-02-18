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

/-! ## Front-Building Reflexive-Transitive Closure -/

/-- Front-building reflexive-transitive closure of a relation.

    `StarHead r a b` means `a` reduces to `b` in zero or more steps, where paths are
    built from the start (via `head`) rather than from the end (via `Star.tail`). -/
inductive StarHead (r : α → α → Prop) : α → α → Prop where
  | refl : ∀ a, StarHead r a a
  | head : ∀ {a b c}, r a b → StarHead r b c → StarHead r a c

namespace StarHead

/-- Single step implies StarHead -/
theorem single {r : α → α → Prop} {a b : α} (h : r a b) : StarHead r a b :=
  StarHead.head h (StarHead.refl b)

/-- StarHead is transitive -/
theorem trans {r : α → α → Prop} {a b c : α} (h1 : StarHead r a b) (h2 : StarHead r b c) : StarHead r a c := by
  induction h1 with
  | refl => exact h2
  | head hab hbc ih => exact StarHead.head hab (ih h2)

/-- Append a single step to the end of a StarHead path. -/
theorem append {r : α → α → Prop} {a b c : α} (hab : StarHead r a b) (hbc : r b c) : StarHead r a c := by
  induction hab with
  | refl =>
    exact StarHead.head hbc (StarHead.refl c)
  | head hab hbd ih =>
    exact StarHead.head hab (ih hbc)

/-- Convert StarHead to Star. -/
theorem toStar {r : α → α → Prop} {a b : α} (h : StarHead r a b) : Star r a b := by
  induction h with
  | refl => exact Star.refl _
  | head hab hbc ih => exact Star.head hab ih

/-- Convert Star to StarHead. -/
theorem ofStar {r : α → α → Prop} {a b : α} (h : Star r a b) : StarHead r a b := by
  induction h with
  | refl => exact StarHead.refl _
  | tail hab hbc ih => exact StarHead.append ih hbc

theorem iff_star {r : α → α → Prop} {a b : α} : StarHead r a b ↔ Star r a b :=
  ⟨toStar, ofStar⟩

end StarHead

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

/-! ## Determinism -/

/-- A relation is deterministic if it has at most one successor at each state. -/
def Deterministic (r : α → α → Prop) : Prop :=
  ∀ ⦃a b c⦄, r a b → r a c → b = c

theorem starHead_comparable_of_deterministic {r : α → α → Prop} (hdet : Deterministic r) :
    ∀ {a b c : α}, StarHead r a b → StarHead r a c → StarHead r b c ∨ StarHead r c b := by
  intro a b c hab hac
  induction hab generalizing c with
  | refl =>
    exact Or.inl hac
  | head hab1 habrest ih =>
    cases hac with
    | refl =>
      exact Or.inr (StarHead.head hab1 habrest)
    | head hac1 hacrest =>
      have habEq : _ := hdet hab1 hac1
      subst habEq
      exact ih hacrest

theorem star_comparable_of_deterministic {r : α → α → Prop} (hdet : Deterministic r) {a b c : α}
    (hab : Star r a b) (hac : Star r a c) : Star r b c ∨ Star r c b := by
  have hab' : StarHead r a b := StarHead.ofStar hab
  have hac' : StarHead r a c := StarHead.ofStar hac
  cases starHead_comparable_of_deterministic (r := r) hdet hab' hac' with
  | inl hbc => exact Or.inl (StarHead.toStar hbc)
  | inr hcb => exact Or.inr (StarHead.toStar hcb)

theorem confluent_of_deterministic {r : α → α → Prop} (hdet : Deterministic r) : Confluent r := by
  intro a b c hab hac
  cases star_comparable_of_deterministic (r := r) hdet hab hac with
  | inl hbc => exact ⟨c, hbc, Star.refl c⟩
  | inr hcb => exact ⟨b, Star.refl b, hcb⟩

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

namespace Joinable

/-- If `a` reduces to `a'` and `a'` is joinable with `b`, then `a` is joinable with `b`. -/
theorem left_of_star {r : α → α → Prop} {a a' b : α} (haa' : Star r a a') (ha'b : Joinable r a' b) :
    Joinable r a b := by
  obtain ⟨c, ha'c, hbc⟩ := ha'b
  exact ⟨c, Star.trans haa' ha'c, hbc⟩

/-- If `b` reduces to `b'` and `a` is joinable with `b'`, then `a` is joinable with `b`. -/
theorem right_of_star {r : α → α → Prop} {a b b' : α} (hbb' : Star r b b') (hab' : Joinable r a b') :
    Joinable r a b := by
  obtain ⟨c, hac, hb'c⟩ := hab'
  exact ⟨c, hac, Star.trans hbb' hb'c⟩

/-- Joinability is stable under pre-reduction on both sides. -/
theorem of_star_star {r : α → α → Prop} {a a' b b' : α} (haa' : Star r a a') (hbb' : Star r b b')
    (ha'b' : Joinable r a' b') : Joinable r a b := by
  obtain ⟨c, ha'c, hb'c⟩ := ha'b'
  exact ⟨c, Star.trans haa' ha'c, Star.trans hbb' hb'c⟩

/-- Under confluence, joinability is transitive. -/
theorem trans_of_confluent {r : α → α → Prop} (hconf : Confluent r) {a b c : α}
    (hab : Joinable r a b) (hbc : Joinable r b c) : Joinable r a c := by
  obtain ⟨x, hax, hbx⟩ := hab
  obtain ⟨y, hby, hcy⟩ := hbc
  obtain ⟨z, hxz, hyz⟩ := hconf b x y hbx hby
  exact ⟨z, Star.trans hax hxz, Star.trans hcy hyz⟩

/-- Under confluence, joinability is an equivalence relation. -/
theorem equivalence_of_confluent {r : α → α → Prop} (hconf : Confluent r) : Equivalence (Joinable r) := by
  refine ⟨Joinable.refl r, ?_, ?_⟩
  · intro a b hab
    exact Joinable.symm hab
  · intro a b c hab hbc
    exact trans_of_confluent hconf hab hbc

end Joinable

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

/-- Local (element-wise) termination implies existence of normal forms. -/
theorem hasNormalForm_of_acc {r : α → α → Prop} {a : α} (h : Acc (fun x y => r y x) a) : HasNormalForm r a := by
  classical
  induction h with
  | intro a ha ih =>
    by_cases hstep : ∃ b, r a b
    · obtain ⟨b, hab⟩ := hstep
      obtain ⟨n, hbn, hnnf⟩ := ih b hab
      exact ⟨n, Star.trans (Star.single hab) hbn, hnnf⟩
    · have hnf : IsNormalForm r a := by
        intro b hab
        exact hstep ⟨b, hab⟩
      exact ⟨a, Star.refl a, hnf⟩

/-- Termination implies existence of normal forms. -/
theorem hasNormalForm_of_terminating {r : α → α → Prop} (hterm : Terminating r) (a : α) : HasNormalForm r a := by
  classical
  refine hterm.induction a ?_
  intro a ih
  by_cases hnf : IsNormalForm r a
  · exact ⟨a, Star.refl a, hnf⟩
  · have hstep : ∃ b, r a b := by
      -- If there were no outgoing step, `a` would be a normal form.
      by_cases h : ∃ b, r a b
      · exact h
      · exfalso
        apply hnf
        intro b hab
        exact h ⟨b, hab⟩
    obtain ⟨b, hab⟩ := hstep
    obtain ⟨n, hbn, hnnf⟩ := ih b (Plus.single hab)
    exact ⟨n, Star.trans (Star.single hab) hbn, hnnf⟩

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

/-- If `a` has a normal form and the relation is confluent, that normal form is unique. -/
theorem existsUnique_normalForm_of_confluent_hasNormalForm {r : α → α → Prop}
    (hconf : Confluent r) {a : α} (hnf : HasNormalForm r a) :
    ∃ n, Star r a n ∧ IsNormalForm r n ∧
      ∀ n', Star r a n' ∧ IsNormalForm r n' → n' = n := by
  classical
  obtain ⟨n, han, hnn⟩ := hnf
  refine ⟨n, han, hnn, ?_⟩
  intro n' hn'
  rcases hn' with ⟨han', hnn'⟩
  exact normalForm_unique hconf han' han hnn' hnn

/-- Determinism implies uniqueness of normal forms (when they exist). -/
theorem normalForm_unique_of_deterministic {r : α → α → Prop} (hdet : Deterministic r) {a n₁ n₂ : α}
    (h1 : Star r a n₁) (h2 : Star r a n₂) (hn1 : IsNormalForm r n₁) (hn2 : IsNormalForm r n₂) : n₁ = n₂ :=
  normalForm_unique (confluent_of_deterministic hdet) h1 h2 hn1 hn2

/-- Termination + confluence gives existence and uniqueness of normal forms. -/
theorem existsUnique_normalForm_of_terminating_confluent {r : α → α → Prop}
    (hterm : Terminating r) (hconf : Confluent r) (a : α) :
    ∃ n, Star r a n ∧ IsNormalForm r n ∧
      ∀ n', Star r a n' ∧ IsNormalForm r n' → n' = n := by
  classical
  obtain ⟨n, han, hnn⟩ := hasNormalForm_of_terminating (r := r) hterm a
  refine ⟨n, han, hnn, ?_⟩
  intro n' hn'
  rcases hn' with ⟨han', hnn'⟩
  exact normalForm_unique hconf han' han hnn' hnn

/-! ## Key Equivalences -/

/-- Semi-confluence is equivalent to confluence -/
theorem confluent_iff_semiConfluent {r : α → α → Prop} :
    Confluent r ↔ SemiConfluent r :=
  ⟨SemiConfluent.of_confluent, SemiConfluent.toConfluent⟩

end Rewriting
