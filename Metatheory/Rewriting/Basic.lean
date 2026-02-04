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

import Mathlib.Order.WellFounded

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

/-- Inversion for Star: either reflexive or a first step with remaining Star. -/
theorem cases_head {r : α → α → Prop} {a b : α} (h : Star r a b) :
    a = b ∨ ∃ a', r a a' ∧ Star r a' b := by
  induction h with
  | refl => left; rfl
  | tail hab hbc ih =>
    cases ih with
    | inl hEq =>
      subst hEq
      right
      exact ⟨_, hbc, Star.refl _⟩
    | inr h =>
      rcases h with ⟨a', haa', ha'b⟩
      right
      exact ⟨a', haa', Star.tail ha'b hbc⟩

/-- If a Star path is nontrivial, it has a first step. -/
theorem cases_head_ne {r : α → α → Prop} {a b : α} (h : Star r a b) (hne : a ≠ b) :
    ∃ a', r a a' ∧ Star r a' b := by
  cases cases_head (r := r) h with
  | inl hEq => exact (hne hEq).elim
  | inr h' => exact h'

/-- Inversion for Star: either reflexive or a final step with prior Star. -/
theorem cases_tail {r : α → α → Prop} {a b : α} (h : Star r a b) :
    a = b ∨ ∃ b', Star r a b' ∧ r b' b := by
  induction h with
  | refl => left; rfl
  | tail hab hbc ih =>
    right
    exact ⟨_, hab, hbc⟩

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

/-- Inversion for StarHead: either reflexive or a first step with remaining StarHead. -/
theorem cases_head {r : α → α → Prop} {a b : α} (h : StarHead r a b) :
    a = b ∨ ∃ a', r a a' ∧ StarHead r a' b := by
  induction h with
  | refl => left; rfl
  | head hab hbc ih =>
    right
    exact ⟨_, hab, hbc⟩

/-- If a StarHead path is nontrivial, it has a first step. -/
theorem cases_head_ne {r : α → α → Prop} {a b : α} (h : StarHead r a b) (hne : a ≠ b) :
    ∃ a', r a a' ∧ StarHead r a' b := by
  cases cases_head (r := r) h with
  | inl hEq => exact (hne hEq).elim
  | inr h' => exact h'

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

/-- Transitive closure from a single step and a Star path. -/
theorem of_step_star {r : α → α → Prop} {a b c : α}
    (hab : r a b) (hbc : Star r b c) : Plus r a c := by
  induction hbc with
  | refl => exact Plus.single hab
  | tail _ hcd ih => exact Plus.tail ih hcd

/-- Inversion for Plus: expose the first step and the remaining Star path. -/
theorem cases_head {r : α → α → Prop} {a b : α} (h : Plus r a b) :
    ∃ a', r a a' ∧ Star r a' b := by
  induction h with
  | single hstep =>
    exact ⟨_, hstep, Star.refl _⟩
  | tail hplus hstep ih =>
    rcases ih with ⟨a', haa', ha'b⟩
    exact ⟨a', haa', Star.tail ha'b hstep⟩

/-- Inversion for Plus: expose the last step and preceding Star path. -/
theorem cases_tail {r : α → α → Prop} {a b : α} (h : Plus r a b) :
    ∃ b', Star r a b' ∧ r b' b := by
  rcases cases_head (r := r) h with ⟨a', haa', ha'b⟩
  cases Star.cases_tail (r := r) ha'b with
  | inl hEq =>
      subst hEq
      exact ⟨a, Star.refl a, haa'⟩
  | inr htail =>
      rcases htail with ⟨b', hab', hb'⟩
      exact ⟨b', Star.head haa' hab', hb'⟩

/-- Nontrivial Star paths give a Plus path. -/
theorem of_star_ne {r : α → α → Prop} {a b : α} (h : Star r a b) (hne : a ≠ b) : Plus r a b := by
  obtain ⟨a', haa', ha'b⟩ := Star.cases_head_ne (r := r) h hne
  exact of_step_star haa' ha'b

end Plus

/-- Transitive closure from a Star path and a final step. -/
theorem plus_of_star_step {r : α → α → Prop} {a b c : α}
    (hab : Star r a b) (hbc : r b c) : Plus r a c := by
  induction hab generalizing c with
  | refl =>
    exact Plus.single hbc
  | tail hab hstep ih =>
    exact Plus.tail (ih hstep) hbc

/-- A Star path is either reflexive or yields a Plus path. -/
theorem star_eq_or_plus {r : α → α → Prop} {a b : α} (h : Star r a b) : a = b ∨ Plus r a b := by
  cases Star.cases_head (r := r) h with
  | inl hEq => exact Or.inl hEq
  | inr hstep =>
    rcases hstep with ⟨a', haa', ha'b⟩
    exact Or.inr (Plus.of_step_star haa' ha'b)

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

namespace SemiDiamond

/-- Diamond property implies semi-diamond. -/
theorem of_diamond {r : α → α → Prop} (h : Diamond r) : SemiDiamond r := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := h a b c hab hac
  exact ⟨d, Star.single hbd, hcd⟩

/-- Semi-diamond implies local confluence. -/
theorem toLocalConfluent {r : α → α → Prop} (h : SemiDiamond r) : LocalConfluent r := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := h a b c hab hac
  exact ⟨d, hbd, Star.single hcd⟩

/-- Strip lemma for semi-diamond: push a step through a multi-step. -/
theorem strip {r : α → α → Prop} (h : SemiDiamond r) {a b c : α}
    (hab : r a b) (hac : Star r a c) :
    ∃ d, Star r b d ∧ Star r c d := by
  have stripHead : ∀ {a c : α}, StarHead r a c → ∀ {b : α}, r a b → ∃ d, Star r b d ∧ Star r c d := by
    intro a c hac'
    induction hac' with
    | refl =>
      intro b hab
      exact ⟨b, Star.refl b, Star.single hab⟩
    | head hab' hrest ih =>
      intro b hab
      obtain ⟨d1, hbd1, ha'd1⟩ := h _ _ _ hab hab'
      obtain ⟨d, hd1d, hcd⟩ := ih ha'd1
      exact ⟨d, Star.trans hbd1 hd1d, hcd⟩
  exact stripHead (StarHead.ofStar hac) hab

end SemiDiamond

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

/-! ## Semi-Diamond Corollaries -/

/-- Semi-diamond implies semi-confluence. -/
theorem semiConfluent_of_semiDiamond {r : α → α → Prop} (h : SemiDiamond r) : SemiConfluent r := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := SemiDiamond.strip h hab hac
  exact ⟨d, hbd, hcd⟩

/-- Semi-diamond implies confluence. -/
theorem confluent_of_semiDiamond {r : α → α → Prop} (h : SemiDiamond r) : Confluent r :=
  SemiConfluent.toConfluent (semiConfluent_of_semiDiamond h)

/-! ## Determinism Corollaries -/

/-- Deterministic relations are locally confluent. -/
theorem localConfluent_of_deterministic {r : α → α → Prop} (hdet : Deterministic r) :
    LocalConfluent r :=
  Confluent.toLocalConfluent (confluent_of_deterministic hdet)

/-- Deterministic relations are semi-confluent. -/
theorem semiConfluent_of_deterministic {r : α → α → Prop} (hdet : Deterministic r) :
    SemiConfluent r :=
  SemiConfluent.of_confluent (confluent_of_deterministic hdet)

/-- Determinism gives joinability for any two reductions from a common source. -/
theorem joinable_of_deterministic {r : α → α → Prop} (hdet : Deterministic r) {a b c : α}
    (hab : Star r a b) (hac : Star r a c) : Joinable r b c := by
  cases star_comparable_of_deterministic (r := r) hdet hab hac with
  | inl hbc => exact Joinable.of_star hbc
  | inr hcb => exact Joinable.symm (Joinable.of_star hcb)

/-! ## Termination / Strong Normalization -/

/-- A relation is terminating (strongly normalizing) if there are no infinite
    reduction sequences. Formally: the converse of the transitive closure is well-founded. -/
def Terminating (r : α → α → Prop) : Prop :=
  WellFounded (fun a b => Plus r b a)

/-- A Plus-loop witnesses non-termination. -/
theorem not_terminating_of_plus_loop {r : α → α → Prop} {a : α} (hloop : Plus r a a) :
    ¬ Terminating r := by
  intro hterm
  dsimp [Terminating] at hterm
  have hP : ∀ x, Acc (fun u v => Plus r v u) x → (Plus r x x → False) := by
    intro x hacc
    induction hacc with
    | intro x hx ih =>
      intro hloopx
      rcases Plus.cases_head (r := r) hloopx with ⟨y, hxy, hyx⟩
      have hyloop : Plus r y y := plus_of_star_step (hab := hyx) (hbc := hxy)
      exact (ih y (Plus.single hxy) hyloop)
  exact hP a (hterm.apply a) hloop

/-- Termination implies Plus is irreflexive. -/
theorem plus_irrefl_of_terminating {r : α → α → Prop} (hterm : Terminating r) {a : α} :
    ¬ Plus r a a := by
  intro hloop
  exact (not_terminating_of_plus_loop (a := a) hloop) hterm

/-- In a terminating system, mutual reachability implies equality. -/
theorem star_antisymm_of_terminating {r : α → α → Prop} (hterm : Terminating r) {a b : α}
    (hab : Star r a b) (hba : Star r b a) : a = b := by
  by_contra hne
  have hab_plus : Plus r a b := Plus.of_star_ne hab hne
  have hba_plus : Plus r b a := Plus.of_star_ne hba (by simpa [eq_comm] using hne)
  have hloop : Plus r a a := Plus.trans hab_plus hba_plus
  exact (plus_irrefl_of_terminating hterm hloop)

/-! ## Normal Forms -/

/-- An element is in normal form if it cannot be reduced further -/
def IsNormalForm (r : α → α → Prop) (a : α) : Prop :=
  ∀ b, ¬ r a b

/-- An element has a normal form if it can reduce to one -/
def HasNormalForm (r : α → α → Prop) (a : α) : Prop :=
  ∃ b, Star r a b ∧ IsNormalForm r b

/-- Any normal form trivially has a normal form. -/
theorem hasNormalForm_of_isNormalForm {r : α → α → Prop} {a : α} (hn : IsNormalForm r a) :
    HasNormalForm r a :=
  ⟨a, Star.refl a, hn⟩

/-- Normal-form existence is preserved by multi-step reduction. -/
theorem hasNormalForm_of_star {r : α → α → Prop} {a b : α}
    (hab : Star r a b) (hnf : HasNormalForm r b) : HasNormalForm r a := by
  rcases hnf with ⟨n, hbn, hnnf⟩
  exact ⟨n, Star.trans hab hbn, hnnf⟩

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

/-- If a normal form is joinable with another term, that term reduces to it. -/
theorem star_of_joinable_normalForm_left {r : α → α → Prop} {a b : α}
    (hn : IsNormalForm r a) (hab : Joinable r a b) : Star r b a := by
  rcases hab with ⟨c, hac, hbc⟩
  have hEq : a = c := star_normalForm_eq hac hn
  subst hEq
  exact hbc

/-- If a term is joinable with a normal form, it reduces to that normal form. -/
theorem star_of_joinable_normalForm_right {r : α → α → Prop} {a b : α}
    (hab : Joinable r a b) (hn : IsNormalForm r b) : Star r a b := by
  rcases hab with ⟨c, hac, hbc⟩
  have hEq : b = c := star_normalForm_eq hbc hn
  subst hEq
  exact hac

/-- Joinable normal form yields existence of normal form. -/
theorem hasNormalForm_of_joinable_normalForm {r : α → α → Prop} {a b : α}
    (hab : Joinable r a b) (hn : IsNormalForm r b) : HasNormalForm r a :=
  ⟨b, star_of_joinable_normalForm_right hab hn, hn⟩

/-- In a confluent system, joinability with normal forms determines a unique normal form. -/
theorem normalForm_unique_of_joinable_of_confluent {r : α → α → Prop} (hconf : Confluent r)
    {a b₁ b₂ : α} (h1 : Joinable r a b₁) (h2 : Joinable r a b₂)
    (hn1 : IsNormalForm r b₁) (hn2 : IsNormalForm r b₂) : b₁ = b₂ := by
  have hb1 : Star r a b₁ := star_of_joinable_normalForm_right h1 hn1
  have hb2 : Star r a b₂ := star_of_joinable_normalForm_right h2 hn2
  obtain ⟨c, h1c, h2c⟩ := hconf a b₁ b₂ hb1 hb2
  have eq1 : b₁ = c := star_normalForm_eq h1c hn1
  have eq2 : b₂ = c := star_normalForm_eq h2c hn2
  exact eq1.trans eq2.symm

/-- In a confluent system, joinable terms share the normal form of the source term. -/
theorem normalForm_of_joinable_of_confluent {r : α → α → Prop} (hconf : Confluent r) {a b : α}
    (hab : Joinable r a b) (hnf : HasNormalForm r a) :
    ∃ n, Star r a n ∧ Star r b n ∧ IsNormalForm r n := by
  rcases hnf with ⟨n, han, hnnf⟩
  rcases hab with ⟨c, hac, hbc⟩
  obtain ⟨d, hcd, hnd⟩ := hconf a c n hac han
  have hEq : n = d := star_normalForm_eq hnd hnnf
  subst hEq
  have hbd : Star r b n := Star.trans hbc hcd
  exact ⟨n, han, hbd, hnnf⟩

/-- If `a` is joinable with `b` in a confluent system and `b` has a normal form,
    then `a` has a normal form. -/
theorem hasNormalForm_of_joinable_of_confluent {r : α → α → Prop} (hconf : Confluent r) {a b : α}
    (hab : Joinable r a b) (hnf : HasNormalForm r b) : HasNormalForm r a := by
  rcases hab with ⟨c, hac, hbc⟩
  rcases hnf with ⟨n, hbn, hnnf⟩
  obtain ⟨d, hcd, hnd⟩ := hconf b c n hbc hbn
  have hEq : d = n := (star_normalForm_eq hnd hnnf).symm
  subst hEq
  exact ⟨d, Star.trans hac hcd, hnnf⟩

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
