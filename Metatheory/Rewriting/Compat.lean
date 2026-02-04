/-
# Mathlib Compatibility Layer

This module provides type aliases and lemma names following mathlib conventions,
making it easier for users familiar with mathlib to work with this library.

## Mathlib Conventions

- `ReflTransGen` for reflexive-transitive closure (vs our `Star`)
- `TransGen` for transitive closure (vs our `Plus`)
- `EqvGen` for equivalence closure

## Usage

```lean
import Metatheory.Rewriting.Compat
open Rewriting.Compat
```
-/

import Metatheory.Rewriting.Basic
import Metatheory.Rewriting.Diamond
import Metatheory.Rewriting.Newman

namespace Rewriting.Compat

/-! ## Type Aliases (Mathlib Style) -/

/-- Reflexive-transitive closure (mathlib name: `Relation.ReflTransGen`) -/
abbrev ReflTransGen (r : α → α → Prop) := Star r

/-- Transitive closure (mathlib name: `Relation.TransGen`) -/
abbrev TransGen (r : α → α → Prop) := Plus r

/-! ## Relation Properties -/

/-- A relation has the Church-Rosser property -/
abbrev MetatheoryProp (r : α → α → Prop) := Metatheory r

/-- A relation is confluent -/
abbrev IsConfluent (r : α → α → Prop) := Confluent r

/-- A relation is locally confluent (weak Church-Rosser) -/
abbrev IsLocallyConfluent (r : α → α → Prop) := LocalConfluent r

/-- A relation has the diamond property -/
abbrev HasDiamond (r : α → α → Prop) := Diamond r

/-- A relation has the semi-diamond property. -/
abbrev HasSemiDiamond (r : α → α → Prop) := SemiDiamond r

/-- A relation is terminating (well-founded) -/
abbrev IsTerminating (r : α → α → Prop) := Terminating r

/-- A relation is deterministic (at most one successor). -/
abbrev IsDeterministic (r : α → α → Prop) := Deterministic r

/-! ## Lemma Aliases -/

/-- Diamond property implies confluence (mathlib style name) -/
theorem isConfluent_of_hasDiamond {r : α → α → Prop} (h : HasDiamond r) : IsConfluent r :=
  confluent_of_diamond h

/-- Newman's lemma: termination + local confluence → confluence -/
theorem isConfluent_of_terminating_isLocallyConfluent {r : α → α → Prop}
    (hterm : IsTerminating r) (hlc : IsLocallyConfluent r) : IsConfluent r :=
  confluent_of_terminating_localConfluent hterm hlc

/-- Confluence implies Church-Rosser property -/
theorem churchRosserProp_of_isConfluent {r : α → α → Prop} (h : IsConfluent r) : MetatheoryProp r :=
  h

/-- Determinism implies confluence (compat alias). -/
theorem isConfluent_of_isDeterministic {r : α → α → Prop} (hdet : IsDeterministic r) : IsConfluent r :=
  confluent_of_deterministic hdet

/-- Determinism implies local confluence (compat alias). -/
theorem isLocallyConfluent_of_isDeterministic {r : α → α → Prop} (hdet : IsDeterministic r) :
    IsLocallyConfluent r :=
  localConfluent_of_deterministic hdet

/-- Diamond implies semi-diamond (compat alias). -/
theorem hasSemiDiamond_of_hasDiamond {r : α → α → Prop} (h : HasDiamond r) : HasSemiDiamond r :=
  SemiDiamond.of_diamond h

/-- Semi-diamond implies local confluence (compat alias). -/
theorem isLocallyConfluent_of_hasSemiDiamond {r : α → α → Prop} (h : HasSemiDiamond r) :
    IsLocallyConfluent r :=
  SemiDiamond.toLocalConfluent h

/-- Semi-diamond implies semi-confluence (compat alias). -/
theorem isSemiConfluent_of_hasSemiDiamond {r : α → α → Prop} (h : HasSemiDiamond r) :
    Rewriting.SemiConfluent r :=
  semiConfluent_of_semiDiamond h

/-- Semi-diamond implies confluence (compat alias). -/
theorem isConfluent_of_hasSemiDiamond {r : α → α → Prop} (h : HasSemiDiamond r) : IsConfluent r :=
  confluent_of_semiDiamond h

/-! ## ReflTransGen Lemmas (matching mathlib API) -/

namespace ReflTransGen

/-- Reflexivity -/
theorem refl {r : α → α → Prop} (a : α) : ReflTransGen r a a :=
  Rewriting.Star.refl a

/-- Single step -/
theorem single {r : α → α → Prop} {a b : α} (h : r a b) : ReflTransGen r a b :=
  Rewriting.Star.single h

/-- Transitivity -/
theorem trans {r : α → α → Prop} {a b c : α}
    (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c :=
  Rewriting.Star.trans hab hbc

/-- Head: prepend a step -/
theorem head {r : α → α → Prop} {a b c : α}
    (hab : r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c :=
  Rewriting.Star.head hab hbc

/-- Tail: append a step -/
theorem tail {r : α → α → Prop} {a b c : α}
    (hab : ReflTransGen r a b) (hbc : r b c) : ReflTransGen r a c :=
  Rewriting.Star.tail hab hbc

/-- Inversion for ReflTransGen: either reflexive or a first step. -/
theorem cases_head {r : α → α → Prop} {a b : α} (h : ReflTransGen r a b) :
    a = b ∨ ∃ a', r a a' ∧ ReflTransGen r a' b :=
  Rewriting.Star.cases_head h

/-- Nontrivial ReflTransGen has a first step. -/
theorem cases_head_ne {r : α → α → Prop} {a b : α} (h : ReflTransGen r a b) (hne : a ≠ b) :
    ∃ a', r a a' ∧ ReflTransGen r a' b :=
  Rewriting.Star.cases_head_ne h hne

/-- Inversion for ReflTransGen: either reflexive or a final step. -/
theorem cases_tail {r : α → α → Prop} {a b : α} (h : ReflTransGen r a b) :
    a = b ∨ ∃ b', ReflTransGen r a b' ∧ r b' b :=
  Rewriting.Star.cases_tail h

/-- ReflTransGen is reflexive or yields a TransGen path. -/
theorem eq_or_transGen {r : α → α → Prop} {a b : α} (h : ReflTransGen r a b) :
    a = b ∨ TransGen r a b :=
  Rewriting.star_eq_or_plus h

end ReflTransGen

/-! ## TransGen Lemmas (matching mathlib API) -/

namespace TransGen

/-- Single step -/
theorem single {r : α → α → Prop} {a b : α} (h : r a b) : TransGen r a b :=
  Rewriting.Plus.single h

/-- Transitivity -/
theorem trans {r : α → α → Prop} {a b c : α}
    (hab : TransGen r a b) (hbc : TransGen r b c) : TransGen r a c :=
  Rewriting.Plus.trans hab hbc

/-- Head: prepend a step -/
theorem head {r : α → α → Prop} {a b c : α}
    (hab : r a b) (hbc : TransGen r b c) : TransGen r a c :=
  Rewriting.Plus.trans (Rewriting.Plus.single hab) hbc

/-- Tail: append a step -/
theorem tail {r : α → α → Prop} {a b c : α}
    (hab : TransGen r a b) (hbc : r b c) : TransGen r a c :=
  Rewriting.Plus.tail hab hbc

/-- Convert to reflexive-transitive closure -/
theorem toReflTransGen {r : α → α → Prop} {a b : α} (h : TransGen r a b) : ReflTransGen r a b :=
  Rewriting.Plus.toStar h

/-- Inversion for TransGen: expose the first step and remaining ReflTransGen. -/
theorem cases_head {r : α → α → Prop} {a b : α} (h : TransGen r a b) :
    ∃ a', r a a' ∧ ReflTransGen r a' b :=
  Rewriting.Plus.cases_head h

/-- Inversion for TransGen: expose the last step and preceding ReflTransGen. -/
theorem cases_tail {r : α → α → Prop} {a b : α} (h : TransGen r a b) :
    ∃ b', ReflTransGen r a b' ∧ r b' b :=
  Rewriting.Plus.cases_tail h

end TransGen

/-! ## Termination -/

/-- A Plus-loop witnesses non-termination (mathlib-style). -/
theorem not_terminating_of_transGen_loop {r : α → α → Prop} {a : α} (hloop : TransGen r a a) :
    ¬ IsTerminating r :=
  Rewriting.not_terminating_of_plus_loop hloop

/-! ## Normal Forms -/

/-- An element is in normal form if it has no successors -/
abbrev IsNormalForm (r : α → α → Prop) (a : α) := Rewriting.IsNormalForm r a

/-- An element has a normal form if it can reduce to one -/
abbrev HasNormalForm (r : α → α → Prop) (a : α) := Rewriting.HasNormalForm r a

/-- Any normal form has a normal form (compat alias). -/
theorem hasNormalForm_of_isNormalForm {r : α → α → Prop} {a : α} (hn : IsNormalForm r a) :
    HasNormalForm r a :=
  Rewriting.hasNormalForm_of_isNormalForm hn

/-- Termination implies existence of normal forms (compat alias). -/
theorem hasNormalForm_of_isTerminating {r : α → α → Prop} (hterm : IsTerminating r) (a : α) :
    HasNormalForm r a :=
  Rewriting.hasNormalForm_of_terminating hterm a

/-- Normal forms are unique in confluent systems -/
theorem normalForm_unique_of_isConfluent {r : α → α → Prop} (hconf : IsConfluent r)
    {a n₁ n₂ : α} (h1 : ReflTransGen r a n₁) (h2 : ReflTransGen r a n₂)
    (hn1 : IsNormalForm r n₁) (hn2 : IsNormalForm r n₂) : n₁ = n₂ :=
  Rewriting.normalForm_unique hconf h1 h2 hn1 hn2

/-- Confluence + normal-form existence gives a unique normal form (compat alias). -/
theorem existsUnique_normalForm_of_isConfluent_hasNormalForm {r : α → α → Prop} (hconf : IsConfluent r)
    {a : α} (hnf : HasNormalForm r a) :
    ∃ n, ReflTransGen r a n ∧ IsNormalForm r n ∧
      ∀ n', ReflTransGen r a n' ∧ IsNormalForm r n' → n' = n :=
  Rewriting.existsUnique_normalForm_of_confluent_hasNormalForm hconf hnf

/-- Termination + confluence gives unique normal forms (compat alias). -/
theorem existsUnique_normalForm_of_isTerminating_isConfluent {r : α → α → Prop}
    (hterm : IsTerminating r) (hconf : IsConfluent r) (a : α) :
    ∃ n, ReflTransGen r a n ∧ IsNormalForm r n ∧
      ∀ n', ReflTransGen r a n' ∧ IsNormalForm r n' → n' = n :=
  Rewriting.existsUnique_normalForm_of_terminating_confluent hterm hconf a

/-- Termination implies TransGen is irreflexive. -/
theorem transGen_irrefl_of_terminating {r : α → α → Prop} (hterm : IsTerminating r) {a : α} :
    ¬ TransGen r a a := by
  intro hloop
  exact (not_terminating_of_transGen_loop (a := a) hloop) hterm

/-- Termination gives antisymmetry for ReflTransGen. -/
theorem reflTransGen_antisymm_of_terminating {r : α → α → Prop} (hterm : IsTerminating r) {a b : α}
    (hab : ReflTransGen r a b) (hba : ReflTransGen r b a) : a = b :=
  Rewriting.star_antisymm_of_terminating hterm hab hba

end Rewriting.Compat
