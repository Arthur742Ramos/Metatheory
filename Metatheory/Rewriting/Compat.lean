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

/-- A relation is terminating (well-founded) -/
abbrev IsTerminating (r : α → α → Prop) := Terminating r

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

end TransGen

/-! ## Normal Forms -/

/-- An element is in normal form if it has no successors -/
abbrev IsNormalForm (r : α → α → Prop) (a : α) := Rewriting.IsNormalForm r a

/-- Normal forms are unique in confluent systems -/
theorem normalForm_unique_of_isConfluent {r : α → α → Prop} (hconf : IsConfluent r)
    {a n₁ n₂ : α} (h1 : ReflTransGen r a n₁) (h2 : ReflTransGen r a n₂)
    (hn1 : IsNormalForm r n₁) (hn2 : IsNormalForm r n₂) : n₁ = n₂ :=
  Rewriting.normalForm_unique hconf h1 h2 hn1 hn2

end Rewriting.Compat
