/-
# Diamond Property and Church-Rosser

This module proves that the diamond property implies confluence (Church-Rosser).

## Main Result

`confluent_of_diamond`: If r has the diamond property, then r is confluent.

## Proof Strategy

We prove that diamond implies semi-confluence, then use the fact that
semi-confluence implies confluence (from Basic.lean).

The key is the "strip" lemma: given diamond, if r a b and Star r a c,
then b and c are joinable.
-/

import Metatheory.Rewriting.Basic

namespace Rewriting

/-! ## Strip Lemma -/

universe u

/-- Helper: push a single step through a multi-step from the SAME source.

    Given diamond, r a b, and Star r a c, find d with Star r b d and r c d.

    Note: the conclusion has `r c d` (single step from c), not `Star r c d`.
    This is a stepping stone for the full strip lemma.

    ```
        a
       / \
      b   *
       \ ↘
        d←c
    ``` -/
theorem strip_single {α : Sort u} {r : α → α → Prop} (hdiamond : Diamond r) {a b c : α}
    (hab : r a b) (hac : Star r a c) :
    ∃ d, Star r b d ∧ r c d := by
  induction hac generalizing b with
  | refl =>
    -- c = a, so r a b gives us r c b
    -- Take d = b: Star r b b (refl), r a b (which is r c b since c = a)
    exact ⟨b, Star.refl b, hab⟩
  | tail hac' hc'c ih =>
    -- hac' : Star r a x for some x
    -- hc'c : r x c (where c is the final endpoint)
    -- ih : ∀ {b}, r a b → ∃ d', Star r b d' ∧ r x d'
    obtain ⟨d', hbd', hxd'⟩ := ih hab
    -- Apply diamond to hxd' : r x d' and hc'c : r x c (same source x)
    obtain ⟨d, hd'd, hcd⟩ := hdiamond _ d' _ hxd' hc'c
    -- hd'd : r d' d, hcd : r c d
    -- Extend path: Star r b d' then r d' d gives Star r b d
    exact ⟨d, Star.tail hbd' hd'd, hcd⟩

/-- Strip lemma: diamond allows pushing a step through a multi-step.

    Given Diamond r, r a b, and Star r a c, find d with Star r b d and Star r c d.

    ```
        a
       / \
      b   *
       \ /
        d←c (where ← is *)
    ``` -/
theorem strip {α : Sort u} {r : α → α → Prop} (hdiamond : Diamond r) {a b c : α}
    (hab : r a b) (hac : Star r a c) :
    ∃ d, Star r b d ∧ Star r c d := by
  induction hac generalizing b with
  | refl =>
    -- c = a, take d = b
    exact ⟨b, Star.refl b, Star.single hab⟩
  | tail hac' hc'c ih =>
    -- hac' : Star r a c', hc'c : r c' c
    -- ih : ∀ {b}, r a b → ∃ d', Star r b d' ∧ Star r c' d'
    obtain ⟨d', hbd', hc'd'⟩ := ih hab
    -- Now push hc'c : r c' c through hc'd' : Star r c' d'
    -- strip_single returns: ∃ d, Star r c d ∧ r d' d
    obtain ⟨d, hcd, hd'd⟩ := strip_single hdiamond hc'c hc'd'
    -- hcd : Star r c d, hd'd : r d' d
    -- Compose: Star r b d' → r d' d gives Star r b d
    exact ⟨d, Star.tail hbd' hd'd, hcd⟩

/-! ## Main Theorems -/

/-- Diamond property implies semi-confluence -/
theorem semiConfluent_of_diamond {r : α → α → Prop} (h : Diamond r) : SemiConfluent r := by
  intro a b c hab hac
  exact strip h hab hac

/-- Diamond property implies confluence -/
theorem confluent_of_diamond {r : α → α → Prop} (h : Diamond r) : Confluent r :=
  SemiConfluent.toConfluent (semiConfluent_of_diamond h)

/-- Church-Rosser from diamond (synonym) -/
theorem church_rosser_of_diamond {r : α → α → Prop} (h : Diamond r) : Metatheory r :=
  confluent_of_diamond h

end Rewriting
