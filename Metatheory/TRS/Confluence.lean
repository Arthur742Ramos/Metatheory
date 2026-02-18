/-
# Confluence of Simple Expression Rewriting

This module proves confluence for our simple expression rewriting system
using Newman's lemma from the generic framework.

## Strategy

Unlike lambda calculus (which uses diamond property of parallel reduction),
this system is proven confluent via Newman's lemma:

1. **Termination**: Every rule decreases expression size
2. **Local Confluence**: Case analysis on critical pairs
3. **Confluence**: Follows from Newman's lemma
-/

import Metatheory.TRS.Rules
import Metatheory.Rewriting.Newman

namespace Metatheory.TRS

open Expr Step

/-! ## Termination

We prove that the rewriting system is terminating using the size measure.
-/

/-- The transitive closure of Step decreases size -/
theorem plus_size_decreasing {e₁ e₂ : Expr}
    (h : Rewriting.Plus Step e₁ e₂) : e₂.size < e₁.size := by
  induction h with
  | single h => exact Step.size_decreasing h
  | tail _ hstep ih =>
    have := Step.size_decreasing hstep
    omega

/-- Step is terminating (no infinite reduction sequences).

    Proof: Each step decreases size (Step.size_decreasing).
    Therefore the transitive closure decreases size (plus_size_decreasing).
    The inverse relation "e →⁺ e'" is bounded by size, hence well-founded. -/
theorem step_terminating : Rewriting.Terminating Step := by
  -- Terminating Step means WellFounded (fun a b => Plus Step b a)
  -- We need to show this relation is well-founded
  -- We use the fact that Plus Step b a implies b.size < a.size
  apply Subrelation.wf
  · -- Show our relation is a subrelation of InvImage (· < ·) Expr.size
    intro a b hplus
    exact plus_size_decreasing hplus
  · -- Show InvImage (· < ·) Expr.size is well-founded
    exact InvImage.wf Expr.size Nat.lt_wfRel.wf

/-! ## Normal Forms -/

/-- Every expression has a normal form (by termination). -/
theorem hasNormalForm (e : Expr) : Rewriting.HasNormalForm Step e :=
  Rewriting.hasNormalForm_of_terminating step_terminating e

/-! ## Local Confluence

Local confluence is proven by exhaustive case analysis on critical pairs.
The proof is mechanical but tedious - for each pair of rules that can apply
to the same expression, we show the results can be joined.

**Critical pairs in our system**:
1. Same rule applied twice: trivially joinable (both reach same result)
2. Base rule vs congruence: join via base rule on the reduced expression
3. Different congruence positions: parallel reduction closes the diagram

The proof technique is standard critical pair analysis from term rewriting.

References:
- Knuth & Bendix (1970), "Simple Word Problems in Universal Algebras"
- Terese (2003), "Term Rewriting Systems", Chapter 2
-/

/-- An expression is in normal form if it cannot be reduced -/
def IsNormal (e : Expr) : Prop := ∀ e', ¬(e ⟶ e')

/-- Zero is in normal form -/
theorem zero_normal : IsNormal 𝟬 := fun e' h => by cases h

/-- One is in normal form -/
theorem one_normal : IsNormal 𝟭 := fun e' h => by cases h

/-- Local confluence: if e ⟶ e₁ and e ⟶ e₂, then e₁ and e₂ are joinable.

    We prove this by case analysis on both steps, using recursion for
    congruence cases where both steps apply to the same position. -/
theorem local_confluent (e e₁ e₂ : Expr) (h1 : e ⟶ e₁) (h2 : e ⟶ e₂) :
    Rewriting.Joinable Step e₁ e₂ :=
  match h1, h2 with
  -- Same rule: trivially joinable
  | Step.addZeroR _, Step.addZeroR _ => ⟨_, MultiStep.refl _, MultiStep.refl _⟩
  | Step.addZeroL _, Step.addZeroL _ => ⟨_, MultiStep.refl _, MultiStep.refl _⟩
  | Step.mulOneR _, Step.mulOneR _ => ⟨_, MultiStep.refl _, MultiStep.refl _⟩
  | Step.mulOneL _, Step.mulOneL _ => ⟨_, MultiStep.refl _, MultiStep.refl _⟩
  | Step.mulZeroR _, Step.mulZeroR _ => ⟨𝟬, MultiStep.refl 𝟬, MultiStep.refl 𝟬⟩
  | Step.mulZeroL _, Step.mulZeroL _ => ⟨𝟬, MultiStep.refl 𝟬, MultiStep.refl 𝟬⟩
  -- Cross rules (where both sides apply): join at common form
  | Step.addZeroR _, Step.addZeroL _ => ⟨𝟬, MultiStep.refl 𝟬, MultiStep.refl 𝟬⟩
  | Step.addZeroL _, Step.addZeroR _ => ⟨𝟬, MultiStep.refl 𝟬, MultiStep.refl 𝟬⟩
  | Step.mulOneR _, Step.mulOneL _ => ⟨𝟭, MultiStep.refl 𝟭, MultiStep.refl 𝟭⟩
  | Step.mulOneL _, Step.mulOneR _ => ⟨𝟭, MultiStep.refl 𝟭, MultiStep.refl 𝟭⟩
  | Step.mulZeroR _, Step.mulZeroL _ => ⟨𝟬, MultiStep.refl 𝟬, MultiStep.refl 𝟬⟩
  | Step.mulZeroL _, Step.mulZeroR _ => ⟨𝟬, MultiStep.refl 𝟬, MultiStep.refl 𝟬⟩
  | Step.mulOneR _, Step.mulZeroL _ => ⟨𝟬, MultiStep.refl 𝟬, MultiStep.refl 𝟬⟩
  | Step.mulZeroL _, Step.mulOneR _ => ⟨𝟬, MultiStep.refl 𝟬, MultiStep.refl 𝟬⟩
  | Step.mulOneL _, Step.mulZeroR _ => ⟨𝟬, MultiStep.refl 𝟬, MultiStep.refl 𝟬⟩
  | Step.mulZeroR _, Step.mulOneL _ => ⟨𝟬, MultiStep.refl 𝟬, MultiStep.refl 𝟬⟩
  -- Base rule vs congruence: join by applying base rule after congruence
  | Step.addZeroR _, Step.addL h => ⟨_, MultiStep.single h, MultiStep.single (Step.addZeroR _)⟩
  | Step.addZeroR _, Step.addR h => absurd h (zero_normal _)
  | Step.addZeroL _, Step.addL h => absurd h (zero_normal _)
  | Step.addZeroL _, Step.addR h => ⟨_, MultiStep.single h, MultiStep.single (Step.addZeroL _)⟩
  | Step.mulOneR _, Step.mulL h => ⟨_, MultiStep.single h, MultiStep.single (Step.mulOneR _)⟩
  | Step.mulOneR _, Step.mulR h => absurd h (one_normal _)
  | Step.mulOneL _, Step.mulL h => absurd h (one_normal _)
  | Step.mulOneL _, Step.mulR h => ⟨_, MultiStep.single h, MultiStep.single (Step.mulOneL _)⟩
  | Step.mulZeroR _, Step.mulL _ => ⟨𝟬, MultiStep.refl 𝟬, MultiStep.single (Step.mulZeroR _)⟩
  | Step.mulZeroR _, Step.mulR h => absurd h (zero_normal _)
  | Step.mulZeroL _, Step.mulL h => absurd h (zero_normal _)
  | Step.mulZeroL _, Step.mulR _ => ⟨𝟬, MultiStep.refl 𝟬, MultiStep.single (Step.mulZeroL _)⟩
  -- Symmetric: congruence vs base rule
  | Step.addL h, Step.addZeroR _ => ⟨_, MultiStep.single (Step.addZeroR _), MultiStep.single h⟩
  | Step.addL h, Step.addZeroL _ => absurd h (zero_normal _)
  | Step.addR h, Step.addZeroR _ => absurd h (zero_normal _)
  | Step.addR h, Step.addZeroL _ => ⟨_, MultiStep.single (Step.addZeroL _), MultiStep.single h⟩
  | Step.mulL h, Step.mulOneR _ => ⟨_, MultiStep.single (Step.mulOneR _), MultiStep.single h⟩
  | Step.mulL h, Step.mulOneL _ => absurd h (one_normal _)
  | Step.mulL _, Step.mulZeroR _ => ⟨𝟬, MultiStep.single (Step.mulZeroR _), MultiStep.refl 𝟬⟩
  | Step.mulL h, Step.mulZeroL _ => absurd h (zero_normal _)
  | Step.mulR h, Step.mulOneR _ => absurd h (one_normal _)
  | Step.mulR h, Step.mulOneL _ => ⟨_, MultiStep.single (Step.mulOneL _), MultiStep.single h⟩
  | Step.mulR h, Step.mulZeroR _ => absurd h (zero_normal _)
  | Step.mulR _, Step.mulZeroL _ => ⟨𝟬, MultiStep.single (Step.mulZeroL _), MultiStep.refl 𝟬⟩
  -- Congruence vs congruence: different positions (parallel)
  | Step.addL h1, Step.addR h2 => ⟨_ ⊕ _, MultiStep.single (Step.addR h2), MultiStep.single (Step.addL h1)⟩
  | Step.addR h1, Step.addL h2 => ⟨_ ⊕ _, MultiStep.single (Step.addL h2), MultiStep.single (Step.addR h1)⟩
  | Step.mulL h1, Step.mulR h2 => ⟨_ ⊛ _, MultiStep.single (Step.mulR h2), MultiStep.single (Step.mulL h1)⟩
  | Step.mulR h1, Step.mulL h2 => ⟨_ ⊛ _, MultiStep.single (Step.mulL h2), MultiStep.single (Step.mulR h1)⟩
  -- Congruence vs congruence: same position (recursive)
  | Step.addL h1, Step.addL h2 =>
    let ⟨e', h1', h2'⟩ := local_confluent _ _ _ h1 h2
    ⟨e' ⊕ _, MultiStep.addL h1', MultiStep.addL h2'⟩
  | Step.addR h1, Step.addR h2 =>
    let ⟨e', h1', h2'⟩ := local_confluent _ _ _ h1 h2
    ⟨_ ⊕ e', MultiStep.addR h1', MultiStep.addR h2'⟩
  | Step.mulL h1, Step.mulL h2 =>
    let ⟨e', h1', h2'⟩ := local_confluent _ _ _ h1 h2
    ⟨e' ⊛ _, MultiStep.mulL h1', MultiStep.mulL h2'⟩
  | Step.mulR h1, Step.mulR h2 =>
    let ⟨e', h1', h2'⟩ := local_confluent _ _ _ h1 h2
    ⟨_ ⊛ e', MultiStep.mulR h1', MultiStep.mulR h2'⟩
termination_by structural h1

/-! ## Main Theorem: Confluence

By Newman's lemma, since the system is terminating and locally confluent,
it is confluent.
-/

/-- The simple expression rewriting system is confluent -/
theorem confluent : Rewriting.Confluent Step :=
  Rewriting.confluent_of_terminating_localConfluent step_terminating local_confluent

/-- Every expression has a unique normal form (by termination + confluence). -/
theorem existsUnique_normalForm (e : Expr) :
    ∃ n, e ⟶* n ∧ Rewriting.IsNormalForm Step n ∧
      ∀ n', e ⟶* n' ∧ Rewriting.IsNormalForm Step n' → n' = n :=
  Rewriting.existsUnique_normalForm_of_terminating_confluent step_terminating confluent e

/-! ## Multi-Step and Normal Forms -/

/-- Church-Rosser property for simple expressions -/
theorem church_rosser {e e₁ e₂ : Expr} (h1 : e ⟶* e₁) (h2 : e ⟶* e₂) :
    ∃ e', (e₁ ⟶* e') ∧ (e₂ ⟶* e') :=
  confluent e e₁ e₂ h1 h2

/-- Normal forms are unique -/
theorem normal_unique {e n₁ n₂ : Expr}
    (h1 : e ⟶* n₁) (h2 : e ⟶* n₂)
    (hn1 : IsNormal n₁) (hn2 : IsNormal n₂) : n₁ = n₂ := by
  have hn1' : Rewriting.IsNormalForm Step n₁ := fun e h => hn1 e h
  have hn2' : Rewriting.IsNormalForm Step n₂ := fun e h => hn2 e h
  exact Rewriting.normalForm_unique confluent h1 h2 hn1' hn2'

/-! ## Summary

This module demonstrates the use of Newman's lemma for proving confluence.

**Key differences from lambda calculus**:
- Lambda: Uses diamond property of parallel reduction
- TRS: Uses Newman's lemma (termination + local confluence)

Both approaches are captured by the generic rewriting framework,
showing its flexibility and generality.

**Proof structure**:
1. Termination: Proven via size measure (each rule reduces size)
2. Local confluence: Proven by exhaustive case analysis on critical pairs
3. Confluence: Immediate from Newman's lemma
-/

end Metatheory.TRS
