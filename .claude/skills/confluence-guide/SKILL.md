---
name: confluence-guide
description: Guide for proving confluence of a rewriting system. Use when asked to prove Church-Rosser or confluence properties.
---

# Proving Confluence

This skill provides guidance for proving confluence of rewriting systems in the Metatheory project.

## Choose Your Approach

### Option 1: Diamond Property (for systems like Lambda, CL)

Best when: The reduction relation has an obvious "parallel" version.

1. **Define parallel reduction** that contracts multiple redexes simultaneously:
   ```lean
   inductive ParRed : Term → Term → Prop where
     | var : ParRed (var n) (var n)
     | app : ParRed M M' → ParRed N N' → ParRed (app M N) (app M' N')
     | lam : ParRed M M' → ParRed (lam M) (lam M')
     | beta : ParRed M M' → ParRed N N' → ParRed (app (lam M) N) (M'[N'])
   ```

2. **Define complete development** that contracts ALL redexes:
   ```lean
   def complete : Term → Term
   ```

3. **Prove the key lemma**: any parallel reduction reaches complete development:
   ```lean
   theorem parRed_complete : M ⇒ N → N ⇒ complete M
   ```

4. **Diamond property follows** from the triangle:
   ```lean
   theorem parRed_diamond : Rewriting.Diamond ParRed
   ```

5. **Apply generic theorem**:
   ```lean
   theorem confluent : Confluent BetaRed :=
     confluent_of_diamond parRed_diamond
   ```

### Option 2: Newman's Lemma (for terminating systems like TRS)

Best when: You can prove termination via a well-founded measure.

1. **Prove termination** via a decreasing measure:
   ```lean
   theorem step_terminating : Rewriting.Terminating Step := by
     apply terminating_of_measure size
     intro a b h
     exact step_decreases_size h
   ```

2. **Prove local confluence** by critical pair analysis:
   ```lean
   theorem local_confluent : LocalConfluent Step := by
     intro a b c hab hac
     -- Analyze all critical pairs
     cases hab <;> cases hac <;> ...
   ```

3. **Apply Newman's lemma**:
   ```lean
   theorem confluent : Confluent Step :=
     confluent_of_terminating_localConfluent step_terminating local_confluent
   ```

### Option 3: Hindley-Rosen (for unions of relations)

Best when: You have two confluent relations that commute.

```lean
theorem confluent_union : Confluent r → Confluent s → Commute r s → Confluent (Union r s)
```

## Key Imports

```lean
import Metatheory.Rewriting.Basic
import Metatheory.Rewriting.Diamond
import Metatheory.Rewriting.Newman
import Metatheory.Rewriting.HindleyRosen
```

## Examples in This Repo

- `Lambda/Confluence.lean` - Diamond property approach
- `CL/Confluence.lean` - Diamond property approach
- `TRS/Confluence.lean` - Newman's lemma approach
- `StringRewriting/Confluence.lean` - Newman's lemma approach
