# Proof Techniques in Metatheory

This document provides detailed explanations of the proof techniques used in the Metatheory library.

## Table of Contents

1. [Diamond Property and Parallel Reduction](#1-diamond-property-and-parallel-reduction)
2. [Newman's Lemma](#2-newmans-lemma)
3. [Hindley-Rosen Lemma](#3-hindley-rosen-lemma)
4. [Decreasing Diagrams](#4-decreasing-diagrams)
5. [Logical Relations (Tait's Method)](#5-logical-relations-taits-method)

---

## 1. Diamond Property and Parallel Reduction

### The Problem

The Church-Rosser theorem states that β-reduction is confluent:

```
If M →* N₁ and M →* N₂, then ∃P such that N₁ →* P and N₂ →* P
```

However, single-step β-reduction does **not** have the diamond property. Consider:

```
    (λx.xx)(λy.y)
       /        \
      ↓          ↓
(λy.y)(λy.y)   (λx.xx)(λy.y)  -- Different redexes contracted
      |              |
      ↓              ↓
    λy.y        (λy.y)(λy.y)
                     |
                     ↓
                   λy.y
```

The divergence takes multiple steps to close, not one.

### The Solution: Parallel Reduction

Define a relation that contracts **any subset** of redexes simultaneously:

```lean
inductive ParRed : Term → Term → Prop where
  | var  : ParRed (var n) (var n)
  | app  : ParRed M M' → ParRed N N' → ParRed (app M N) (app M' N')
  | lam  : ParRed M M' → ParRed (lam M) (lam M')
  | beta : ParRed M M' → ParRed N N' → ParRed (app (lam M) N) (M'[N'])
```

Key properties:
- Reflexive: `M ⇒ M` (contract zero redexes)
- Contains β: `M → N` implies `M ⇒ N`
- `M ⇒* N` iff `M →* N`

### Complete Development

The **complete development** contracts ALL redexes:

```lean
def complete : Term → Term
  | var n => var n
  | lam M => lam (complete M)
  | app (lam M) N => (complete M)[complete N]  -- Contract the redex!
  | app M N => app (complete M) (complete N)
```

### The Key Lemma

```lean
theorem parRed_complete : M ⇒ N → N ⇒ complete M
```

This says: no matter which redexes you contract (getting N), you can always reach the complete development.

### Diamond Property Follows

```
        M
       / \
      ⇒   ⇒
     /     \
    N₁     N₂
     \     /
      ⇒   ⇒
       \ /
    complete(M)
```

Since `N₁ ⇒ complete(M)` and `N₂ ⇒ complete(M)`, we have the diamond!

### Files

- `Lambda/Parallel.lean`: ParRed definition
- `Lambda/Complete.lean`: Complete development
- `Lambda/Diamond.lean`: Diamond property proof

---

## 2. Newman's Lemma

### Statement

For **terminating** relations:

```
Terminating + LocalConfluent → Confluent
```

Where:
- **Terminating**: No infinite reduction sequences
- **LocalConfluent**: One-step divergences can be closed (possibly in multiple steps)

### Why Termination Matters

Without termination, local confluence doesn't imply confluence:

```
     a
    / \
   ↓   ↓
   b   c
   |   |
   ↓   ↓
   a   a    -- Both reduce back to a!
```

This is locally confluent (b and c both reach a) but not confluent in general.

### Proof Strategy

The proof uses well-founded induction on the termination ordering:

1. Take a divergence: `a →* b` and `a →* c`
2. By termination, we can induct on `a`
3. If the divergence is trivial (a = b or a = c), done
4. Otherwise, use local confluence on the first steps
5. Apply IH to close the remaining diagram

### Implementation

```lean
theorem confluent_of_terminating_localConfluent
    {r : α → α → Prop}
    (hterm : Terminating r)
    (hlocal : LocalConfluent r) :
    Confluent r := by
  intro a b c hab hac
  -- Well-founded induction on a
  induction hterm a with
  | intro a ha ih =>
    -- Case analysis on the reductions...
```

### Application: TRS

For the simple TRS with rules like `0 + x → x`:

1. **Termination**: Prove via size measure (each step reduces expression size)
2. **Local confluence**: Check all critical pairs (overlapping rule applications)
3. **Apply Newman's lemma**: Get full confluence

### Files

- `Rewriting/Newman.lean`: Newman's lemma
- `TRS/Confluence.lean`: Application to TRS
- `StringRewriting/Confluence.lean`: Application with critical pairs

---

## 3. Hindley-Rosen Lemma

### Statement

```lean
theorem confluent_union :
    Confluent r → Confluent s → Commute r s → Confluent (Union r s)
```

Where `Commute r s` means: if `a →r b` and `a →s c`, then ∃d with `b →s* d` and `c →r* d`.

### Intuition

If you have two confluent relations that "play well together" (commute), their union is also confluent.

```
        a
       /|\
      r s r
     / | \
    b  c  d
    |  |  |
    s* r* s*
    |  |  |
    e  e  e
```

### Application

Useful when you have multiple reduction rules that are independent (e.g., different evaluation strategies).

### Files

- `Rewriting/HindleyRosen.lean`

---

## 4. Decreasing Diagrams

### The Idea (van Oostrom)

Label each reduction step and require that when closing diagrams, the labels "decrease":

```
      a
     /l\
    ↓   ↓
   b     c
    \   /
   <l  <l     -- Labels strictly less than l
     \ /
      d
```

This ensures the closing process terminates.

### Statement

```lean
theorem confluent_of_locallyDecreasing
    (hwf : WellFounded lt)
    (hld : LocallyDecreasing r lt) :
    Confluent (LabeledUnion r)
```

### Files

- `Rewriting/DecreasingDiagrams.lean`

---

## 5. Logical Relations (Tait's Method)

### Goal

Prove strong normalization for STLC:

```lean
theorem strong_normalization : HasType Γ M A → SN M
```

### The Problem

Direct structural induction doesn't work because:
- In `app M N`, the type of M is `A → B`, which is **larger** than `B`
- We can't apply IH directly

### The Solution: Reducibility

Define a predicate `Reducible A M` by induction on **types**:

```lean
def Reducible : Ty → Term → Prop
  | base n, M => SN M
  | arr A B, M => ∀ N, Reducible A N → Reducible B (app M N)
```

Key insight: For arrow types, we quantify over **all** reducible arguments.

### Reducibility Conditions (CR1-CR3)

These are proved by induction on types:

1. **CR1**: `Reducible A M → SN M`
   - Base: trivial (Reducible = SN)
   - Arrow: Apply M to a reducible term, use IH

2. **CR2**: `Reducible A M → M → N → Reducible A N`
   - Reducibility is closed backward under reduction

3. **CR3**: `Neutral M → (∀N, M → N → Reducible A N) → Reducible A M`
   - Neutral terms with reducible reducts are reducible

### Fundamental Lemma

```lean
theorem fundamental_lemma :
    HasType Γ M A →
    (∀ n A, Γ.get? n = some A → Reducible A (σ n)) →
    Reducible A (applySubst σ M)
```

If M is well-typed and σ maps variables to reducible terms, then M[σ] is reducible.

### Proof of Strong Normalization

1. Take well-typed term: `HasType Γ M A`
2. Use identity substitution (which is reducible by CR3 on variables)
3. By fundamental lemma: `Reducible A M`
4. By CR1: `SN M`

### The Hard Part: Beta Redexes

The trickiest case is showing `(λM) N` is reducible when M[N] is reducible.

This requires a complex induction on:
- SN M (the body)
- SN N (the argument)
- For arrow types: SN P (any additional argument)

### Files

- `STLC/Normalization.lean`: Full proof

---

## Summary

| Technique | When to Use | Key Idea |
|-----------|-------------|----------|
| **Parallel Reduction** | Non-terminating systems (λ-calculus) | Contract multiple redexes simultaneously |
| **Newman's Lemma** | Terminating systems (TRS) | Local confluence + termination → confluence |
| **Hindley-Rosen** | Union of independent relations | Commuting confluent relations |
| **Decreasing Diagrams** | Labeled reductions | Labels decrease when closing diagrams |
| **Logical Relations** | Normalization proofs | Induction on types, not terms |

---

## Further Reading

1. Takahashi (1995) - Original parallel reduction paper
2. Barendregt (1984) - Chapter 3 on Church-Rosser
3. Terese (2003) - Comprehensive treatment of term rewriting
4. Girard et al. (1989) - Chapter 6 on normalization
