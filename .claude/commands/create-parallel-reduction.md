# Create Parallel Reduction

Define parallel reduction for a term language to prove Church-Rosser via the diamond property.

## Arguments
- $ARGUMENTS: The term language/rewriting system to create parallel reduction for

## Instructions

1. **Understand the term language** from: $ARGUMENTS

2. **Design parallel reduction**

Parallel reduction `M ⇒ N` should:
- Allow reducing ZERO or MORE redexes simultaneously
- Be reflexive (include identity reductions)
- Contract redexes in parallel, not sequentially

### Standard Pattern

```lean
/-- Parallel reduction: contract zero or more redexes simultaneously -/
inductive ParRed : Term → Term → Prop where
  | var : ParRed (var n) (var n)
  | app : ParRed M M' → ParRed N N' → ParRed (app M N) (app M' N')
  | lam : ParRed M M' → ParRed (lam M) (lam M')
  | beta : ParRed M M' → ParRed N N' →
           ParRed (app (lam M) N) (M'[N'])  -- Key: reduce + contract
```

Key insight: The `beta` case allows:
- Reducing M to M' (in parallel)
- Reducing N to N' (in parallel)
- THEN contracting the beta redex

3. **Define complete development**

Complete development `complete M` contracts ALL redexes in M:

```lean
/-- Complete development: contract ALL redexes -/
def complete : Term → Term
  | var n => var n
  | app (lam M) N => (complete M)[(complete N)]  -- Contract redex
  | app M N => app (complete M) (complete N)      -- No redex at root
  | lam M => lam (complete M)
```

4. **Prove key lemmas**

### Lemma: ParRed is reflexive
```lean
theorem parRed_refl : ∀ M, ParRed M M
```

### Lemma: Parallel reduction reaches complete development
```lean
theorem parRed_complete : M ⇒ N → N ⇒ complete M
```

This is THE key lemma. Proof by induction on ParRed derivation.
The `beta` case requires substitution lemmas.

### Lemma: Diamond property
```lean
theorem parRed_diamond : Rewriting.Diamond ParRed := by
  intro M M₁ M₂ h1 h2
  exact ⟨complete M, parRed_complete h1, parRed_complete h2⟩
```

5. **Bridge to single-step reduction**

```lean
theorem step_implies_parRed : Step M N → ParRed M N

theorem parRed_implies_star : ParRed M N → Star Step M N
```

6. **Apply generic framework**

```lean
theorem confluent : Rewriting.Confluent Step := by
  -- Use: confluent_of_diamond on ParRed
  -- Then bridge back to Step
```

## Example: Lambda Calculus

See `Metatheory/Lambda/Parallel.lean` and `Metatheory/Lambda/Complete.lean` for the full implementation.

## Checklist

- [ ] ParRed inductive definition
- [ ] complete function (total, terminating)
- [ ] parRed_refl lemma
- [ ] parRed_complete lemma (the hard one)
- [ ] parRed_diamond theorem
- [ ] Bridge lemmas to/from single-step
- [ ] Final confluence theorem
- [ ] All proofs complete (no sorry)
- [ ] Builds successfully
