# Getting Started with Metatheory

This guide will help you get started with the Metatheory library.

## Prerequisites

- Basic familiarity with Lean 4 syntax
- Understanding of lambda calculus concepts (optional but helpful)

## Installation

```bash
git clone https://github.com/Arthur742Ramos/Metatheory.git
cd Metatheory
lake build
```

## Your First Proof

Let's prove that β-reduction preserves some properties. Create a new file `MyProofs.lean`:

```lean
import Metatheory

open Metatheory.Lambda
open Rewriting

-- The Church-Rosser theorem is already proved!
-- Let's use it:

example {M N₁ N₂ : Term} (h1 : MultiStep M N₁) (h2 : MultiStep M N₂) :
    ∃ P, MultiStep N₁ P ∧ MultiStep N₂ P :=
  confluence h1 h2
```

## Understanding De Bruijn Indices

In Metatheory, lambda terms use de Bruijn indices instead of named variables:

```lean
-- Named notation:     λx. λy. x y
-- De Bruijn notation: λ. λ. (var 1) (var 0)
--                          ↑        ↑
--                          │        └── bound by inner λ (distance 0)
--                          └── bound by outer λ (distance 1)

open Term

def example_term : Term := lam (lam (app (var 1) (var 0)))

-- Using notation:
def example_term' : Term := ƛ (ƛ (var 1 @ var 0))
```

### Why De Bruijn?

1. **No α-equivalence**: `λx.x` and `λy.y` are literally equal (`ƛ (var 0)`)
2. **Capture-avoiding substitution**: Built into the definition
3. **Decidable equality**: `Term` derives `DecidableEq`

## Working with the Generic Framework

The rewriting framework is parameterized over any relation:

```lean
import Metatheory.Rewriting.Basic
import Metatheory.Rewriting.Diamond

open Rewriting

-- Define your own relation
inductive MyStep : Nat → Nat → Prop where
  | dec : n > 0 → MyStep n (n - 1)

-- Prove properties using the generic framework
example : Terminating MyStep := by
  intro n
  induction n with
  | zero =>
    constructor
    intro m hm
    cases hm
    omega
  | succ n ih =>
    constructor
    intro m hm
    cases hm with
    | dec h =>
      simp at *
      exact ih
```

## The Module Structure

```
Metatheory/
├── Rewriting/     ← Generic framework (start here for foundations)
├── Lambda/        ← Untyped lambda calculus
├── CL/            ← Combinatory logic
├── TRS/           ← Term rewriting
├── StringRewriting/
└── STLC/          ← Simply typed lambda calculus
```

### Recommended Reading Order

1. **`Rewriting/Basic.lean`**: Core definitions (Star, Diamond, Confluent)
2. **`Rewriting/Diamond.lean`**: Diamond → Confluence proof
3. **`Lambda/Term.lean`**: De Bruijn terms
4. **`Lambda/Beta.lean`**: β-reduction
5. **`Lambda/Parallel.lean`**: Parallel reduction
6. **`Lambda/Confluence.lean`**: Church-Rosser

## Common Patterns

### Using Multi-step Reduction

```lean
open Rewriting

-- Build multi-step reductions
example {M N P : Term} (h1 : BetaStep M N) (h2 : MultiStep N P) :
    MultiStep M P :=
  Star.head h1 h2

-- Transitivity
example {M N P : Term} (h1 : MultiStep M N) (h2 : MultiStep N P) :
    MultiStep M P :=
  Star.trans h1 h2
```

### Working with Substitution

```lean
open Term

-- M[N] means "substitute N for variable 0 in M"
-- Example: (var 0)[I] = I  where I = λx.x

example : (var 0)[I] = I := rfl

-- Substitution under lambda needs shifting:
-- (λ. var 0)[N] = λ. var 0  (var 0 is bound, not substituted)
```

## Tips

1. **Use `open` wisely**: `open Metatheory.Lambda` imports Term, BetaStep, etc.
2. **Check the types**: Use `#check @confluence` to see theorem signatures
3. **Read the docstrings**: Hover over definitions in VS Code
4. **Start with examples**: Look at existing proofs before writing your own

## Next Steps

- Read [Proof Techniques](proof-techniques.md) for detailed explanations
- Explore the source files for examples
- Try extending the library with new results!

## Getting Help

- Open an issue on GitHub for bugs or questions
- Check the references in README for background reading
