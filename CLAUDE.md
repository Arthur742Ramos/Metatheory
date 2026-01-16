# Claude Code Instructions for Metatheory

## Project Overview

**Metatheory** is a comprehensive **programming language foundations library for Lean 4** covering:

- Generic abstract rewriting systems (confluence, termination)
- Lambda calculus and combinatory logic
- Simply typed lambda calculus with strong normalization
- Multiple proof techniques for the Church-Rosser property

### Case Studies

| System | Technique | Key Property |
|--------|-----------|--------------|
| **Lambda Calculus** | Parallel reduction + Complete development | Diamond property |
| **Combinatory Logic** | Parallel reduction | Diamond property |
| **Simple TRS** | Size measure + Critical pair analysis | Termination + Local confluence |
| **String Rewriting** | Length measure + Critical pairs | Termination + Local confluence |
| **STLC** | Logical relations (Tait's method) | Strong normalization |

### Framework Layers

1. **Rewriting/** - Generic abstract rewriting system (ARS) framework
2. **Lambda/** - Lambda calculus Church-Rosser theorem (via diamond property)
3. **CL/** - Combinatory Logic Church-Rosser theorem (via diamond property)
4. **TRS/** - Simple expression rewriting (via Newman's lemma)
5. **StringRewriting/** - String rewriting (via Newman's lemma)
6. **STLC/** - Simply typed lambda calculus (subject reduction + strong normalization)
7. **STLCext/** - STLC with products/sums (parallel reduction + confluence)
8. **STLCextBool/** - STLC with booleans, erased into `STLCext`

The framework demonstrates multiple approaches to proving confluence:

- **Diamond property approach**: Used for lambda calculus and CL via parallel reduction
- **Newman's lemma approach**: Used for terminating systems via local confluence
- **Hindley-Rosen lemma**: Union of commuting confluent relations
- **Decreasing diagrams**: Definitions provided (LabeledARS, LocallyDecreasing); theorem requires additional infrastructure

## CRITICAL: No Sorrys Allowed

**`sorry` is NEVER acceptable in this codebase.** Every theorem must be fully proven.

If a proof is difficult:
1. Break it into smaller lemmas
2. Use helper functions or auxiliary definitions
3. Simplify the statement if the current formulation is unprovable
4. Axiomatize standard results with clear references

## Project Structure

```
Metatheory/
├── Rewriting/           # Generic ARS framework (Layer 0)
│   ├── Basic.lean       # Core definitions: Star, Plus, Joinable, Diamond, Confluent
│   ├── Diamond.lean     # Diamond property implies confluence
│   ├── Newman.lean      # Newman's lemma (termination + local confluence → confluence)
│   ├── HindleyRosen.lean # Union of commuting confluent relations
│   ├── DecreasingDiagrams.lean # van Oostrom's decreasing diagrams
│   └── Compat.lean      # Mathlib-style compatibility layer
├── Lambda/              # Lambda calculus case study (Layer 1a)
│   ├── Term.lean        # De Bruijn indexed terms, substitution
│   ├── Beta.lean        # Single-step β-reduction
│   ├── MultiStep.lean   # Multi-step reduction
│   ├── Parallel.lean    # Parallel reduction
│   ├── Complete.lean    # Complete development (Takahashi method)
│   ├── Diamond.lean     # Diamond property for ParRed
│   ├── Confluence.lean  # Main Church-Rosser theorem
│   └── Generic.lean     # Bridge to generic framework
├── CL/                  # Combinatory Logic case study (Layer 1b)
│   ├── Syntax.lean      # S, K combinators, term syntax
│   ├── Reduction.lean   # Weak reduction rules
│   ├── Parallel.lean    # Parallel reduction
│   └── Confluence.lean  # Church-Rosser via diamond property
├── TRS/                 # Simple TRS case study (Layer 2a)
│   ├── Syntax.lean      # Expression syntax
│   ├── Rules.lean       # Rewriting rules
│   └── Confluence.lean  # Confluence via Newman's lemma
├── StringRewriting/     # String rewriting case study (Layer 2b)
│   ├── Syntax.lean      # Alphabet and strings
│   ├── Rules.lean       # Idempotent reduction rules
│   └── Confluence.lean  # Confluence via Newman's lemma
└── STLC/                # Simply Typed Lambda Calculus (Layer 3)
    ├── Types.lean       # Simple types (base + arrow)
    ├── Terms.lean       # Re-exports untyped terms
    ├── Typing.lean      # Typing relation, subject reduction
    └── Normalization.lean # Strong normalization via logical relations
```

## Build Commands

```bash
lake build              # Build the project
lake clean              # Clean build artifacts
```

## Aristotle Integration (Automated Theorem Proving)

[Aristotle](https://aristotle.harmonic.fun) is an AI-powered theorem prover for Lean 4 that can automatically fill `sorry` placeholders.

### Quick Start

```bash
# Set API key (add to ~/.bashrc for persistence)
export ARISTOTLE_API_KEY='arstl_YOUR_KEY_HERE'

# Run Aristotle
uvx --from aristotlelib aristotle.exe prove-from-file "path/to/file.lean"
```

### CLI Options

```bash
uvx --from aristotlelib aristotle.exe prove-from-file <input_file> [options]

Options:
  --api-key KEY              API key (overrides environment variable)
  --output-file FILE         Output path (default: <input>_aristotle.lean)
  --no-auto-add-imports      Disable automatic import resolution
  --context-files FILE...    Additional context files
  --no-wait                  Submit job without waiting
  --silent                   Suppress console output
```

### Usage with This Project

Given the "No Sorrys Allowed" policy, Aristotle is useful for:

1. **Development workflow** - Fill sorries before committing
2. **Proof exploration** - See what tactics Aristotle suggests
3. **Verification** - Confirm automated provers can handle certain goals

### Proof Hints

Guide Aristotle with `PROVIDED SOLUTION` in docstrings:

```lean
/--
Prove confluence via diamond property.

PROVIDED SOLUTION
Use the diamond property theorem from Rewriting.Diamond.
First show that parallel reduction has the diamond property,
then apply confluent_of_diamond.
-/
theorem confluent : Confluent BetaRed := by
  sorry
```

### Best Practices

1. **Check version compatibility** - Review Aristotle output for 4.24.0-specific tactics
2. **Build locally** - Always verify proofs compile with `lake build`
3. **Adapt as needed** - Replace incompatible tactics manually
4. **Commit only complete proofs** - Per project policy, no sorries in commits

## Key Theorems

### Generic Framework (Rewriting/)

```lean
-- Diamond property implies confluence
theorem confluent_of_diamond : Diamond r → Confluent r

-- Newman's lemma
theorem confluent_of_terminating_localConfluent :
    Terminating r → LocalConfluent r → Confluent r

-- Hindley-Rosen lemma
theorem confluent_union : Confluent r → Confluent s → Commute r s → Confluent (Union r s)

-- Decreasing diagrams: definitions available (LabeledARS, LocallyDecreasing, StarPred)
-- A front-building closure is available as `Rewriting.StarHead`, but the main theorem is still future work

-- Termination implies existence of normal forms
theorem hasNormalForm_of_terminating : Terminating r → ∀ a, HasNormalForm r a

-- Termination + confluence gives a unique normal form
theorem existsUnique_normalForm_of_terminating_confluent :
    Terminating r → Confluent r → ∀ a, ∃ n, Star r a n ∧ IsNormalForm r n ∧ (∀ n', ... → n' = n)
```

### Lambda Calculus (Lambda/)

```lean
-- Church-Rosser theorem
theorem confluence {M N₁ N₂ : Term} (h1 : M →* N₁) (h2 : M →* N₂) :
    ∃ P, (N₁ →* P) ∧ (N₂ →* P)

-- ParRed has diamond property
theorem parRed_diamond : Rewriting.Diamond ParRed
```

### Simply Typed Lambda Calculus (STLC/)

```lean
-- Subject reduction (type preservation)
theorem subject_reduction : HasType Γ M A → BetaStep M N → HasType Γ N A

-- Strong normalization
theorem strong_normalization : HasType Γ M A → SN M
```

### Extended STLC (STLCext/)

```lean
-- Parallel reduction and confluence
-- confluence : (M ⟶* N₁) → (M ⟶* N₂) → ∃ P, (N₁ ⟶* P) ∧ (N₂ ⟶* P)
```

### STLC with Booleans (STLCextBool/)

```lean
-- Erase booleans into sums of unit in STLCext
-- (ttrue ↦ inl unit, tfalse ↦ inr unit, ite ↦ case)

-- Typing preservation under erasure
theorem erase_typing : Γ ⊢ M : A → eraseCtx Γ ⊢ erase M : eraseTy A

-- Strong normalization via STLCext normalization
theorem strong_normalization : Γ ⊢ M : A → STLCext.SN (erase M)

-- Example: erase (if true then false else true)
-- erase (ite ttrue tfalse ttrue) = case (inl unit) (shift1 (inr unit)) (shift1 (inl unit))
```


## Proof Techniques Demonstrated

### 1. Diamond Property Approach (Lambda, CL)

```lean
-- Parallel reduction
inductive ParRed : Term → Term → Prop where
  | var : ParRed (var n) (var n)
  | app : ParRed M M' → ParRed N N' → ParRed (app M N) (app M' N')
  | lam : ParRed M M' → ParRed (lam M) (lam M')
  | beta : ParRed M M' → ParRed N N' → ParRed (app (lam M) N) (M'[N'])

-- Complete development (contracts all redexes)
def complete : Term → Term

-- Key lemma: any parallel reduction reaches complete development
theorem parRed_complete : M ⇒ N → N ⇒ complete M

-- Diamond property follows
theorem parRed_diamond : Rewriting.Diamond ParRed
```

### 2. Newman's Lemma Approach (TRS, StringRewriting)

```lean
-- Termination via size/length measure
theorem step_terminating : Rewriting.Terminating Step

-- Local confluence by critical pair analysis
theorem local_confluent : LocalConfluent Step

-- Confluence via Newman's lemma
theorem confluent : Rewriting.Confluent Step :=
  confluent_of_terminating_localConfluent step_terminating local_confluent
```

### 3. Logical Relations / Tait's Method (STLC)

```lean
-- Reducibility predicate
def Reducible : Ty → Term → Prop
  | base _, M => SN M
  | arr A B, M => ∀ N, Reducible A N → Reducible B (app M N)

-- Fundamental lemma
theorem fundamental_lemma : HasType Γ M A → ... → Reducible A (applySubst σ M)

-- Strong normalization follows
theorem strong_normalization : HasType Γ M A → SN M
```

## Code Style

### Lean 4 Conventions
- Prefer `theorem` for Prop-valued results, `def` for data
- Use docstrings (`/-- ... -/`) for public definitions
- Group related definitions with `/-! ## Section Name -/`

## Proof Status

**All theorems are fully proved with ZERO sorries.**

### Decreasing Diagrams (Future Work)
The decreasing diagrams theorem (`confluent_of_locallyDecreasing`) is not included because
it is easiest with a "front-building" Star type that constructs paths from the START rather than
the END. The current `Star` type uses `tail : Star r a b → r b c → Star r a c`, but the
LocallyDecreasing property needs access to the FIRST step of a path.

All definitions are available (`LabeledARS`, `LocallyDecreasing`, `StarPred`) for future work,
and the needed front-building closure is now available as `Rewriting.StarHead`.
All main confluence results use alternative techniques (diamond property, Newman's lemma).

## Fully Proved Lemmas

### Lambda Calculus (de Bruijn infrastructure)
All de Bruijn substitution lemmas are now **fully proved**:
- `shift_zero` - Shifting by 0 is identity
- `shift_shift` - Composing shifts at same cutoff
- `shift_shift_comm` - Shift commutation at different cutoffs
- `shift_shift_succ` - shift 1 (c+1) (shift 1 c M) = shift 2 c M
- `shift_shift_offset` - shift 1 (c+b) (shift c b N) = shift (c+1) b N
- `shift_subst_at` - Generalized shift-substitution interaction
- `shift_subst` - Shift-substitution interaction at cutoff 0
- `subst_shift_cancel` - Substitution after shift cancels
- **`subst_subst_gen`** - **Substitution composition (KEY LEMMA, ~90 lines)**
  - Proved via generalized `subst_subst_gen_full` with level parameter

### STLC (Normalization)
- **`reducible_app_lam`** - Beta redexes are reducible (~108 lines)
  - Full proof using CR properties and reducibility preservation

### Combinatory Logic
- **`parRed_complete`** - Parallel reduction reaches complete development
  - Full proof using Takahashi's method

## References

### Core Papers
- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
- Newman, "On Theories with a Combinatorial Definition of Equivalence" (1942)
- Knuth & Bendix, "Simple Word Problems in Universal Algebras" (1970)
- Huet, "Confluent Reductions: Abstract Properties and Applications" (1980)
- Hindley, "An Abstract Church-Rosser Theorem" (1969)
- van Oostrom, "Confluence for Abstract and Higher-Order Rewriting" (1994)
- Tait, "Intensional Interpretations of Functionals" (1967)

### Books
- Barendregt, "The Lambda Calculus: Its Syntax and Semantics"
- Terese, "Term Rewriting Systems" (2003)
- Hindley & Seldin, "Lambda-Calculus and Combinators" (2008)
- Pierce et al., "Software Foundations" (Vol 2: PLF)
- Girard, Lafont & Taylor, "Proofs and Types" (1989)

### Other Formalizations
- Isabelle/HOL: Nominal Isabelle Church-Rosser proof
- CoLoR (Coq): Certified termination and confluence proofs
- Agda: Various de Bruijn formalizations
- PVS: Term rewriting formalization
