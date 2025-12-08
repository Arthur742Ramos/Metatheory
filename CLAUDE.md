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

The framework demonstrates multiple approaches to proving confluence:
- **Diamond property approach**: Used for lambda calculus and CL via parallel reduction
- **Newman's lemma approach**: Used for terminating systems via local confluence
- **Hindley-Rosen lemma**: Union of commuting confluent relations
- **Decreasing diagrams**: van Oostrom's labeled confluence criterion

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

-- Decreasing diagrams (van Oostrom 1994)
theorem confluent_of_locallyDecreasing :
    WellFounded lt → LocallyDecreasing r lt → Confluent (LabeledUnion r)
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
- Use `axiom` with clear references for standard but complex proofs

## Axiomatized Lemmas

The following are axiomatized with references (standard results with complex Lean 4 proofs):

### Lambda Calculus (de Bruijn infrastructure)
| Lemma | Location | References |
|-------|----------|------------|
| `shift_shift_comm` | Lambda/Term.lean | Pierce (SF Vol 2), Barendregt |
| `shift_subst_below` | Lambda/Term.lean | Pierce (SF Vol 2), Barendregt |
| `shift_subst` | Lambda/Term.lean | Standard de Bruijn |
| `shift_subst_high` | Lambda/Term.lean | Barendregt |
| `subst_subst` | Lambda/Term.lean | Barendregt, Terese |
| `subst_subst_gen` | Lambda/Term.lean | Standard de Bruijn |

### STLC
| Lemma | Location | References |
|-------|----------|------------|
| `typing_shift_self` | STLC/Typing.lean | Standard de Bruijn typing |
| `reducible_app_lam` | STLC/Normalization.lean | Girard/Lafont/Taylor, Tait |
| `liftSubst_extendSubst_comm` | STLC/Normalization.lean | Standard substitution |

### Generic Framework
| Lemma | Location | References |
|-------|----------|------------|
| `confluent_of_locallyDecreasing` | Rewriting/DecreasingDiagrams.lean | van Oostrom (1994) |

### Combinatory Logic
| Lemma | Location | References |
|-------|----------|------------|
| `parRed_complete` | CL/Confluence.lean | Takahashi (1995), Hindley (1974) |

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
