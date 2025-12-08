# Metatheory

A comprehensive **programming language foundations library for Lean 4** covering:

- Generic abstract rewriting systems (confluence, termination)
- Lambda calculus and combinatory logic
- Simply typed lambda calculus with strong normalization
- Multiple proof techniques for the Church-Rosser property

## Key Results

### Generic Rewriting Framework

| Theorem | Description |
|---------|-------------|
| `confluent_of_diamond` | Diamond property implies confluence |
| `confluent_of_terminating_localConfluent` | Newman's lemma |
| `confluent_union` | Hindley-Rosen lemma |
| `confluent_of_locallyDecreasing` | Decreasing diagrams (van Oostrom) |

### Case Studies

| System | Key Theorem | Technique |
|--------|-------------|-----------|
| **Lambda Calculus** | `confluence` (Church-Rosser) | Parallel reduction + Complete development |
| **Combinatory Logic** | `confluent` | Parallel reduction |
| **Simple TRS** | `confluent` | Newman's lemma |
| **String Rewriting** | `confluent` | Newman's lemma + Critical pairs |
| **STLC** | `strong_normalization` | Logical relations (Tait's method) |

## Building

```bash
lake build
```

Requires Lean 4.14.0 or compatible version.

## Project Structure

```
Metatheory/
├── Rewriting/           # Generic ARS framework
│   ├── Basic.lean       # Star, Joinable, Diamond, Confluent, Terminating
│   ├── Diamond.lean     # Diamond → Confluence
│   ├── Newman.lean      # Terminating + LocalConfluent → Confluent
│   ├── HindleyRosen.lean # Union of commuting confluent relations
│   └── DecreasingDiagrams.lean # van Oostrom's technique
├── Lambda/              # Untyped lambda calculus
│   ├── Term.lean        # De Bruijn indexed terms
│   ├── Beta.lean        # β-reduction
│   ├── Parallel.lean    # Parallel reduction
│   ├── Complete.lean    # Complete development
│   └── Confluence.lean  # Church-Rosser theorem
├── CL/                  # Combinatory Logic (S, K)
├── TRS/                 # Simple term rewriting
├── StringRewriting/     # String rewriting
└── STLC/                # Simply typed lambda calculus
    ├── Types.lean       # Simple types
    ├── Typing.lean      # Type system + Subject reduction
    └── Normalization.lean # Strong normalization
```

## References

### Papers
- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
- Newman, "On Theories with a Combinatorial Definition of Equivalence" (1942)
- van Oostrom, "Confluence for Abstract and Higher-Order Rewriting" (1994)
- Tait, "Intensional Interpretations of Functionals" (1967)

### Books
- Barendregt, "The Lambda Calculus: Its Syntax and Semantics"
- Terese, "Term Rewriting Systems" (2003)
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
- Pierce et al., "Software Foundations" (Vol 2: PLF)

## License

MIT
