# Copilot Instructions for Metatheory

## Project Overview

**Metatheory** is a comprehensive **programming language foundations library for Lean 4** covering:

- Generic abstract rewriting systems (confluence, termination)
- Lambda calculus and combinatory logic
- Simply typed lambda calculus with strong normalization
- Multiple proof techniques for the Church-Rosser property

## CRITICAL: No Sorrys Allowed

**`sorry` is NEVER acceptable in this codebase.** Every theorem must be fully proven.

If a proof is difficult:
1. Break it into smaller lemmas
2. Use helper functions or auxiliary definitions
3. Simplify the statement if the current formulation is unprovable

## Non-negotiables

- `sorry` is not acceptable anywhere in `Metatheory/`.
- Prefer small, reviewable changes over large refactors.
- Keep edits consistent with existing Lean style and naming.

## Framework Layers

| Layer | Directory | Description |
|-------|-----------|-------------|
| 0 | `Rewriting/` | Generic abstract rewriting system (ARS) framework |
| 1a | `Lambda/` | Lambda calculus Church-Rosser theorem (via diamond property) |
| 1b | `CL/` | Combinatory Logic Church-Rosser theorem (via diamond property) |
| 2a | `TRS/` | Simple expression rewriting (via Newman's lemma) |
| 2b | `StringRewriting/` | String rewriting (via Newman's lemma) |
| 3 | `STLC/` | Simply typed lambda calculus (subject reduction + strong normalization) |

## Build Commands

```bash
lake build    # Build the project
lake clean    # Clean build artifacts
```

## Workflow

### 1. Orient
- Identify the relevant layer under `Metatheory/`
- Find similar theorems/lemmas nearby and mirror their proof style

### 2. Implement
- Update Lean code with the smallest change that fixes the issue
- If a proof gets stuck, extract helper lemmas

### 3. Validate
Run `lake build` and ensure no `sorry` placeholders remain.

### 4. Report
Summarize what changed and which command(s) you ran.

## Key Theorems

### Generic Framework (Rewriting/)
- `confluent_of_diamond` - Diamond property implies confluence
- `confluent_of_terminating_localConfluent` - Newman's lemma
- `confluent_union` - Hindley-Rosen lemma

### Lambda Calculus (Lambda/)
- `confluence` - Church-Rosser theorem
- `parRed_diamond` - ParRed has diamond property

### STLC (STLC/)
- `subject_reduction` - Type preservation
- `strong_normalization` - Strong normalization via logical relations

## Proof Techniques

### Diamond Property Approach (Lambda, CL)
1. Define parallel reduction
2. Define complete development
3. Prove any parallel reduction reaches complete development
4. Diamond property follows

### Newman's Lemma Approach (TRS, StringRewriting)
1. Prove termination via size/length measure
2. Prove local confluence by critical pair analysis
3. Apply Newman's lemma

### Logical Relations (STLC)
1. Define reducibility predicate
2. Prove fundamental lemma
3. Strong normalization follows

## Code Style

- Prefer `theorem` for Prop-valued results, `def` for data
- Use docstrings (`/-- ... -/`) for public definitions
- Group related definitions with `/-! ## Section Name -/`

## Additional Context

See `CLAUDE.md` for full project documentation including Aristotle integration and references.
